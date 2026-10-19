-- Prove2me | solution 1 for QAlgorithms.Nannicini.oblivious_perp_state
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T00:14:19.309268+00:00
-- url     : https://prove2.me/submissions/402ac2ee-9666-457a-89a0-283c00b28094

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation

open QAlgorithms
open scoped ComplexConjugate

private lemma oa_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) : act (A * B) v = act A (act B v) := by
  simp only [act, Matrix.mulVec_mulVec, WithLp.ofLp_toLp]

private lemma oa_adjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    inner ℂ x (act (star A) y) = inner ℂ (act A x) y := by
  change inner ℂ x (Matrix.toEuclideanLin (star A) y) =
    inner ℂ (Matrix.toEuclideanLin A x) y
  rw [Matrix.star_eq_conjTranspose, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact LinearMap.adjoint_inner_right _ _ _

private lemma oa_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ)
    (x y : EuclideanSpace ℂ ι) : inner ℂ (act A x) (act A y) = inner ℂ x y := by
  rw [← oa_adjoint, ← oa_mul, Unitary.star_mul_self_of_mem hA]
  simp [act]

private lemma oa_flag_inner {ι : Type*} [Fintype ι] (b c : Bool)
    (x y : EuclideanSpace ℂ ι) :
    inner ℂ (tensorVec (ket b) x) (tensorVec (ket c) y) =
      if b = c then inner ℂ x y else 0 := by
  cases b <;> cases c <;>
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, tensorVec, ket,
      Fintype.sum_prod_type, mul_comm]

private lemma oa_flag_ket {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ (Bool × ι)) :
    inner ℂ (tensorVec (ket false) (ket i)) v = v (false, i) := by
  have h : tensorVec (ket false) (ket i) = ket (false, i) := by
    ext ⟨b,j⟩
    cases b <;> simp [tensorVec, ket]
  rw [h]
  simp [ket, EuclideanSpace.inner_single_left]

theorem solution {n : ℕ} (U : Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ)
    (V : Matrix (Qubits n) (Qubits n) ℂ) (θ : ℝ)
    (ϕ : EuclideanSpace ℂ (Qubits n) → EuclideanSpace ℂ (Qubits n))
    (hU : U ∈ Matrix.unitaryGroup (Bool × Qubits n) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Qubits n) ℂ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hact : ∀ ψ : EuclideanSpace ℂ (Qubits n), IsState ψ →
      act U (tensorVec (ket false) ψ) =
        (Real.sin θ : ℂ) • tensorVec (ket false) (act V ψ) +
          (Real.cos θ : ℂ) • tensorVec (ket true) (ϕ ψ))
    (ψ : EuclideanSpace ℂ (Qubits n)) (hψ : IsState ψ) :
    let Ψperp := act (star U) ((Real.cos θ : ℂ) • tensorVec (ket false) (act V ψ) -
      (Real.sin θ : ℂ) • tensorVec (ket true) (ϕ ψ))
    inner ℂ (tensorVec (ket false) ψ) Ψperp = 0 ∧
      act (Matrix.kronecker (Matrix.diagonal fun b : Bool => if b then (0 : ℂ) else 1)
        (1 : Matrix (Qubits n) (Qubits n) ℂ)) Ψperp = 0 := by
  classical
  dsimp only
  let a := (Real.sin θ : ℂ)
  let b := (Real.cos θ : ℂ)
  let F := fun x : EuclideanSpace ℂ (Qubits n) => tensorVec (ket false) x
  let B := fun x : EuclideanSpace ℂ (Qubits n) => tensorVec (ket true) x
  let q := b • F (act V ψ) - a • B (ϕ ψ)
  have hb : b ≠ 0 := by
    dsimp [b]
    exact_mod_cast ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  have trig : a ^ 2 + b ^ 2 = 1 := by
    dsimp [a, b]
    exact_mod_cast Real.sin_sq_add_cos_sq θ
  have coords : ∀ i : Qubits n, act (star U) q (false, i) = 0 := by
    intro i
    have hi : IsState (ket i) := by simp [IsState, ket]
    have hu := oa_inner U hU (F (ket i)) (F ψ)
    dsimp [F] at hu
    rw [hact _ hi, hact _ hψ] at hu
    have hv := oa_inner V hV (ket i) ψ
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, oa_flag_inner, if_true, Bool.false_eq_true,
      Bool.true_eq_false, if_false, mul_zero, add_zero, zero_add] at hu
    rw [hv] at hu
    have hbad : inner ℂ (ϕ (ket i)) (ϕ ψ) = inner ℂ (ket i) ψ := by
      apply (mul_left_cancel₀ (pow_ne_zero 2 hb))
      change a * (a * inner ℂ (ket i) ψ) + b * (b * inner ℂ (ϕ (ket i)) (ϕ ψ)) =
        inner ℂ (ket i) ψ at hu
      linear_combination hu - inner ℂ (ket i) ψ * trig
    rw [← oa_flag_ket, oa_adjoint, hact _ hi]
    change inner ℂ (a • F (act V (ket i)) + b • B (ϕ (ket i))) q = 0
    simp only [q, F, B, inner_sub_right, inner_add_left, inner_smul_left,
      inner_smul_right]
    have ha : starRingEnd ℂ a = a := Complex.conj_ofReal _
    have hc : starRingEnd ℂ b = b := Complex.conj_ofReal _
    simp only [ha, hc, oa_flag_inner, if_true, Bool.false_eq_true,
      Bool.true_eq_false, if_false, mul_zero]
    rw [hv, hbad]
    ring
  constructor
  · change inner ℂ (tensorVec (ket false) ψ) (act (star U) q) = 0
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, tensorVec, ket,
      Fintype.sum_prod_type, coords]
  · have proj : ∀ v : EuclideanSpace ℂ (Bool × Qubits n),
        act (Matrix.kronecker (Matrix.diagonal fun b : Bool => if b then (0 : ℂ) else 1)
          (1 : Matrix (Qubits n) (Qubits n) ℂ)) v =
            WithLp.toLp 2 (fun p => if p.1 then 0 else v p) := by
      intro v
      ext ⟨c,i⟩
      cases c <;>
        simp [act, Matrix.mulVec, dotProduct,
          Matrix.diagonal_apply, Matrix.one_apply, Fintype.sum_prod_type]
    rw [proj]
    ext ⟨c,i⟩
    cases c
    · exact coords i
    · rfl


