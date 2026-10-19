-- Prove2me | solution 1 for QAlgorithms.Nannicini.oblivious_amplitudeAmplification
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T00:22:23.61772+00:00
-- url     : https://prove2.me/submissions/40965d35-7252-455f-a02e-04c4038b51c4

import Theorems.Thm_QAlgorithms_Nannicini_oblivious_perp_state
import Mathlib.Tactic.Module

open QAlgorithms

private lemma amp_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) : act (A * B) v = act A (act B v) := by
  simp only [act, Matrix.mulVec_mulVec, WithLp.ofLp_toLp]

private lemma amp_add {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (v w : EuclideanSpace ℂ ι) : act A (v + w) = act A v + act A w := by
  change (Matrix.toEuclideanLin A) (v + w) = _
  exact map_add _ _ _

private lemma amp_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (z : ℂ) (v : EuclideanSpace ℂ ι) : act A (z • v) = z • act A v := by
  change (Matrix.toEuclideanLin A) (z • v) = _
  exact map_smul _ _ _

private lemma amp_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (v w : EuclideanSpace ℂ ι) : act A (v - w) = act A v - act A w := by
  change (Matrix.toEuclideanLin A) (v - w) = _
  exact map_sub _ _ _

private lemma amp_negmat {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) : act (-A) v = -act A v := by
  simp [act, Matrix.neg_mulVec]

private lemma amp_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ ι) : act (1 : Matrix ι ι ℂ) v = v := by simp [act]

private lemma amp_reflect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ (Bool × ι)) :
    act (Matrix.kronecker (reflAt false) (1 : Matrix ι ι ℂ)) v =
      WithLp.toLp 2 (fun p => if p.1 then -v p else v p) := by
  ext ⟨b,i⟩
  cases b <;> simp [act, reflAt, Matrix.mulVec, dotProduct,
    Matrix.diagonal_apply, Matrix.one_apply, Fintype.sum_prod_type]

private lemma amp_project {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ (Bool × ι)) :
    act (Matrix.kronecker (Matrix.diagonal fun b : Bool => if b then (0 : ℂ) else 1)
      (1 : Matrix ι ι ℂ)) v =
      WithLp.toLp 2 (fun p => if p.1 then 0 else v p) := by
  ext ⟨b,i⟩
  cases b <;> simp [act, Matrix.mulVec, dotProduct,
    Matrix.diagonal_apply, Matrix.one_apply, Fintype.sum_prod_type]

theorem solution {n : ℕ}
    (U : Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ)
    (V : Matrix (Qubits n) (Qubits n) ℂ) (θ : ℝ)
    (ϕ : EuclideanSpace ℂ (Qubits n) → EuclideanSpace ℂ (Qubits n))
    (hU : U ∈ Matrix.unitaryGroup (Bool × Qubits n) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Qubits n) ℂ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hact : ∀ ψ : EuclideanSpace ℂ (Qubits n), IsState ψ →
      act U (tensorVec (ket false) ψ) =
        (Real.sin θ : ℂ) • tensorVec (ket false) (act V ψ) +
          (Real.cos θ : ℂ) • tensorVec (ket true) (ϕ ψ))
    (ψ : EuclideanSpace ℂ (Qubits n)) (hψ : IsState ψ) (k : ℕ) (_hk : 0 < k) :
    let R : Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ :=
      Matrix.kronecker (reflAt false) (1 : Matrix (Qubits n) (Qubits n) ℂ)
    let G := -(U * star R * star U * R)
    act (G ^ k) (act U (tensorVec (ket false) ψ)) =
      (Real.sin ((2 * (k : ℝ) + 1) * θ) : ℂ) • tensorVec (ket false) (act V ψ) +
        (Real.cos ((2 * (k : ℝ) + 1) * θ) : ℂ) • tensorVec (ket true) (ϕ ψ) := by
  classical
  dsimp only
  let R : Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ :=
    Matrix.kronecker (reflAt false) 1
  let G := -(U * star R * star U * R)
  let a := (Real.sin θ : ℂ)
  let b := (Real.cos θ : ℂ)
  let F := tensorVec (ket false) (act V ψ)
  let B := tensorVec (ket true) (ϕ ψ)
  let x := tensorVec (ket false) ψ
  let y := act (star U) (b • F - a • B)
  have trig : a ^ 2 + b ^ 2 = 1 := by
    dsimp [a, b]
    exact_mod_cast Real.sin_sq_add_cos_sq θ
  have hx : act U x = a • F + b • B := hact ψ hψ
  have hy : act U y = b • F - a • B := by
    dsimp [y]
    rw [← amp_mul, Unitary.mul_star_self_of_mem hU, amp_one]
  have hstar : star R = R := by
    ext ⟨c,i⟩ ⟨d,j⟩
    cases c <;> cases d <;>
      simp [R, reflAt, Matrix.star_apply, Matrix.one_apply, eq_comm]
    split_ifs <;> simp_all
  have rx : act R x = x := by
    rw [amp_reflect]
    ext ⟨c,i⟩
    cases c <;> simp [x, tensorVec, ket]
  have rf : act R F = F := by
    rw [amp_reflect]
    ext ⟨c,i⟩
    cases c <;> simp [F, tensorVec, ket]
  have rb : act R B = -B := by
    rw [amp_reflect]
    ext ⟨c,i⟩
    cases c <;> simp [B, tensorVec, ket]
  have ry : act R y = -y := by
    have hp := (QAlgorithms.Nannicini.oblivious_perp_state
      U V θ ϕ hU hV hθ0 hθ1 hact ψ hψ).2
    change act (Matrix.kronecker (Matrix.diagonal fun c : Bool => if c then (0 : ℂ) else 1)
      (1 : Matrix (Qubits n) (Qubits n) ℂ)) y = 0 at hp
    rw [amp_project] at hp
    rw [amp_reflect]
    ext ⟨c,i⟩
    cases c
    · have hz := congrArg (fun v : EuclideanSpace ℂ (Bool × Qubits n) => v (false,i)) hp
      change y (false,i) = 0 at hz
      change y (false,i) = -y (false,i)
      rw [hz, neg_zero]
    · rfl
  have ux : act (star U) (act U x) = x := by
    rw [← amp_mul, Unitary.star_mul_self_of_mem hU, amp_one]
  have uf : act (star U) F = a • x + b • y := by
    have hs : a • act U x + b • act U y = F := by
      rw [hx, hy]
      match_scalars <;> first | ring1 | linear_combination trig
    have uy : act (star U) (act U y) = y := by
      rw [← amp_mul, Unitary.star_mul_self_of_mem hU, amp_one]
    rw [← hs, amp_add, amp_smul, amp_smul, ux, uy]
  have ub : act (star U) B = b • x - a • y := by
    have hs : b • act U x - a • act U y = B := by
      rw [hx, hy]
      match_scalars <;> first | ring1 | linear_combination trig
    have uy : act (star U) (act U y) = y := by
      rw [← amp_mul, Unitary.star_mul_self_of_mem hU, amp_one]
    rw [← hs, amp_sub, amp_smul, amp_smul, ux, uy]
  have gf : act G F = (b^2-a^2) • F - (2*a*b) • B := by
    dsimp only [G]
    rw [amp_negmat, amp_mul, amp_mul, amp_mul, rf, uf, hstar,
      amp_add, amp_smul, amp_smul, rx, ry]
    simp only [smul_neg, ← sub_eq_add_neg, amp_sub, amp_smul, hx, hy]
    module
  have gb : act G B = (2*a*b) • F + (b^2-a^2) • B := by
    dsimp only [G]
    rw [amp_negmat, amp_mul, amp_mul, amp_mul, rb]
    rw [show -B = (-1 : ℂ) • B by simp, amp_smul, ub, hstar,
      amp_smul, amp_sub, amp_smul, amp_smul, rx, amp_smul, ry]
    simp only [smul_neg, sub_neg_eq_add, amp_smul, amp_add, hx, hy]
    module
  have allk : ∀ j : ℕ, act (G ^ j) (act U x) =
      (Real.sin ((2 * (j : ℝ) + 1) * θ) : ℂ) • F +
      (Real.cos ((2 * (j : ℝ) + 1) * θ) : ℂ) • B := by
    intro j
    induction j with
    | zero => simpa [amp_one, a, b] using hx
    | succ j ih =>
      rw [pow_succ', amp_mul, ih, amp_add, amp_smul, amp_smul, gf, gb]
      have angle : (2 * ((j+1 : ℕ) : ℝ) + 1) * θ =
          (2 * (j : ℝ) + 1) * θ + 2 * θ := by push_cast; ring
      rw [angle, Real.sin_add, Real.cos_add, Real.sin_two_mul, Real.cos_two_mul]
      ext i
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
        Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_one]
      dsimp [a, b] at trig ⊢
      linear_combination -((Real.sin ((2 * (j : ℝ) + 1) * θ) : ℂ) * F i +
        (Real.cos ((2 * (j : ℝ) + 1) * θ) : ℂ) * B i) * trig
  exact allk k
