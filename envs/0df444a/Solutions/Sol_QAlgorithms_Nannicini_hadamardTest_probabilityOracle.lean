-- Prove2me | solution 1 for QAlgorithms.Nannicini.hadamardTest_probabilityOracle
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T03:34:45.142557+00:00
-- url     : https://prove2.me/submissions/6d13800d-0db6-44b8-852c-8467d652fef2

import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Nannicini_Ch05a_Model

set_option autoImplicit false
open QAlgorithms
open scoped ComplexConjugate

private lemma act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) : act (A * B) v = act A (act B v) := by
  exact congrArg (WithLp.toLp 2) (Matrix.mulVec_mulVec _ _ _).symm

private noncomputable def blocks {ι : Type*}
    (v w : EuclideanSpace ℂ ι) : EuclideanSpace ℂ (Bool × ι) :=
  WithLp.toLp 2 (fun p => if p.1 then w p.2 else v p.2)

private lemma act_controlled {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (v w : EuclideanSpace ℂ ι) :
    act (controlled U) (blocks v w) = blocks v (act U w) := by
  ext ⟨b,i⟩
  cases b <;> simp [act, controlled, blocks, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Fintype.sum_bool, Matrix.one_apply]

private lemma act_flag {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix Bool Bool ℂ) (v w : EuclideanSpace ℂ ι) :
    act (Matrix.kronecker M (1 : Matrix ι ι ℂ)) (blocks v w) =
      blocks (M false false • v + M false true • w)
        (M true false • v + M true true • w) := by
  ext ⟨b,i⟩
  cases b <;> simp [act, blocks, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Fintype.sum_bool, Matrix.kronecker_apply, Matrix.one_apply, add_comm]

private lemma act_X {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v w : EuclideanSpace ℂ ι) :
    act (Matrix.kronecker pauliX (1 : Matrix ι ι ℂ)) (blocks v w) = blocks w v := by
  rw [act_flag]; simp [pauliX]

private lemma act_H {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v w : EuclideanSpace ℂ ι) :
    act (Matrix.kronecker hadamard (1 : Matrix ι ι ℂ)) (blocks v w) =
      blocks ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (v + w))
        ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (v - w)) := by
  rw [act_flag]; simp [hadamard, smul_add, smul_sub, sub_eq_add_neg]

private lemma controlled_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    controlled U ∈ Matrix.unitaryGroup (Bool × ι) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext ⟨a,i⟩ ⟨b,j⟩
  have h := congrArg (fun M : Matrix ι ι ℂ => M i j) hU.2
  cases a <;> cases b <;>
    simp_all [controlled, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fintype.sum_bool, Matrix.one_apply]

private lemma hadamard_unitary : hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  have hs : hadamard.conjTranspose = hadamard := by
    ext a b; cases a <;> cases b <;> simp [hadamard, Matrix.conjTranspose_apply]
  change hadamard * hadamard.conjTranspose = 1
  rw [hs, hadamard_mul_self]

private lemma X_unitary : pauliX ∈ Matrix.unitaryGroup Bool ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext a b; cases a <;> cases b <;>
    simp [pauliX, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_bool]

private lemma circuit_unitary {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Qubits n) (Qubits n) ℂ) (V : Matrix (Qubits n × X) (Qubits n × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Qubits n × X) ℂ) :
    hadamardTestCircuit U V ∈ Matrix.unitaryGroup (Bool × (Qubits n × X)) ℂ := by
  have hH := Matrix.kronecker_mem_unitary hadamard_unitary
    (one_mem (Matrix.unitaryGroup (Qubits n × X) ℂ))
  have hX := Matrix.kronecker_mem_unitary X_unitary
    (one_mem (Matrix.unitaryGroup (Qubits n × X) ℂ))
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hX hH)
    (controlled_unitary V hV)) hX)
    (controlled_unitary _ (Matrix.kronecker_mem_unitary hU (one_mem _)))) hX) hH

private lemma tensor_ket_inner {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (v w : EuclideanSpace ℂ ι) (x : κ) :
    inner ℂ (tensorVec v (ket x)) (tensorVec w (ket x)) = inner ℂ v w := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, tensorVec, ket, dotProduct,
    Fintype.sum_prod_type, EuclideanSpace.single_apply, Pi.single_apply]

private lemma tensor_ket_norm {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (v : EuclideanSpace ℂ ι) (x : κ) : ‖tensorVec v (ket x)‖ = ‖v‖ := by
  have h := congrArg Complex.re (tensor_ket_inner v v x)
  simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re] at h
  nlinarith [norm_nonneg (tensorVec v (ket x)), norm_nonneg v]

private lemma act_tensor_ket {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (U : Matrix ι ι ℂ) (z : ι) (x : κ) :
    act (Matrix.kronecker U (1 : Matrix κ κ ℂ)) (ket (z,x)) =
      tensorVec (act U (ket z)) (ket x) := by
  ext ⟨i,j⟩
  simp [act, ket, tensorVec, Matrix.kronecker_apply, Matrix.one_apply,
    EuclideanSpace.single_apply, Pi.single_apply, eq_comm]

private lemma act_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (c : ℂ) (v : EuclideanSpace ℂ ι) :
    act U (c • v) = c • act U v :=
  (Matrix.toEuclideanLin U).map_smul c v

private lemma circuit_output {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Qubits n) (Qubits n) ℂ) (V : Matrix (Qubits n × X) (Qubits n × X) ℂ)
    (x : X) :
    act (hadamardTestCircuit U V) (ket (false, ((0 : Qubits n),x))) =
      blocks ((1 / 2 : ℂ) •
        (tensorVec (act U (zeroKet n)) (ket x) - act V (ket ((0 : Qubits n),x))))
        ((1 / 2 : ℂ) •
        (tensorVec (act U (zeroKet n)) (ket x) + act V (ket ((0 : Qubits n),x)))) := by
  have hinit : ket (false, ((0 : Qubits n),x)) =
      blocks (ket ((0 : Qubits n),x)) 0 := by
    ext ⟨b,i⟩; cases b <;> simp [ket, blocks, EuclideanSpace.single_apply, Pi.single_apply]
  have hc : ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) = 1 / 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hn := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    have h : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
      field_simp; nlinarith
    rw [← Complex.ofReal_mul, h]
    norm_num
  simp only [hadamardTestCircuit, act_mul]
  rw [hinit, act_H]
  simp only [add_zero, sub_zero]
  rw [act_X, act_controlled, act_X, act_controlled, act_H, act_X]
  simp only [act_smul, act_tensor_ket, smul_add, smul_sub, smul_smul, hc]
  rfl

private lemma normalized_branch {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι) (p : ℝ) (hp : ‖v‖ ^ 2 = p) :
    ∃ ψ : EuclideanSpace ℂ ι, IsState ψ ∧ (Real.sqrt p : ℂ) • ψ = v := by
  have hs : Real.sqrt p = ‖v‖ := by rw [← hp, Real.sqrt_sq (norm_nonneg _)]
  by_cases hv : v = 0
  · refine ⟨ket i, by simp [IsState, ket], ?_⟩
    simp [hs, hv]
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, ?_, ?_⟩
    · simp [IsState, norm_smul, Complex.norm_real, abs_of_nonneg (norm_nonneg v), hn]
    · rw [hs, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn, Complex.ofReal_one,
        one_smul]

private lemma branch_norms {ι : Type*} [Fintype ι]
    (u v : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖(1 / 2 : ℂ) • (u - v)‖ ^ 2 = 1 - (1 + (inner ℂ u v).re) / 2 ∧
    ‖(1 / 2 : ℂ) • (u + v)‖ ^ 2 = (1 + (inner ℂ u v).re) / 2 := by
  have ha := @norm_add_sq ℂ _ _ _ _ u v
  have hs := @norm_sub_sq ℂ _ _ _ _ u v
  simp only [hu, hv, RCLike.re_to_complex] at ha hs
  have hc : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  simp only [norm_smul, hc, mul_pow]
  constructor <;> nlinarith

theorem solution {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Qubits n) (Qubits n) ℂ) (V : Matrix (Qubits n × X) (Qubits n × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (hV : V ∈ Matrix.unitaryGroup (Qubits n × X) ℂ)
    (ϕ : X → EuclideanSpace ℂ (Qubits n))
    (hϕ : ∀ x, act V (ket ((0 : Qubits n), x)) = tensorVec (ϕ x) (ket x)) :
    IsProbabilityOracle (0 : Qubits n) (hadamardTestCircuit U V)
      (fun x => (1 + (inner ℂ (act U (zeroKet n)) (ϕ x)).re) / 2) := by
  classical
  have hn (x : X) :
      ‖(1 / 2 : ℂ) • (tensorVec (act U (zeroKet n)) (ket x) - act V (ket ((0 : Qubits n),x)))‖ ^ 2 =
        1 - (1 + (inner ℂ (act U (zeroKet n)) (ϕ x)).re) / 2 ∧
      ‖(1 / 2 : ℂ) • (tensorVec (act U (zeroKet n)) (ket x) + act V (ket ((0 : Qubits n),x)))‖ ^ 2 =
        (1 + (inner ℂ (act U (zeroKet n)) (ϕ x)).re) / 2 := by
    have hu : ‖tensorVec (act U (zeroKet n)) (ket x)‖ = 1 := by
      rw [tensor_ket_norm, act_norm_of_mem_unitaryGroup hU]
      simp [zeroKet, ket]
    have hv : ‖act V (ket ((0 : Qubits n),x))‖ = 1 := by
      rw [act_norm_of_mem_unitaryGroup hV]; simp [ket]
    simpa only [hϕ x, tensor_ket_inner] using branch_norms _ _ hu hv
  refine ⟨circuit_unitary U V hU hV, ?_, ?_⟩
  · intro x
    have h0 := (hn x).1
    have h1 := (hn x).2
    constructor <;> nlinarith [sq_nonneg ‖(1 / 2 : ℂ) •
      (tensorVec (act U (zeroKet n)) (ket x) - act V (ket ((0 : Qubits n),x)))‖,
      sq_nonneg ‖(1 / 2 : ℂ) •
      (tensorVec (act U (zeroKet n)) (ket x) + act V (ket ((0 : Qubits n),x)))‖]
  · intro x
    obtain ⟨ψ0, hψ0, he0⟩ := normalized_branch ((0 : Qubits n),x) _ _ (hn x).1
    obtain ⟨ψ1, hψ1, he1⟩ := normalized_branch ((0 : Qubits n),x) _ _ (hn x).2
    refine ⟨ψ0, ψ1, hψ0, hψ1, ?_⟩
    rw [circuit_output]
    have he : blocks
        ((1 / 2 : ℂ) • (tensorVec (act U (zeroKet n)) (ket x) - act V (ket ((0 : Qubits n),x))))
        ((1 / 2 : ℂ) • (tensorVec (act U (zeroKet n)) (ket x) + act V (ket ((0 : Qubits n),x)))) =
        blocks ((Real.sqrt (1 - (1 + (inner ℂ (act U (zeroKet n)) (ϕ x)).re) / 2) : ℂ) • ψ0)
          ((Real.sqrt ((1 + (inner ℂ (act U (zeroKet n)) (ϕ x)).re) / 2) : ℂ) • ψ1) := by
      rw [he0, he1]
    rw [he]
    ext ⟨b,i⟩; cases b <;> simp [blocks, tensorVec, ket, EuclideanSpace.single_apply,
      Pi.single_apply]
