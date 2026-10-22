-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P17.admissible_form_clifford_embedding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:15:10.133466+00:00
-- url     : https://prove2.me/submissions/f67ed9fb-b7a7-4084-8d08-e64d0fd0f9f8

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17
open QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

section
set_option linter.unusedSectionVars false
variable {K : Type*} [Field K] [CharZero K] {d : ℕ}
variable {g : Matrix (Fin d) (Fin d) K}
variable {S : Type*} [AddCommGroup S] [Module K S]

theorem g74c_sign_sq {t : K} (h : IsSign t) : t * t = 1 := by
  rcases h with rfl | rfl <;> norm_num

theorem g74c_cva (rho : SpinRepresentation g S) (v : Fin d → K) :
    cliffordVectorAction rho v = rho.action (CliffordAlgebra.ι (cliffordQ g) v) := rfl

theorem g74c_even_comm (rho : SpinRepresentation g S) (A : Module.End K S) (τ : K)
    (hτ : IsSign τ) (hA : ∀ v, cliffordVectorAction rho v * A = τ • (A * cliffordVectorAction rho v))
    (a : CliffordAlgebra.even (cliffordQ g)) : rho.action a.val * A = A * rho.action a.val := by
  obtain ⟨x, hx⟩ := a
  change rho.action x * A = A * rho.action x
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commutes r A
  | add x y hx hy ihx ihy => rw [map_add, add_mul, mul_add, ihx, ihy]
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul, ← g74c_cva, ← g74c_cva]
    have h1 : cliffordVectorAction rho m₁ * (cliffordVectorAction rho m₂ * A) =
        A * (cliffordVectorAction rho m₁ * cliffordVectorAction rho m₂) := by
      rw [hA, mul_smul_comm, ← mul_assoc, hA, smul_mul_assoc, smul_smul, g74c_sign_sq hτ,
        one_smul, mul_assoc]
    rw [mul_assoc, mul_assoc, ih, ← mul_assoc (cliffordVectorAction rho m₂),
      ← mul_assoc (cliffordVectorAction rho m₁), h1]
    simp only [mul_assoc]

theorem g74c_form_gen (rho : SpinRepresentation g S) (b : LinearMap.BilinForm K S) (τ σ : K)
    (h : FormSigns rho b τ σ) (u v : Fin d → K) (s t : S) :
    b (spinGenerator rho u v s) t = - b s (spinGenerator rho u v t) := by
  obtain ⟨hτ, -, hc, -⟩ := h
  have key : ∀ x y : Fin d → K, ∀ s t, b ((cliffordVectorAction rho x * cliffordVectorAction rho y) s) t
      = b s ((cliffordVectorAction rho y * cliffordVectorAction rho x) t) := by
    intro x y s t
    simp only [Module.End.mul_apply]
    rw [hc, hc, ← mul_assoc, g74c_sign_sq hτ, one_mul]
  simp only [spinGenerator, LinearMap.smul_apply, LinearMap.sub_apply, map_smul, map_sub,
    LinearMap.smul_apply, LinearMap.sub_apply, key, smul_eq_mul]
  ring

theorem g74c_inv (rho : SpinRepresentation g S) (b : LinearMap.BilinForm K S) (τ σ : K)
    (h : FormSigns rho b τ σ) : b ∈ invariantForms rho := by
  intro u v s t
  rw [g74c_form_gen rho b τ σ h]; ring

theorem g74c_isSign_mul {a b : K} (ha : IsSign a) (hb : IsSign b) : IsSign (a * b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [IsSign]

end
section
set_option linter.unusedSectionVars false
variable {K : Type*} [Field K] [CharZero K] {d : ℕ}
variable {g : Matrix (Fin d) (Fin d) K}
variable {S : Type*} [AddCommGroup S] [Module K S]

theorem g74c_polar (x y : Fin d → K) :
    QuadraticMap.polar (cliffordQ g) x y = -(g.toBilin' x y + g.toBilin' y x) := by
  unfold cliffordQ Matrix.toQuadraticForm'
  rw [LinearMap.BilinMap.polar_toQuadraticMap]
  simp [Matrix.toBilin'_apply', Matrix.toLinearMap₂'_apply', Matrix.neg_mulVec]
  ring

theorem g74c_rel (rho : SpinRepresentation g S) (x y : Fin d → K) :
    cliffordVectorAction rho x * cliffordVectorAction rho y =
      (QuadraticMap.polar (cliffordQ g) x y) • 1 - cliffordVectorAction rho y * cliffordVectorAction rho x := by
  have h := congrArg rho.action (CliffordAlgebra.ι_mul_ι_add_swap (Q := cliffordQ g) x y)
  rw [map_add, map_mul, map_mul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one] at h
  rw [← h, g74c_cva, g74c_cva]; abel

theorem g74c_comm_calc {A : Type*} [Ring A] [Algebra K A] (X Y Z : A) (a b c : K)
    (hXY : Y * X = a • 1 - X * Y) (hYZ : Y * Z = b • 1 - Z * Y) (hXZ : X * Z = c • 1 - Z * X) :
    ((1/4 : K) • (X * Y - Y * X)) * Z - Z * ((1/4 : K) • (X * Y - Y * X)) =
      (-(c/2)) • Y + (b/2) • X := by
  have h3 : X * Y * Z = b • X - c • Y + Z * X * Y := by
    rw [mul_assoc, hYZ, mul_sub, mul_smul_comm, mul_one, ← mul_assoc, hXZ, sub_mul,
      smul_mul_assoc, one_mul, mul_assoc]; abel
  rw [hXY]
  simp only [smul_sub, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h3,
    ← mul_assoc]
  module

end
section
set_option linter.unusedSectionVars false
variable {K : Type*} [Field K] [CharZero K] {d : ℕ}
variable {g : Matrix (Fin d) (Fin d) K}
variable {S : Type*} [AddCommGroup S] [Module K S]

theorem g74c_vec_gen (rho : SpinRepresentation g S) (hg : ∀ x y, g.toBilin' x y = g.toBilin' y x)
    (u v x : Fin d → K) :
    cliffordVectorAction rho (vectorGenerator g u v x) =
      spinGenerator rho u v * cliffordVectorAction rho x -
        cliffordVectorAction rho x * spinGenerator rho u v := by
  unfold spinGenerator
  rw [g74c_comm_calc _ _ _ _ _ _ (g74c_rel rho v u) (g74c_rel rho v x) (g74c_rel rho u x),
    g74c_polar, g74c_polar, hg x u, hg x v]
  simp only [vectorGenerator, map_sub, map_smul]
  module

end

theorem g74c_sig_symm (p q : ℕ) (x y : Fin (p + q) → ℝ) :
    (signatureMatrix p q).toBilin' x y = (signatureMatrix p q).toBilin' y x := by
  simp only [signatureMatrix, Matrix.toBilin'_apply', dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem g74c_sig_single (p q : ℕ) (x : Fin (p + q) → ℝ) (i : Fin (p + q)) :
    (signatureMatrix p q).toBilin' x (Pi.single i 1) = x i * (if i.val < p then 1 else -1) := by
  simp only [signatureMatrix, Matrix.toBilin'_apply', dotProduct, Matrix.mulVec_diagonal]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

/-- Definition 2.1 consequence, PDF p. 18. Printed: every admissible beta gives
an embedding. Changed: injectivity requires beta != 0; all other clauses include
zero. Why: zero is admissible under the printed conditions and gives the zero map
on nonzero V. No other hypothesis or conclusion is changed. -/
theorem solution (p q : ℕ) (hd : 0 < p + q)
    (S : Type*) [AddCommGroup S] [Module ℝ S] [FiniteDimensional ℝ S]
    (rho : SpinRepresentation (signatureMatrix p q) S)
    (splitting : Option (SpinSplitting rho)) (hs : CompleteSplitting rho splitting)
    (b : LinearMap.BilinForm ℝ S) (hb : FormAdmissible rho splitting b)
    (tau sigma : ℝ) (hsgn : FormSigns rho b tau sigma) :
    b ∈ invariantForms rho ∧ cliffordForm rho b ∈ equivariantForms rho ∧
    (b ≠ 0 → Function.Injective (cliffordForm rho b)) ∧
    (∀ v s t, cliffordForm rho b v t s = (tau * sigma) * cliffordForm rho b v s t) ∧
    (∀ h : SpinSplitting rho, splitting = some h →
      ∀ i : ℝ, FormIsotropy h.grading b i →
        ∀ v, FormIsotropy h.grading (cliffordForm rho b v) (-i)) := by
  have hsgn0 := hsgn
  obtain ⟨ht, hsg, hc, hy⟩ := hsgn
  have hsym := g74c_sig_symm p q
  refine ⟨g74c_inv rho b tau sigma hsgn0, ?_, ?_, ?_, ?_⟩
  · intro u v x s t
    show b (cliffordVectorAction rho (vectorGenerator _ u v x) s) t +
      b (cliffordVectorAction rho x (spinGenerator rho u v s)) t +
      b (cliffordVectorAction rho x s) (spinGenerator rho u v t) = 0
    rw [g74c_vec_gen rho hsym]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub]
    rw [g74c_form_gen rho b tau sigma hsgn0 u v (cliffordVectorAction rho x s) t]; ring
  · intro hb0
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hv' : ∀ s t, b (cliffordVectorAction rho v s) t = 0 := fun s t => by
      have := congrArg (fun f : LinearMap.BilinForm ℝ S => f s t) hv
      simpa [cliffordForm, formCompose] using this
    have hstab : SpinStable (Set.range rho.action) (LinearMap.ker b) := by
      rintro _ ⟨a, rfl⟩
      induction a using CliffordAlgebra.induction with
      | algebraMap r =>
        intro x hx
        rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
        simp only [LinearMap.smul_apply, Module.End.one_apply]
        exact (LinearMap.ker b).smul_mem r hx
      | ι w =>
        intro x hx
        rw [LinearMap.mem_ker] at hx ⊢
        ext t
        rw [← g74c_cva, hc]
        simp [hx]
      | mul a1 a2 h1 h2 =>
        intro x hx
        rw [map_mul, Module.End.mul_apply]
        exact h1 _ (h2 x hx)
      | add a1 a2 h1 h2 =>
        intro x hx
        rw [map_add, LinearMap.add_apply]
        exact (LinearMap.ker b).add_mem (h1 x hx) (h2 x hx)
    rcases rho.irreducible.2 _ hstab with h0 | h0
    · have hz : cliffordVectorAction rho v = 0 := by
        ext s
        have : cliffordVectorAction rho v s ∈ LinearMap.ker b := by
          rw [LinearMap.mem_ker]; ext t; simpa using hv' s t
        rw [h0] at this
        simpa using this
      haveI : Nontrivial S := rho.irreducible.1
      funext i
      have hr := g74c_rel rho v (Pi.single i 1)
      rw [hz, zero_mul, mul_zero, sub_zero, eq_comm, smul_eq_zero] at hr
      rcases hr with hr | hr
      · rw [g74c_polar, g74c_sig_single, hsym, g74c_sig_single] at hr
        simp only [Pi.zero_apply]
        split_ifs at hr <;> linarith
      · exact absurd hr one_ne_zero
    · exfalso; apply hb0
      ext s t
      have : s ∈ LinearMap.ker b := by rw [h0]; trivial
      rw [LinearMap.mem_ker] at this
      simp [this]
  · intro v s t
    show b (cliffordVectorAction rho v t) s = tau * sigma * b (cliffordVectorAction rho v s) t
    rw [hy s (cliffordVectorAction rho v t), hc v s t]
    linear_combination (-(sigma * b s (cliffordVectorAction rho v t))) * g74c_sign_sq ht
  · intro h _ i hi v
    obtain ⟨hi1, hi2⟩ := hi
    refine ⟨by rcases hi1 with rfl | rfl <;> simp [IsSign], ?_⟩
    intro s t
    show b (cliffordVectorAction rho v (h.grading s)) t =
      -i * b (cliffordVectorAction rho v s) (h.grading t)
    have ho := congrArg (fun F : Module.End ℝ S => F s) (h.odd v)
    simp only [Module.End.mul_apply, LinearMap.neg_apply] at ho
    have ho' : cliffordVectorAction rho v (h.grading s) = -(h.grading (cliffordVectorAction rho v s)) := by
      rw [ho]; simp
    rw [ho', map_neg, LinearMap.neg_apply, hi2]; ring
