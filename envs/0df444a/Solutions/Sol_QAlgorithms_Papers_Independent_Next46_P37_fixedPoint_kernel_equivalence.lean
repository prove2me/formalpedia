-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P37.fixedPoint_kernel_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:40:47.46438+00:00
-- url     : https://prove2.me/submissions/a75779cd-a0b6-4b42-b892-c3db85a83481

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P37
noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)
open QAlgorithms.Papers.Independent.Next46.P37
open Matrix

theorem g62q_comp {n : ℕ} (P L Q : Matrix (Fin n) (Fin n) ℝ) (z : Phase n → ℝ) :
    (freeProjection P L Q - 1) *ᵥ z = Sum.elim
      ((L⁻¹ * Q) *ᵥ (z ∘ Sum.inl) + L⁻¹ *ᵥ (z ∘ Sum.inr) - z ∘ Sum.inl)
      ((P * L⁻¹ * Q - Lᵀ) *ᵥ (z ∘ Sum.inl) + (P * L⁻¹) *ᵥ (z ∘ Sum.inr) - z ∘ Sum.inr) := by
  have hz : z = Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) := by
    funext i; rcases i with i | i <;> rfl
  rw [sub_mulVec, one_mulVec, freeProjection]
  conv_lhs => rw [hz]
  rw [fromBlocks_mulVec]
  funext i; rcases i with i | i <;> simp

theorem g62q_fwd {n : ℕ} (P L Q : Matrix (Fin n) (Fin n) ℝ) (hL : L.det ≠ 0) (z : Phase n → ℝ)
    (hz : (freeProjection P L Q - 1) *ᵥ z = 0) :
    z ∘ Sum.inr = (L - Q) *ᵥ (z ∘ Sum.inl) ∧ diagonalHessian P L Q *ᵥ (z ∘ Sum.inl) = 0 := by
  have hLu : IsUnit L.det := isUnit_iff_ne_zero.2 hL
  rw [g62q_comp] at hz
  set x := z ∘ Sum.inl
  set p := z ∘ Sum.inr
  have h1 : (L⁻¹ * Q) *ᵥ x + L⁻¹ *ᵥ p - x = 0 := by
    funext i; have := congrFun hz (Sum.inl i); simpa using this
  have h2 : (P * L⁻¹ * Q - Lᵀ) *ᵥ x + (P * L⁻¹) *ᵥ p - p = 0 := by
    funext i; have := congrFun hz (Sum.inr i); simpa using this
  have hp : p = (L - Q) *ᵥ x := by
    have := congrArg (fun v => L *ᵥ v) h1
    simp only [mulVec_sub, mulVec_add, mulVec_mulVec, mulVec_zero, ← Matrix.mul_assoc,
      mul_nonsing_inv _ hLu, Matrix.one_mul, one_mulVec] at this
    rw [sub_mulVec]
    rw [sub_eq_zero] at this
    rw [← this]; abel
  refine ⟨hp, ?_⟩
  rw [hp] at h2
  simp only [mulVec_mulVec] at h2
  rw [← add_mulVec, ← sub_mulVec] at h2
  have e : P * L⁻¹ * Q - Lᵀ + P * L⁻¹ * (L - Q) - (L - Q) = diagonalHessian P L Q := by
    rw [Matrix.mul_sub, Matrix.mul_assoc P L⁻¹ L, nonsing_inv_mul _ hLu, Matrix.mul_one,
      diagonalHessian]
    abel
  rw [e] at h2; exact h2

theorem g62q_bwd {n : ℕ} (P L Q : Matrix (Fin n) (Fin n) ℝ) (hL : L.det ≠ 0) (x : Fin n → ℝ)
    (hx : diagonalHessian P L Q *ᵥ x = 0) :
    (freeProjection P L Q - 1) *ᵥ (Sum.elim x ((L - Q) *ᵥ x)) = 0 := by
  have hLu : IsUnit L.det := isUnit_iff_ne_zero.2 hL
  rw [g62q_comp]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  have hx' : (fun i => x i) = x := rfl
  have hv : (fun i => ((L - Q) *ᵥ x) i) = (L - Q) *ᵥ x := rfl
  rw [hx', hv]
  funext i
  rcases i with i | i
  · simp only [Sum.elim_inl, Pi.zero_apply]
    have : (L⁻¹ * Q) *ᵥ x + L⁻¹ *ᵥ ((L - Q) *ᵥ x) - x = 0 := by
      rw [mulVec_mulVec, ← add_mulVec, Matrix.mul_sub, nonsing_inv_mul _ hLu, add_sub_cancel,
        one_mulVec, sub_self]
    exact congrFun this i
  · simp only [Sum.elim_inr, Pi.zero_apply]
    have : (P * L⁻¹ * Q - Lᵀ) *ᵥ x + (P * L⁻¹) *ᵥ ((L - Q) *ᵥ x) - (L - Q) *ᵥ x = 0 := by
      rw [mulVec_mulVec, ← add_mulVec, ← sub_mulVec]
      have e : P * L⁻¹ * Q - Lᵀ + P * L⁻¹ * (L - Q) - (L - Q) = diagonalHessian P L Q := by
        rw [Matrix.mul_sub, Matrix.mul_assoc P L⁻¹ L, nonsing_inv_mul _ hLu, Matrix.mul_one,
          diagonalHessian]
        abel
      rw [e, hx]
    exact congrFun this i

theorem solution (n : ℕ) (hn : 0 < n)
    (P L Q : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.IsSymm) (hQ : Q.IsSymm) (hL : L.det ≠ 0) :
    ∃ e : LinearMap.ker (freeProjection P L Q - 1).mulVecLin ≃ₗ[ℝ]
        LinearMap.ker (diagonalHessian P L Q).mulVecLin,
      (∀ z, (e z).val = fun i => z.val (Sum.inl i)) ∧
      (∀ x, (e.symm x).val = Sum.elim x.val ((L - Q).mulVec x.val)) := by
  let e : LinearMap.ker (freeProjection P L Q - 1).mulVecLin ≃ₗ[ℝ]
      LinearMap.ker (diagonalHessian P L Q).mulVecLin :=
    { toFun := fun z => ⟨fun i => z.val (Sum.inl i), by
        have := (g62q_fwd P L Q hL z.val (by have := LinearMap.mem_ker.1 z.2; rwa [Matrix.mulVecLin_apply] at this)).2
        exact LinearMap.mem_ker.2 (by rw [Matrix.mulVecLin_apply]; simpa [Function.comp_def] using this)⟩
      invFun := fun x => ⟨Sum.elim x.val ((L - Q).mulVec x.val), by
        exact LinearMap.mem_ker.2 (by
          rw [Matrix.mulVecLin_apply]
          exact g62q_bwd P L Q hL x.val (by have := LinearMap.mem_ker.1 x.2; rwa [Matrix.mulVecLin_apply] at this))⟩
      map_add' := fun a b => by ext i; rfl
      map_smul' := fun c a => by ext i; rfl
      left_inv := fun z => by
        apply Subtype.ext
        have h := (g62q_fwd P L Q hL z.val (by have := LinearMap.mem_ker.1 z.2; rwa [Matrix.mulVecLin_apply] at this)).1
        funext i
        rcases i with i | i
        · rfl
        · simp only [Sum.elim_inr]
          have := congrFun h i
          simpa [Function.comp_def] using this.symm
      right_inv := fun x => by ext i; rfl }
  exact ⟨e, fun z => rfl, fun x => rfl⟩
