-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.spectral_adjoint_det_trace_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T00:58:46.21507+00:00
-- url     : https://prove2.me/submissions/5bffc60e-7422-4f8f-9338-047135482841

import Mathlib

set_option autoImplicit false

open scoped InnerProductSpace

namespace P3f47664f

lemma prod_le_mul_sum_pow {n : ℕ} (l : Fin n → ℝ) (hl : ∀ i, 0 ≤ l i) (i : Fin n) :
    ∏ j, l j ≤ l i * (∑ j, l j) ^ (n - 1) := by
  rw [← Finset.mul_prod_erase Finset.univ l (Finset.mem_univ i)]
  apply mul_le_mul_of_nonneg_left _ (hl i)
  calc ∏ j ∈ Finset.univ.erase i, l j ≤ ∏ _j ∈ Finset.univ.erase i, (∑ k, l k) := by
        apply Finset.prod_le_prod
        · intro j _; exact hl j
        · intro j _
          exact Finset.single_le_sum (fun k _ => hl k) (Finset.mem_univ j)
    _ = (∑ j, l j) ^ (n - 1) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
          Fintype.card_fin]

end P3f47664f

theorem solution {n : ℕ} (hn : 0 < n)
    (A B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hBA : B.comp A = LinearMap.id)
    (g : EuclideanSpace ℝ (Fin n)) :
    ‖(LinearMap.adjoint B) g‖ ^ 2 *
        LinearMap.det (LinearMap.adjoint A |>.comp A) ≤
      ‖g‖ ^ 2 *
        (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (LinearMap.adjoint A |>.comp A)) ^ (n - 1) := by
  set w := LinearMap.adjoint B g with hw
  have hg : LinearMap.adjoint A w = g := by
    have h1 := congrArg LinearMap.adjoint hBA
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_id] at h1
    have := LinearMap.congr_fun h1 g
    simpa [hw] using this
  set T := A.comp (LinearMap.adjoint A) with hTdef
  have hT : T.IsSymmetric := by
    intro x y
    simp only [hTdef, LinearMap.comp_apply]
    rw [← LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_left]
  have hdet : LinearMap.det (LinearMap.adjoint A |>.comp A) = LinearMap.det T := by
    rw [hTdef, LinearMap.det_comp, LinearMap.det_comp, mul_comm]
  have htr : LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (LinearMap.adjoint A |>.comp A)
      = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) T := by
    rw [hTdef, LinearMap.trace_comp_comm']
  have hgn : ‖g‖ ^ 2 = ⟪w, T w⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq, ← hg, hTdef, LinearMap.comp_apply,
      LinearMap.adjoint_inner_right, real_inner_comm]
  have hn' : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  set e := hT.eigenvectorBasis hn' with he
  set l := hT.eigenvalues hn' with hl
  have hlnn : ∀ i, 0 ≤ l i := by
    intro i
    apply eigenvalue_nonneg_of_nonneg (hT.hasEigenvalue_eigenvalues hn' i)
    intro x
    simp only [hTdef, LinearMap.comp_apply, RCLike.re_to_real]
    rw [← LinearMap.adjoint_inner_left]
    exact real_inner_self_nonneg
  have hdetT : LinearMap.det T = ∏ i, l i := by
    rw [hT.det_eq_prod_eigenvalues hn']; simp [hl]
  have htrT : LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) T = ∑ i, l i := by
    rw [hT.trace_eq_sum_eigenvalues hn']; simp [hl]
  have hw2 : ‖w‖ ^ 2 = ∑ i, ⟪e i, w⟫_ℝ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← e.sum_inner_mul_inner w w]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [real_inner_comm w (e i), sq]
  have hTw : ⟪w, T w⟫_ℝ = ∑ i, l i * ⟪e i, w⟫_ℝ ^ 2 := by
    rw [← e.sum_inner_mul_inner w (T w)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hT (e i) w, he, hT.apply_eigenvectorBasis hn' i, real_inner_smul_left,
      real_inner_comm w]
    simp [hl]; ring
  rw [hdet, htr, hgn, hdetT, htrT, hw2, hTw, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have := P3f47664f.prod_le_mul_sum_pow l hlnn i
  have hc : 0 ≤ ⟪e i, w⟫_ℝ ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left this hc]
