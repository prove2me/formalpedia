-- Prove2me | solution 1 for PolyhedralSOC.LowerBound.covering_claim
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:26:14.972968+00:00
-- url     : https://prove2.me/submissions/8e28b3bc-8e0d-4431-8717-10dda9c99769

import Mathlib
import Definitions.Def_PolyhedralSOC_Shared_LorentzCone
set_option autoImplicit false
open PolyhedralSOC
set_option maxHeartbeats 600000 in
theorem solution {k : ℕ} {ε : ℝ} (hε : 0 < ε) (S : Finset (Fin k → ℝ))
    (hB : {y : Fin k → ℝ | Shared.eucNorm y ≤ 1} ⊆ convexHull ℝ (S : Set (Fin k → ℝ)))
    (hS : ∀ s ∈ S, Shared.eucNorm s ≤ 1 + ε) :
    ∀ y : Fin k → ℝ, Shared.eucNorm y = 1 + ε →
      ∃ s ∈ S, Shared.eucNorm (y - s) ≤ Real.sqrt (2 * ε * (1 + ε)) := by
  intro y hy
  have hR : 0 < 1 + ε := by linarith
  have hy2 : (∑ i, y i ^ 2) = (1 + ε)^2 := by
    rw [← hy]
    exact (Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (y i))).symm
  have hx : Shared.eucNorm ((1+ε)⁻¹ • y) ≤ 1 := by
    unfold Shared.eucNorm
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by norm_num, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    have he : (∑ i, ((1+ε)⁻¹ * y i)^2) = (1+ε)⁻¹^2 * ∑ i, y i^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he, hy2]
    field_simp
    norm_num
  let f : (Fin k → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ i, y i * x i
      map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a x
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring }
  obtain ⟨s, hs, hfs⟩ := (f.convexOn convex_univ).exists_ge_of_mem_convexHull
    (Set.subset_univ _) (hB hx)
  have hf : f ((1+ε)⁻¹ • y) = 1+ε := by
    change (∑ i, y i * ((1+ε)⁻¹ * y i)) = _
    have he : (∑ i, y i * ((1+ε)⁻¹ * y i)) = (1+ε)⁻¹ * ∑ i, y i^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he, hy2]
    field_simp <;> ring
  rw [hf] at hfs
  change 1+ε ≤ ∑ i, y i*s i at hfs
  have hs2 : (∑ i, s i^2) ≤ (1+ε)^2 := by
    have hh := hS s hs
    unfold Shared.eucNorm at hh
    exact (Real.sqrt_le_iff).mp hh |>.2
  refine ⟨s, hs, ?_⟩
  unfold Shared.eucNorm
  apply Real.sqrt_le_sqrt
  have he : (∑ i, (y i-s i)^2) = (∑ i, y i^2) + (∑ i, s i^2) - 2*∑ i, y i*s i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change (∑ i, (y i-s i)^2) ≤ _
  rw [he, hy2]
  nlinarith
