-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P04.bilinear_density
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T03:50:03.029996+00:00
-- url     : https://prove2.me/submissions/bf818680-7e02-4eb7-b324-14111bfa8be4

import Theorems.Thm_Plasticity_Ext_BishopPhelps
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_bilinear_extension
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_bilinear_attainment
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RCLike.Real

noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

namespace X9

theorem bishopPhelpsBall {K E : Type*} [RCLike K] [NormedAddCommGroup E]
    [NormedSpace K E] [CompleteSpace E] (f : E →L[K] K) (eps : ℝ) (heps : 0 < eps) :
    ∃ g : E →L[K] K, ‖g - f‖ < eps ∧ ∃ y : E, ‖y‖ ≤ 1 ∧ ‖g y‖ = ‖g‖ := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ K E
  letI : IsScalarTower ℝ K E := ⟨fun r k x => by
    change (r • k) • x = (algebraMap ℝ K r) • (k • x)
    simp only [Algebra.smul_def, mul_smul]⟩
  let I := StrongDual.extendRCLikeₗᵢ (𝕜 := K) (F := E)
  obtain ⟨g, hg, y, hy, hgy⟩ := Plasticity.Ext.BishopPhelps (I.symm f) eps heps
  refine ⟨I g, ?_, y, hy, ?_⟩
  · calc
      ‖I g - f‖ = ‖I g - I (I.symm f)‖ := by rw [I.apply_symm_apply]
      _ = ‖I (g - I.symm f)‖ := by rw [map_sub]
      _ = ‖g - I.symm f‖ := I.norm_map _
      _ < eps := hg
  · apply le_antisymm
    · exact ((I g).le_opNorm y).trans (mul_le_of_le_one_right (norm_nonneg _) hy)
    · calc
        ‖I g‖ = ‖g‖ := I.norm_map _
        _ = |g y| := by rw [hgy, abs_of_nonneg (norm_nonneg _)]
        _ = |RCLike.re ((I g) y)| := by
          change |g y| = |RCLike.re (g.extendRCLike y : K)|
          rw [StrongDual.re_extendRCLike_apply]
        _ ≤ ‖(I g) y‖ := RCLike.abs_re_le_norm _

end X9

open QAlgorithms.Papers.Independent.Renew46.P04

universe u v

variable {K : Type*} [RCLike K]

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

section Banach

variable {X Y Z : Type*}

variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]

variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

variable [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]

theorem solution [CompleteSpace X] [CompleteSpace Y] [Nontrivial X] [Nontrivial Y]
    (h : ∀ z : Projective K X Y, TensorAttains z) :
    Dense {B : Bilinear K X Y K | BilinearAttains B} := by
  classical
  obtain ⟨I, hI, _⟩ := (bilinear_extension (K := K) (X := X) (Y := Y) (Z := K)).1
  apply Metric.dense_iff.2
  intro B eps heps
  obtain ⟨g, hg, z, hz, hgz⟩ := X9.bishopPhelpsBall (I B) eps heps
  let B' := I.symm g
  refine ⟨B', ?_, ?_⟩
  · change dist B' B < eps
    have hd : dist B' B = dist g (I B) := by
      dsimp [B']
      simpa using I.symm.isometry.dist_eq g (I B)
    rw [hd, dist_eq_norm]
    exact hg
  · change BilinearAttains B'
    by_cases hg0 : g = 0
    · have hB0 : B' = 0 := by simp [B', hg0]
      rw [hB0]
      obtain ⟨x, hx⟩ := exists_ne (0 : X)
      obtain ⟨y, hy⟩ := exists_ne (0 : Y)
      refine ⟨(‖x‖⁻¹ : K) • x, (‖y‖⁻¹ : K) • y,
        norm_smul_inv_norm hx, norm_smul_inv_norm hy, ?_⟩
      simp
    · have hz1 : ‖z‖ = 1 := by
        apply le_antisymm hz
        have hle := g.le_opNorm z
        rw [hgz] at hle
        nlinarith [norm_pos_iff.mpr hg0]
      apply bilinear_attainment B' z hz1 (h z)
      have hmap : extendBilinear B' = g := by
        rw [← hI B']
        exact I.apply_symm_apply g
      rw [hmap, hgz]
      exact (I.symm.norm_map g).symm

end Banach
end
