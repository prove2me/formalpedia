-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_mul_mem_sub_6a5df893941c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:51.118371+00:00
-- url     : https://prove2.me/submissions/d12c7c7d-099c-46d6-ad02-06b88fdec90e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulMemSecsTwistIdealSys
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_mul_mem_chartRing_54282771e4c4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_mul_not_mem_1b7cbf7fb574

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial Kleiman
noncomputable section
variable {S : Type*} [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal] {O : Type*} [CommRing O] [Algebra S O]
  [IsLocalization.AtPrime O 𝔪] {Ω : Type*} [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω]
  {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
theorem _root_.solution {G : SubSystem S x Ω} {I : Chart x} {z : Ω} (hz : z ∈ (G.baseChange O).sub I) :
    ∃ t : S, t ∉ 𝔪 ∧ algebraMap S Ω t * z ∈ G.sub I := by
  change z ∈ Submodule.span (chartRing O x I) (G.sub I : Set Ω) at hz
  induction hz using Submodule.span_induction with
  | mem y hy => exact ⟨1, fun h => (Ideal.IsMaximal.ne_top inferInstance) ((Ideal.eq_top_iff_one _).mpr h),
      by rw [map_one, one_mul]; exact hy⟩
  | zero => exact ⟨1, fun h => (Ideal.IsMaximal.ne_top inferInstance) ((Ideal.eq_top_iff_one _).mpr h),
      by rw [mul_zero]; exact zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨t₁, ht₁, h₁⟩ := ha
    obtain ⟨t₂, ht₂, h₂⟩ := hb
    refine ⟨t₁ * t₂, mul_not_mem 𝔪 ht₁ ht₂, ?_⟩
    have e : algebraMap S Ω (t₁ * t₂) * (a + b) =
        t₂ • (algebraMap S Ω t₁ * a) + t₁ • (algebraMap S Ω t₂ * b) := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]; ring
    rw [e]
    exact add_mem ((G.sub I).smul_of_tower_mem t₂ h₁) ((G.sub I).smul_of_tower_mem t₁ h₂)
  | smul a z _ hz =>
    obtain ⟨t, ht, hzt⟩ := hz
    obtain ⟨t', ht', hb⟩ := exists_mul_mem_chartRing 𝔪 a.2
    refine ⟨t' * t, mul_not_mem 𝔪 ht' ht, ?_⟩
    have e : algebraMap S Ω (t' * t) * (a • z) =
        (⟨_, hb⟩ : chartRing S x I) • (algebraMap S Ω t * z) := by
      rw [chartRing_smul_def, chartRing_smul_def, map_mul]; ring
    rw [e]
    exact (G.sub I).smul_mem _ hzt
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
