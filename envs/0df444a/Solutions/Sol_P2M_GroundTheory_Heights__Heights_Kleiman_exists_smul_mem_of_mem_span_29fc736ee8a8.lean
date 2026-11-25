-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_smul_mem_of_mem_span_29fc736ee8a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:19:19.560124+00:00
-- url     : https://prove2.me/submissions/34071056-1376-40d5-a40b-e16dc30e69e7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsGenericRestrLen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFiniteSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGenericRestrLen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {F : Type u} [Field F] [Algebra S F] [IsFractionRing S F]
  {Ω : Type w} [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (P : Submodule S Ω) {z : Ω}
    (hz : z ∈ Submodule.span F (P : Set Ω)) : ∃ t ∈ nonZeroDivisors S, t • z ∈ P := by
  refine Submodule.span_induction (p := fun z _ => ∃ t ∈ nonZeroDivisors S, t • z ∈ P)
    (fun z hz => ⟨1, one_mem _, by rwa [one_smul]⟩)
    ⟨1, one_mem _, by rw [smul_zero]; exact P.zero_mem⟩ ?_ ?_ hz
  · rintro a b _ _ ⟨t, ht, ha⟩ ⟨t', ht', hb⟩
    refine ⟨t * t', mul_mem ht ht', ?_⟩
    rw [smul_add]
    refine P.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact P.smul_mem t' ha
    · rw [mul_smul]; exact P.smul_mem t hb
  · rintro c z _ ⟨t, ht, hz⟩
    obtain ⟨⟨a, s⟩, hc⟩ := IsLocalization.surj (nonZeroDivisors S) c
    refine ⟨s * t, mul_mem s.2 ht, ?_⟩
    have key : ((s : S) * t) • (c • z) = a • (t • z) := by
      simp only [Algebra.smul_def, IsScalarTower.algebraMap_apply S F Ω, map_mul] at hc ⊢
      rw [← hc, map_mul]
      ring
    rw [key]
    exact P.smul_mem a hz
end GroundTheory.Heights₂.Heights.Kleiman
