-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_mul_mem_secs_beaac2ecfb40
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:32:51.852566+00:00
-- url     : https://prove2.me/submissions/c3a34044-6770-4c4a-bac1-700d76ed001b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulMemSecsTwistIdealSys
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_mul_mem_sub_6a5df893941c

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
theorem _root_.solution {G : SubSystem S x Ω} {z : Ω} (hz : z ∈ (G.baseChange O).secs) :
    ∃ t : S, t ∉ 𝔪 ∧ algebraMap S Ω t * z ∈ G.secs := by
  classical
  simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at hz ⊢
  choose t ht hzt using fun I => exists_mul_mem_sub 𝔪 (hz I)
  refine ⟨∏ I, t I, fun h => ?_, fun I => ?_⟩
  · obtain ⟨I, -, hI⟩ := (Ideal.IsPrime.prod_mem_iff (hp := inferInstance)).mp h
    exact ht I hI
  · rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ I), map_mul, mul_comm (algebraMap S Ω (t I)),
      mul_assoc, ← Algebra.smul_def]
    exact (G.sub I).smul_of_tower_mem _ (hzt I)
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
