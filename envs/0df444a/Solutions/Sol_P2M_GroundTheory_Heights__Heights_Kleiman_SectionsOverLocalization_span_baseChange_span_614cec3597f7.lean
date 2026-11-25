-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_span_baseChange_span_614cec3597f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:48:39.241539+00:00
-- url     : https://prove2.me/submissions/80ed7628-46e5-4fbd-9858-ae3451c731ac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_smul_mem_span_baseChange_1decc818f05e

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
open scoped Pointwise
noncomputable section
variable {S : Type*} [CommRing S] {O : Type*} [CommRing O] [Algebra S O] {Ω : Type*} [Field Ω]
  [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
theorem _root_.solution (I : Chart x) (P : Set Ω) :
    Submodule.span (chartRing O x I) (Submodule.span (chartRing S x I) P : Set Ω) =
      Submodule.span (chartRing O x I) P := by
  apply le_antisymm
  · refine Submodule.span_le.mpr fun y hy => ?_
    refine Submodule.span_induction
      (p := fun y _ => y ∈ Submodule.span (chartRing O x I) P) ?_ ?_ ?_ ?_ hy
    · intro z hz; exact Submodule.subset_span hz
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; exact smul_mem_span_baseChange P a hz
  · exact Submodule.span_mono Submodule.subset_span
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
