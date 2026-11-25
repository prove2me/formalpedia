-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_twistSys_one_94b99c7842cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:13:11.278449+00:00
-- url     : https://prove2.me/submissions/7cdddd46-911e-4737-b489-1a46f8ac1404

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_of_le_8fafb6f504f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_secs_twistBundle_one_62fb03cd3d01
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_span_range_eq_twistMod_one_cf9eb67143e0


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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace KThm
theorem _root_.solution : (twistSys S x 1).Generated := by
  refine KThm.generated_of_le _ fun I => ?_
  change twistMod S x 1 I ≤ _
  rw [← span_range_eq_twistMod_one I]
  exact Submodule.span_mono (Set.range_subset_iff.mpr fun j => mem_secs_twistBundle_one j)
end KThm
end GroundTheory.Heights₂.Heights.Kleiman
