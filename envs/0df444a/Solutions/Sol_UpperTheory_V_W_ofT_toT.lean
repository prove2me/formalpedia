-- Prove2me | solution 1 for UpperTheory.V.W.ofT_toT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:31:17.47844+00:00
-- url     : https://prove2.me/submissions/76d46723-d56e-4b71-b2a1-b693ebfa737b

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_RepAlg
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnopSMul
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebraHeight_OfDetToDet
import Theorems.Thm_UpperTheory_V_Alg_Lift_map_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] UpperTheory.V.Alg.Lift.map_hom



set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing
open UpperTheory UpperTheory.V UpperTheory.V.W
variable (A G S : Type) [CommRing A] [Group G] [CommRing S] [Algebra A S]
variable {A G S}
namespace UpperTheory.V.W
theorem _root_.solution (x : MonoidAlgebra S G) : ofT A G S (toT A G S x) = x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g s => simp [toT_single, ofT_tmul]
end UpperTheory.V.W
