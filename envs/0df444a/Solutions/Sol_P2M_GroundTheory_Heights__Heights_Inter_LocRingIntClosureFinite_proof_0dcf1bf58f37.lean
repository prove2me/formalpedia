-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_LocRingIntClosureFinite_proof_0dcf1bf58f37
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:01:29.989107+00:00
-- url     : https://prove2.me/submissions/0b314f0c-d568-4ab6-89ba-98efa48a3c4d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingIntClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingChartLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StIntClosureLocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingIntClosure
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_subfield_closure_coords_eq_top_76055511fe92

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
namespace GroundTheory.Heights₂.Heights.Inter
namespace LocRingIntClosureFinite
theorem _root_.solution (h₁ : LocRingChartLoc.Statement) (h₂ : IntClosureLocFinite.Statement) :
    LocRingIntClosureFinite.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W _hv hP' _hQ _hs _hsQ hW
  have := hP'.2.1.1
  have := imageZ_isPrime_of_prime v P'
  obtain ⟨T, hTA, hloc⟩ := h₁ K ι (imageZ v P') W hW.1.1.1 (le_sup_left.trans hW.1.1.2) hW.2
  obtain ⟨t, ht⟩ := h₂ _ _ (fracMapZ v P') _ (subfield_closure_coords_eq_top P') _ T hTA hloc
  exact ⟨t, fun x _ hx => ht x hx⟩
end LocRingIntClosureFinite
end GroundTheory.Heights₂.Heights.Inter
