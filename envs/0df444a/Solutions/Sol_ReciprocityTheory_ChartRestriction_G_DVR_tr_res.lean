-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.tr_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:33.637381+00:00
-- url     : https://prove2.me/submissions/250e3021-2317-428d-9975-dd1956ba6720

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_def
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped Classical
variable {X Y : Scheme.{0}} (L : LB X)
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {V V' : Y.Opens} (hV : V' ≤ V) {ψ : Y ⟶ X} {a b : L.ι} (h : V ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U b)) :
    res hV (tr L V ψ a b) = tr L V' ψ a b := by
  rw [tr_def L h, tr_def L (hV.trans h), res_res']
end ReciprocityTheory.ChartRestriction.G.DVR
