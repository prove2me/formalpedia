-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.tr_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:25:46.615652+00:00
-- url     : https://prove2.me/submissions/55271ceb-c9de-498f-b5a4-8e4304b6bbf6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_def
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_res_pullU_eq


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
theorem _root_.solution (hL : L.IsLB) {V : Y.Opens} {ψ : Y ⟶ X} {a : L.ι} (h : V ≤ ψ ⁻¹ᵁ L.U a) :
    tr L V ψ a a = 1 := by
  have h' : V ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U a) := fun y hy => ⟨h hy, h hy⟩
  rw [tr_def L h']
  have e := res_pullU_eq ψ (le_inf le_rfl le_rfl : L.U a ≤ L.U a ⊓ L.U a) h' h (L.g a a)
  rw [e, hL.g_self, map_one, map_one]
end ReciprocityTheory.ChartRestriction.G.DVR
