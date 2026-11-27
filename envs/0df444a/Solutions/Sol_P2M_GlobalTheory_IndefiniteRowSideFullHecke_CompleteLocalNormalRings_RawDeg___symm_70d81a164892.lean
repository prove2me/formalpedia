-- Prove2me | solution 1 for P2M_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg___symm_70d81a164892
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:51:42.449414+00:00
-- url     : https://prove2.me/submissions/fb2ba5ce-ec39-43d7-bb16-853d97ed2fe5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_RawDegreeForms
import Theorems.Thm_P2M_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg_res__At_40b5cb8bfec4
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg_res_rigAt
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg_quot_congr

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings
variable (R : Type) [CommRing R] [IsDomain R]
attribute [instance] RawDeg.addCommGroup RawDeg.free RawDeg.finite
open GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
variable {R} (D : RawDeg R)
namespace GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
theorem _root_.solution (χ χ' : D.X) : LB.Gen.Corr D.P.L _ _ _ _ (D.τ χ χ') (D.τ χ' χ) := by
  intro j j' _ _ h
  have h0 : j 0 = j' 0 := h 0 0 (by
    change (padd D.P.A (D.cK χ) (D.cK χ')).left = (padd D.P.A (D.cK χ') (D.cK χ)).left
    rw [← cT_add, ← cT_add, add_comm])
  have h1 : j 1 = j' 2 := h 1 2 rfl
  have h2 : j 2 = j' 1 := h 2 1 rfl
  have h3 : j 3 = j' 3 := h 3 3 rfl
  simp only [τ, map_mul, map_inv]
  exact quot_congr (D.res_ψAt (add_comm χ χ') h0 _ _ _ _) (D.res_ψAt rfl h1 _ _ _ _)
    (D.res_ψAt rfl h2 _ _ _ _) (D.res_rigAt h3 _ _ _ _)
end GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
