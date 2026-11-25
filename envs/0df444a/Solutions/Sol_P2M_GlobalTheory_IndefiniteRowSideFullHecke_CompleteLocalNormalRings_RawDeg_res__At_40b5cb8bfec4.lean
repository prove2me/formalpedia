-- Prove2me | solution 1 for P2M_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg_res__At_40b5cb8bfec4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:30:50.414154+00:00
-- url     : https://prove2.me/submissions/ed1f88c3-23c0-4206-8d3c-4f8b84b7b5cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_RawDegreeForms
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg_res_res

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
theorem _root_.solution {χ χ' : D.X} {i i' : D.P.L.ι} (e : χ = χ') (e' : i = i') {V V' W} (h h')
    (k : W ≤ V) (k' : W ≤ V') :
    res k (D.ψAt χ i V h) = res k' (D.ψAt χ' i' V' h') := by
  subst e e'
  exact (res_res _ _ _).trans (res_res _ _ _).symm
end GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
