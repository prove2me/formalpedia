-- Prove2me | solution 1 for P2M_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg__At_trans_8cc8ae9ac14b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:30:30.802228+00:00
-- url     : https://prove2.me/submissions/adad40a4-163a-438b-8198-53e642e7c47d

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
theorem _root_.solution (χ : D.X) (i i' : D.P.L.ι) {V V' W} (h h') (k : W ≤ V) (k' : W ≤ V') (hW) :
    res k (D.ψAt χ i V h) = (D.gAt (D.cK χ).left i i' W hW)⁻¹ * res k' (D.ψAt χ i' V' h') := by
  have H := congrArg (res (le_inf (fun _ hy => Set.mem_iInter.2 fun _ => h (k hy))
    (fun _ hy => Set.mem_iInter.2 fun _ => h' (k' hy)) : W ≤ _ ⊓ _))
    (D.ψ_gen χ (fun _ => i) (fun _ => i'))
  rw [map_mul, res_res, res_res] at H
  refine (res_res _ _ _).trans (H.trans ?_)
  refine congrArg₂ (· * ·) ?_ ?_
  · simp only [LB.LinComb, Finset.univ_unique, Finset.prod_singleton, map_zpow, zpow_neg, zpow_one, map_inv]
    exact congrArg (·⁻¹) (res_res _ _ _)
  · exact (res_res _ _ _).symm
end GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
