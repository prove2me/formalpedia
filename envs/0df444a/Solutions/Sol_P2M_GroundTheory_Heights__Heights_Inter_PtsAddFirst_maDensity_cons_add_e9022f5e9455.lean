-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_maDensity_cons_add_e9022f5e9455
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:52:35.802838+00:00
-- url     : https://prove2.me/submissions/928b5595-8d73-4a29-9654-c41df077edc9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAddFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsAddFirst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_mixedDisc_cons_add_c2f52a1c9aba

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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Inter
namespace PtsAddFirst
theorem _root_.solution {D : ℕ} (f g h : (Fin (D + 1) → ℂ) → ℝ)
    (ψ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (y : Fin (D + 1) → ℂ)
    (hH : cxHessian h y = cxHessian f y + cxHessian g y) :
    maDensity (Fin.cons h ψ) y = maDensity (Fin.cons f ψ) y + maDensity (Fin.cons g ψ) y := by
  have hc : ∀ u : (Fin (D + 1) → ℂ) → ℝ, (fun k => cxHessian ((Fin.cons u ψ : Fin (D + 1) → _) k) y) =
      Fin.cons (cxHessian u y) (fun k => cxHessian (ψ k) y) := by
    intro u
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  simp only [maDensity, hc, hH, PtsAddFirst.mixedDisc_cons_add, Complex.add_re]
  ring
end PtsAddFirst
end GroundTheory.Heights₂.Heights.Inter
