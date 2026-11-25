-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointsBilinear_cxHessian_cons_dc6d4d8f0ae5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:47:18.754178+00:00
-- url     : https://prove2.me/submissions/2d67711b-3df5-4316-8020-4281a7c07f85

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsBilinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsBilinear

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
open GroundTheory.Heights₂.Heights.PointsBilinear
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.PointsBilinear
theorem _root_.solution {n : ℕ} (L : Fin n → HermLine ι) (f v : ((Σ k, ι k) → ℂ) → ℝ)
    (γ : (Fin (n + 1) → ℂ) → (Σ k, ι k) → ℂ) (y : Fin (n + 1) → ℂ) :
    (fun k => cxHessian
        (fun y' => (Fin.cons f (pot L) : Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) k (γ y')) y) =
      Function.update (fun k => cxHessian
        (fun y' => (Fin.cons v (pot L) : Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) k (γ y')) y) 0
        (cxHessian (fun y' => f (γ y')) y) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · rw [Function.update_self]
    simp only [Fin.cons_zero]
  · rw [Function.update_of_ne (Fin.succ_ne_zero j)]
    simp only [Fin.cons_succ]
end GroundTheory.Heights₂.Heights.PointsBilinear
