-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_continuousOn_segre_lift_63fa5bef8928
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:21:57.210237+00:00
-- url     : https://prove2.me/submissions/e7beb09d-3b1e-4cc4-8380-67c3050feab8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularFibre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_continuousOn_lift


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution {e n : ℕ} (R : AnLogRes P J e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x₀ : R.X) :
    ContinuousOn (fun x => Ψ (segre (R.lift x₀ x))) (R.U x₀) := by
  have hl : ContinuousOn (fun x => R.lift x₀ x) (R.U x₀) :=
    continuousOn_pi.mpr fun p => continuousOn_lift R x₀ p
  have hs : Continuous (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) :=
    continuous_pi fun i => continuous_finsetProd Finset.univ fun k _ => continuous_apply _
  exact (LinearMap.continuous_of_finiteDimensional Ψ).comp_continuousOn (hs.comp_continuousOn hl)
end GroundTheory.Heights₂.Heights.Targets
