-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_analyticAt_liftAt_b90f8c15a691
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:10:40.807801+00:00
-- url     : https://prove2.me/submissions/e832af4f-5cdf-4bb7-80f2-8b34ae8f5288

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeN
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_isGoodAtlas_7b36ff3bea7c

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial MeasureTheory Topology Filter Set
open scoped ContDiff
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential MIntegrable locDens)
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res
variable {P : Ideal (MRing ι ℂ)} {e : ℕ} (R : Res ι P e)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res
theorem _root_.solution (x : R.R.M) (q : Σ k, ι k) (j : Fin R.atlas.n) {u : Fin e → ℂ}
    (hu : u ∈ (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x)) :
    AnalyticAt ℂ (fun v => R.liftAt x ((R.atlas.chart j).symm v) q) u :=
  R.isGoodAtlas.1 (R.idx x) (R.R.lift (R.idx x) q) j u hu
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res
