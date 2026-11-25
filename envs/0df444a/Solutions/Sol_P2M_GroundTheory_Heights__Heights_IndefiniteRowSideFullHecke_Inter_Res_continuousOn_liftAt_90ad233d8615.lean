-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_continuousOn_liftAt_90ad233d8615
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:26.44942+00:00
-- url     : https://prove2.me/submissions/d0bb7c8b-71a4-4d26-87cf-9d53fe130d49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeN
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound

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
omit [Fintype K]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res
theorem _root_.solution (x : R.R.M) (q : Σ k, ι k) :
    ContinuousOn (fun y => R.liftAt x y q) (R.R.src (R.idx x)) := by
  have h : ContinuousOn (R.R.coord (R.idx x)) (R.R.src (R.idx x)) :=
    continuousOn_iff_continuous_domRestrict.mpr (R.R.isEmbedding _).continuous
  exact (MvPolynomial.continuous_eval (R.R.lift (R.idx x) q)).comp_continuousOn h
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res
