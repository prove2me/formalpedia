-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_points_eq_conePoints_7ea46e7980ef
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:58:30.207129+00:00
-- url     : https://prove2.me/submissions/3812c7b6-7427-4543-bf38-b2213bc178bd

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Points
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Mathlib
import Mathlib.Tactic






-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (chartRingZ mCoordIdeal chartLat chartLatNm secM mcPts IsArithVar)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
theorem _root_.solution (P : ArithVariety n) (F : Type*) [CommRing F] :
    P.points F = conePoints P.ideal F := by
  first
    | (intros; rfl)
    | (intros; ext; rfl)
    | (intros; exact LinearMap.ext fun _ => rfl)
    | (intros; apply Subtype.ext; rfl)
    | (intros; infer_instance)
    | (refine ⟨?_, ?_⟩ <;> infer_instance)
    | (intros; ext; simp; done)
    | (intros; assumption)
    | (intros; omega)
    | (intros; simp [points, conePoints]; done)
    | (intros; grind)
    | (intros; grind [points, conePoints])
    | (intros; unfold points conePoints; grind)
    | (intros; simp only [points, conePoints] at * <;> grind)
    | (intros; simp_all [points, conePoints] <;> grind)
    | (intros; ext <;> grind [points, conePoints])
    | (intros; constructor <;> intro _ <;> grind [points, conePoints])
    | (intro x; cases x <;> grind [points, conePoints])
    | (intro x; induction x <;> simp_all [points, conePoints])
    | (intro x y; induction x <;> grind [points, conePoints])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [points, conePoints])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [points, conePoints])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_6_1"



end 
