-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smoothNear_iff_609a349cd38a
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:22:26.673433+00:00
-- url     : https://prove2.me/submissions/c7512219-0e03-49d6-bb99-477fbf25a5aa

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial MeasureTheory Filter Topology Matrix
noncomputable section
variable {n d : ℕ}
theorem _root_.solution (S : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SmoothNear S f ↔ GroundTheory.Heights₂.Heights.SmoothNear S f := by
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
    | (intros; simp [SmoothNear]; done)
    | (intros; grind)
    | (intros; grind [SmoothNear])
    | (intros; unfold SmoothNear; grind)
    | (intros; simp only [SmoothNear] at * <;> grind)
    | (intros; simp_all [SmoothNear] <;> grind)
    | (intros; ext <;> grind [SmoothNear])
    | (intros; constructor <;> intro _ <;> grind [SmoothNear])
    | (intro x; cases x <;> grind [SmoothNear])
    | (intro x; induction x <;> simp_all [SmoothNear])
    | (intro x y; induction x <;> grind [SmoothNear])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [SmoothNear])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [SmoothNear])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_13_0"



end 
