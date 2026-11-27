-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_linVal_eq_6dd5ea6c23e8
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:22:27.381157+00:00
-- url     : https://prove2.me/submissions/db79db56-204d-459b-8036-4d9def2832f3

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
theorem _root_.solution (u x : Fin n → ℂ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.linVal u x = GroundTheory.Heights₂.Heights.linEval u x := by
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
    | (intros; simp [linEval, linVal]; done)
    | (intros; grind)
    | (intros; grind [linEval, linVal])
    | (intros; unfold linEval linVal; grind)
    | (intros; simp only [linEval, linVal] at * <;> grind)
    | (intros; simp_all [linEval, linVal] <;> grind)
    | (intros; ext <;> grind [linEval, linVal])
    | (intros; constructor <;> intro _ <;> grind [linEval, linVal])
    | (intro x; cases x <;> grind [linEval, linVal])
    | (intro x; induction x <;> simp_all [linEval, linVal])
    | (intro x y; induction x <;> grind [linEval, linVal])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [linEval, linVal])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [linEval, linVal])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_13_1"



end 
