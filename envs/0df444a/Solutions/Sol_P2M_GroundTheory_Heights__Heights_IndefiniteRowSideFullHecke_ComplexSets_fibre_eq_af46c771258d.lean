-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibre_eq_af46c771258d
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:22:28.598277+00:00
-- url     : https://prove2.me/submissions/59d46401-4771-42a6-8b6d-d19a71dfdf81

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
theorem _root_.solution (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (w : Fin d → ℂ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.fibre J A w =
      GroundTheory.Heights₂.Heights.ComplexSets.fibre J A w := by
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
    | (intros; simp [fibre]; done)
    | (intros; grind)
    | (intros; grind [fibre])
    | (intros; unfold fibre; grind)
    | (intros; simp only [fibre] at * <;> grind)
    | (intros; simp_all [fibre] <;> grind)
    | (intros; ext <;> grind [fibre])
    | (intros; constructor <;> intro _ <;> grind [fibre])
    | (intro x; cases x <;> grind [fibre])
    | (intro x; induction x <;> simp_all [fibre])
    | (intro x y; induction x <;> grind [fibre])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [fibre])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [fibre])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_13_3"



end 
