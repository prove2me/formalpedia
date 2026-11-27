-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_zeroLocus_eq_f6d2d9a3acc9
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:22:28.982462+00:00
-- url     : https://prove2.me/submissions/79472705-2055-44dd-90b8-f320ad6566b6

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
theorem _root_.solution (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.zeroLocus J =
      GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J := by
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
    | (intros; simp [zeroLocus]; done)
    | (intros; grind)
    | (intros; grind [zeroLocus])
    | (intros; unfold zeroLocus; grind)
    | (intros; simp only [zeroLocus] at * <;> grind)
    | (intros; simp_all [zeroLocus] <;> grind)
    | (intros; ext <;> grind [zeroLocus])
    | (intros; constructor <;> intro _ <;> grind [zeroLocus])
    | (intro x; cases x <;> grind [zeroLocus])
    | (intro x; induction x <;> simp_all [zeroLocus])
    | (intro x y; induction x <;> grind [zeroLocus])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [zeroLocus])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [zeroLocus])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_14_0"



end 
