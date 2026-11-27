-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_withFirst_eq_37578fdc4898
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:22:28.04687+00:00
-- url     : https://prove2.me/submissions/5a842cb0-67c5-4ff4-826e-df36acec8676

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
theorem _root_.solution {e : ℕ} (f : (Fin n → ℂ) → ℝ) (ψ : Fin e → (Fin n → ℂ) → ℝ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.withFirst f ψ = Matrix.vecCons f ψ := by
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
    | (intros; simp [withFirst]; done)
    | (intros; grind)
    | (intros; grind [withFirst])
    | (intros; unfold withFirst; grind)
    | (intros; simp only [withFirst] at * <;> grind)
    | (intros; simp_all [withFirst] <;> grind)
    | (intros; ext <;> grind [withFirst])
    | (intros; constructor <;> intro _ <;> grind [withFirst])
    | (intro x; cases x <;> grind [withFirst])
    | (intro x; induction x <;> simp_all [withFirst])
    | (intro x y; induction x <;> grind [withFirst])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [withFirst])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [withFirst])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_13_2"



end 
