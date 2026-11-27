-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_twistPow_deg_f99d9fdb283d
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:25:47.367864+00:00
-- url     : https://prove2.me/submissions/00a44ece-a17c-4a1a-a4ec-d6f743457095

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_FunFieldEquivMemChartRingIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
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
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
theorem _root_.solution (M : HermLine n) (p a : ℕ) (C : ℝ) :
    (twistPow M p a C).deg = a • (p • M.deg + (HermLine.standard n).deg) := by
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
    | (intros; simp [twistPow]; done)
    | (intros; grind)
    | (intros; grind [twistPow])
    | (intros; unfold twistPow; grind)
    | (intros; simp only [twistPow] at * <;> grind)
    | (intros; simp_all [twistPow] <;> grind)
    | (intros; ext <;> grind [twistPow])
    | (intros; constructor <;> intro _ <;> grind [twistPow])
    | (intro x; cases x <;> grind [twistPow])
    | (intro x; induction x <;> simp_all [twistPow])
    | (intro x y; induction x <;> grind [twistPow])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [twistPow])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [twistPow])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_7_1"



end 
