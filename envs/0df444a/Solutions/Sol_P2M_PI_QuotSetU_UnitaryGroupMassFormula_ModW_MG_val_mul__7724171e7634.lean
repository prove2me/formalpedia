-- Prove2me | solution 1 for P2M_PI_QuotSetU_UnitaryGroupMassFormula_ModW_MG_val_mul__7724171e7634
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:06:14.263988+00:00
-- url     : https://prove2.me/submissions/d7efc894-c584-43f6-83c4-ea7c41874ec8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Mathlib.Tactic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped ENNReal NNReal
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.ModW
open PI
variable {m : ℕ}
variable {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}
open PI.QuotSetU.UnitaryGroupMassFormula.ModW.MG
theorem _root_.solution (x y : MG G hG) : (x * y).val = rmulQ y.toM x.val := by
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
    | (intros; simp [MG, toM, val]; done)
    | (intros; grind)
    | (intros; grind [MG, toM, val])
    | (intros; unfold MG toM val; grind)
    | (intros; simp only [MG, toM, val] at * <;> grind)
    | (intros; simp_all [MG, toM, val] <;> grind)
    | (intros; ext <;> grind [MG, toM, val])
    | (intros; constructor <;> intro _ <;> grind [MG, toM, val])
    | (intro x; cases x <;> grind [MG, toM, val])
    | (intro x; induction x <;> simp_all [MG, toM, val])
    | (intro x y; induction x <;> grind [MG, toM, val])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [MG, toM, val])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [MG, toM, val])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_40_0"



end 
