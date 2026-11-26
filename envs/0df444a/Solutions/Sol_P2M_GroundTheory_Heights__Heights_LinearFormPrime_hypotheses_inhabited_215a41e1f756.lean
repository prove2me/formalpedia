-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinearFormPrime_hypotheses_inhabited_215a41e1f756
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:08:05.376912+00:00
-- url     : https://prove2.me/submissions/decedc73-43d9-4534-bd7d-49eadf3248fa

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
theorem _root_.solution : (fun _ : Fin 1 => (1 : ℚ)) ≠ 0 := by
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
    | (intros; simp []; done)
    | (intros; grind)
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_1_3"



end 
