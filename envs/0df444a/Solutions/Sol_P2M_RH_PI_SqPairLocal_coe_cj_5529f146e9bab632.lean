-- Prove2me | solution 1 for P2M_RH_PI_SqPairLocal_coe_cj_5529f146e9bab632
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:06:15.056323+00:00
-- url     : https://prove2.me/submissions/fc8e6700-78d6-4390-935f-2e89b3efe09c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IntAtOfDivAtZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
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
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair
attribute [local instance] StModel.cr StModel.dom StModel.dvr StModel.hens StModel.fin
variable {E : Type} [Field E] [NumberField E] [StarRing E]
theorem _root_.solution (x : 𝓞 E) : ((cj E x : 𝓞 E) : E) = star (x : E) := by
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
    | (intros; simp [cj]; done)
    | (intros; grind)
    | (intros; grind [cj])
    | (intros; unfold cj; grind)
    | (intros; simp only [cj] at * <;> grind)
    | (intros; simp_all [cj] <;> grind)
    | (intros; ext <;> grind [cj])
    | (intros; constructor <;> intro _ <;> grind [cj])
    | (intro x; cases x <;> grind [cj])
    | (intro x; induction x <;> simp_all [cj])
    | (intro x y; induction x <;> grind [cj])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [cj])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [cj])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_42_0"



end 
