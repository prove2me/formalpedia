-- Prove2me | solution 1 for P2M_NormOnePowProof_coe___9ed0e2e30865
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:08:46.783462+00:00
-- url     : https://prove2.me/submissions/e40c9f1f-31ea-45fd-b071-5dc1d23c3226

import Definitions.Def_Formalism_PeriodIntegrals_NormOnePow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormOnePowerPrincipal_PowPrincipal
import Mathlib.Tactic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors
open NormOnePowProof
variable {E : Type} [Field E] [NumberField E]
theorem _root_.solution (c : E →+* E) (y : 𝓞 E) : ((σ c y : 𝓞 E) : E) = c (y : E) := by
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
    | (intros; simp [σ]; done)
    | (intros; grind)
    | (intros; grind [σ])
    | (intros; unfold σ; grind)
    | (intros; simp only [σ] at * <;> grind)
    | (intros; simp_all [σ] <;> grind)
    | (intros; ext <;> grind [σ])
    | (intros; constructor <;> intro _ <;> grind [σ])
    | (intro x; cases x <;> grind [σ])
    | (intro x; induction x <;> simp_all [σ])
    | (intro x y; induction x <;> grind [σ])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [σ])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [σ])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_21_0"



