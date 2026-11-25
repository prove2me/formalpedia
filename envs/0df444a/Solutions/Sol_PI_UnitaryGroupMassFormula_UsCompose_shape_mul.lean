-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.shape_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:10:21.423926+00:00
-- url     : https://prove2.me/submissions/5d525fa2-021d-4b83-a2d6-1ef2e61d853a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_sv_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PI.UnitaryGroupMassFormula.UsCompose
theorem _root_.solution {k j ρ : ℕ} (F : Mat k (j + ρ) → E) (s : SC (2 * (j + ρ) + k + 1)) (M : FS k (j + ρ))
    (g : Mat k (j + ρ)) :
    shape k j ρ F (M.map fun e => (mulSC s e.1, e.2)) g = sv k j ρ s g • shape k j ρ F M g := by
  induction M with
  | nil => simp [shape]
  | cons e M ih =>
    simp only [shape, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, sv_mul, mul_smul, smul_add]
end PI.UnitaryGroupMassFormula.UsCompose
