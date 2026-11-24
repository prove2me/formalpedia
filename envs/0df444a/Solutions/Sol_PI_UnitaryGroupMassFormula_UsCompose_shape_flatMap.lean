-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.shape_flatMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:58:12.670834+00:00
-- url     : https://prove2.me/submissions/d353fe4a-5d50-4f52-9e92-f603e294d037

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development

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
theorem _root_.solution {k j ρ : ℕ} (F : Mat k (j + ρ) → E) (L : FS k (j + ρ))
    (f : SC (2 * (j + ρ) + k + 1) × List (Mat k (j + ρ)) → FS k (j + ρ)) (g : Mat k (j + ρ)) :
    shape k j ρ F (L.flatMap f) g = (L.map fun e => shape k j ρ F (f e) g).sum := by
  induction L with
  | nil => simp [shape]
  | cons e L ih =>
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← ih]
    simp only [shape, List.map_append, List.sum_append]
end PI.UnitaryGroupMassFormula.UsCompose
