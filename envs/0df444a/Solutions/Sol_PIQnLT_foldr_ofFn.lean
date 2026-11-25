-- Prove2me | solution 1 for PIQnLT.foldr_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:21:34.61433+00:00
-- url     : https://prove2.me/submissions/bb0fb7f0-53ce-4055-baf2-8e4d4b1103e1

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_ExpLz
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PIQnLT
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k i r' : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (hL : LevHom)
include hL
omit hL
namespace PIQnLT
theorem _root_.solution {α β : Type*} {t : ℕ} (R : α → β) (Tb : Fin t → α → α) (Ts : Fin t → β → β)
    (h : ∀ j G, R (Tb j G) = Ts j (R G)) (F : α) :
    R ((List.ofFn Tb).foldr (fun T h => T h) F) = (List.ofFn Ts).foldr (fun T h => T h) (R F) := by
  induction t generalizing F with
  | zero => simp
  | succ t ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.foldr_cons, List.foldr_cons, h]
    exact congrArg _ (ih (fun j => Tb j.succ) (fun j => Ts j.succ) (fun j G => h j.succ G) F)
end PIQnLT
