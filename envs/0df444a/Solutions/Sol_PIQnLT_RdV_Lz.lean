-- Prove2me | solution 1 for PIQnLT.RdV_Lz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:09:27.445247+00:00
-- url     : https://prove2.me/submissions/c8791abc-1f3e-41eb-a59b-54a2ce3d0ddb

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_ExpLz
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
import Theorems.Thm_PIQnLT_Lz_smul
import Theorems.Thm_PIQnLT_exp_Lz


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
namespace PIQnLT
theorem _root_.solution (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (F : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E)
    (x : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    RdV (Lz k i r' X) F (ιLev k i r' x) = RdV X (fun y => F (ιLev k i r' y)) x := by
  unfold RdV
  congr 1
  funext t
  rw [← Lz_smul, exp_Lz hL, ← (hL k i r').2]
end PIQnLT
