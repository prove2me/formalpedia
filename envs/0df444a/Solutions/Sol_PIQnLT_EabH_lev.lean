-- Prove2me | solution 1 for PIQnLT.EabH_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:23:56.200605+00:00
-- url     : https://prove2.me/submissions/2f1b5b40-2d8c-4a1f-8371-ee5f86714662

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_ExpLz
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
import Theorems.Thm_PIQnLT_hpart1_lev
import Theorems.Thm_PIQnLT_hpart2_lev
import Theorems.Thm_PIQnLT_RdV_Lz

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
theorem _root_.solution (a b : Fin (2 * r' + k + 1))
    (F : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E)
    (x : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    EabH (Hpk k (i + r')) (levPos k i r' a) (levPos k i r' b) F (ιLev k i r' x) =
      EabH (Hpk k r') a b (fun y => F (ιLev k i r' y)) x := by
  simp only [EabH]
  rw [hpart1_lev, hpart2_lev, RdV_Lz hL, RdV_Lz hL]
end PIQnLT
