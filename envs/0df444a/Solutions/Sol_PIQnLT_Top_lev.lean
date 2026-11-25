-- Prove2me | solution 1 for PIQnLT.Top_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:41.205604+00:00
-- url     : https://prove2.me/submissions/a75b896a-05b2-4538-9051-7595eecdc1c0

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_ExpLz
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
import Theorems.Thm_PIQnLT_EabH_lev
import Theorems.Thm_PIQnLT_lev_inj


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
theorem _root_.solution (u : ℂ) (a b : Fin (2 * r' + k + 1))
    (F : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E)
    (x : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Formalism.QuantumDeterminants.Top (Formalism.FourierDecayAlt.Q.EH k (i + r')) u (levPos k i r' a) (levPos k i r' b) F (ιLev k i r' x) =
      Formalism.QuantumDeterminants.Top (Formalism.FourierDecayAlt.Q.EH k r') u a b (fun y => F (ιLev k i r' y)) x := by
  simp only [Formalism.QuantumDeterminants.Top, Formalism.FourierDecayAlt.Q.EH]
  rw [EabH_lev hL]
  simp only [lev_inj.eq_iff]
end PIQnLT
