-- Prove2me | solution 1 for PI.StabPairs.Conv.ut_sub_one_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:15:56.039392+00:00
-- url     : https://prove2.me/submissions/0a66e482-c84a-419b-a6ec-4ce2786eb4d7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConvAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_UtSubOneLast

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
open PI PI.StabPairs PI.StabPairs.Conv
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW
namespace PI.StabPairs.Conv
theorem _root_.solution {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1))
    (c d : Fin (r + 1)) (h : c.val ≤ d.val) : (u - 1) d c = 0 := by
  rcases lt_or_eq_of_le h with h | h
  · rw [Matrix.sub_apply, hu.1 d c h, Matrix.one_apply_ne (by intro e; subst e; omega), sub_self]
  · have : c = d := Fin.ext h
    subst this; rw [Matrix.sub_apply, hu.2, Matrix.one_apply_eq, sub_self]
end PI.StabPairs.Conv
