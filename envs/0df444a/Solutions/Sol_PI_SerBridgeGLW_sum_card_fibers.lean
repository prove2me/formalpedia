-- Prove2me | solution 1 for PI.SerBridgeGLW.sum_card_fibers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:29:09.10099+00:00
-- url     : https://prove2.me/submissions/47df217b-c5d6-4766-96a9-8fa915e3078e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_CharacterEqOfRepIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ClassFnOfIsIrrChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
open PI PI.SerBridgeGLW
namespace PI.SerBridgeGLW
theorem _root_.solution {r s : ℕ} (b : Fin r → Fin s) : ∑ j, Fintype.card {i // b i = j} = r := by
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv b)
  rw [Fintype.card_sigma, Fintype.card_fin] at h
  exact h
end PI.SerBridgeGLW
