-- Prove2me | solution 1 for P2M_PI_SerBridgeGLW_card_ne_zero__dc2cceebfad7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:50:09.399007+00:00
-- url     : https://prove2.me/submissions/25b5cfbc-3f8c-4870-bc6f-f04caa7b013a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_CharacterEqOfRepIso

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
variable {G : Type} [Group G] [Fintype G]
namespace PI.SerBridgeGLW
theorem _root_.solution : (Nat.card G : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr Nat.card_pos.ne'
end PI.SerBridgeGLW
