-- Prove2me | solution 1 for PI.SerBridgeGLW.isIrrChar_of_simple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:33:21.877042+00:00
-- url     : https://prove2.me/submissions/d8731051-6053-46cc-afa2-12a25e8019b1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_CharacterEqOfRepIso
import Theorems.Thm_PI_SerBridgeGLW_isChar_of_fdrep
import Theorems.Thm_PI_SerBridgeGLW_ipG_eq

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
theorem _root_.solution (hC : ConjChar) (V : FDRep ℂ G) [Simple V] : IsIrrChar V.character := by
  refine ⟨isChar_of_fdrep V, ?_⟩
  rw [ipG_eq hC, (FDRep.simple_iff_char_is_norm_one V).mp inferInstance, Nat.card_eq_fintype_card]
end PI.SerBridgeGLW
