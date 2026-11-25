-- Prove2me | solution 1 for PI.SerBridgeGLW.iso_of_character_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:22:13.491146+00:00
-- url     : https://prove2.me/submissions/3d129c3a-ba80-48f0-ab01-c9ee9a5ecc31

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_CharacterEqOfRepIso
import Theorems.Thm_P2M_PI_SerBridgeGLW_card_ne_zero__dc2cceebfad7

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
theorem _root_.solution (V W : FDRep ℂ G) [Simple V] [Simple W] (h : V.character = W.character) :
    Nonempty (V ≅ W) := by
  classical
  haveI : Invertible ((Nat.card G : ℕ) : ℂ) := invertibleOfNonzero card_ne_zero'
  have h1 := FDRep.char_orthonormal V W
  have h2 := FDRep.char_orthonormal V V
  rw [if_pos ⟨Iso.refl V⟩] at h2
  rw [← h, h2] at h1
  by_contra hn
  rw [if_neg hn] at h1
  exact one_ne_zero h1
end PI.SerBridgeGLW
