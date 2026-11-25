-- Prove2me | solution 1 for PI.SerBridgeGLW.irrSys_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:46:42.656266+00:00
-- url     : https://prove2.me/submissions/0e2f3a5d-478d-4a09-93df-426ff830d868

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_CharacterEqOfRepIso
import Theorems.Thm_PI_SerBridgeGLW_irrCharIff_of
import Theorems.Thm_PI_SerBridgeGLW_iso_of_character_eq
import Theorems.Thm_PI_SerBridgeGLW_repIso_of_iso
import Theorems.Thm_PI_SerBridgeGLW_character_eq_of_repIso

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
theorem _root_.solution (hC : ConjChar) : IrrSys := by
  intro G _ _ I _ ρ hs hi he
  have hI := irrCharIff_of hC
  refine ⟨fun χ => ⟨fun hχ => ?_, ?_⟩, fun i j hij => ?_⟩
  · obtain ⟨V, hV, rfl⟩ := (hI G χ).mp hχ
    obtain ⟨i, hi'⟩ := he V hV
    exact ⟨i, character_eq_of_repIso hi'⟩
  · rintro ⟨i, rfl⟩
    exact (hI G _).mpr ⟨ρ i, hs i, rfl⟩
  · haveI := hs i; haveI := hs j
    obtain ⟨e⟩ := iso_of_character_eq (ρ i) (ρ j) hij
    exact hi i j (repIso_of_iso e)
end PI.SerBridgeGLW
