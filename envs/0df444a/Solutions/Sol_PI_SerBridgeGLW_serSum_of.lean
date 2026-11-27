-- Prove2me | solution 1 for PI.SerBridgeGLW.serSum_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:16:31.123912+00:00
-- url     : https://prove2.me/submissions/93819604-3c2a-482f-8c7a-d4019b322d22

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_CharacterEqOfRepIso
import Theorems.Thm_PI_SerBridgeGLW_irrSys_of
import Theorems.Thm_PI_SerBridgeGLW_eOf_eq_zIdem
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
open PI PI.SerBridgeGLW
namespace PI.SerBridgeGLW
theorem _root_.solution (hC : ConjChar) : SerSum := by
  intro g _ cv r I _ ρ hs hi he f
  classical
  obtain ⟨hchar, hinj⟩ := irrSys_of hC _ I ρ hs hi he
  set χ : I → (GL (Fin r) (ZMod g) → ℂ) := fun i => (ρ i).character with hχ
  set s : Set I := {i | InSeries cv.ι cv.gen (χ i) f}
  have hset : {ψ : GL (Fin r) (ZMod g) → ℂ | IsIrrChar ψ ∧ InSeries cv.ι cv.gen ψ f} = χ '' s := by
    ext ψ
    simp only [Set.mem_ofPred_eq, Set.mem_image, s]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨i, rfl⟩ := (hchar ψ).mp h1
      exact ⟨i, h2, rfl⟩
    · rintro ⟨i, h2, rfl⟩
      exact ⟨(hchar _).mpr ⟨i, rfl⟩, h2⟩
  have h1 : eSerC cv.ι cv.gen r f = ∑ᶠ ψ ∈ χ '' s, eOf ψ := by
    rw [← hset]; rfl
  rw [h1, finsum_mem_image (fun i _ j _ h => hinj i j h)]
  rw [finsum_mem_eq_toFinset_sum]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr
  · ext i; simp [s, hχ]
  · intro i _; exact eOf_eq_zIdem _
end PI.SerBridgeGLW
