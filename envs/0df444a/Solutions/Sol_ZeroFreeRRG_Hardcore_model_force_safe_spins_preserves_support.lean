-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.model_force_safe_spins_preserves_support
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:15:39.43337+00:00
-- url     : https://prove2.me/submissions/f83b84fd-f146-450a-8fec-3099cedba99a

import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_pi_positive_simplex
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_has_safe_spin
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_interaction_symmetric
import Theorems.Thm_ZeroFreeRRG_Hardcore_force_safe_spins_preserves_support
import Mathlib
set_option autoImplicit false
open AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (t : ℝ) (ht : m.PosParam t) :
    ∃ a₀ : m.Spin, ∀ (d n : ℕ) (M : Matching n d)
      (σ : Fin n → m.Spin) (S : Finset (Fin n)),
      weight m t M σ ≠ 0 →
      weight m t M (fun v => if v ∈ S then a₀ else σ v) ≠ 0 := by
  classical
  obtain ⟨a₀, ha⟩ := model_has_safe_spin m hm t ht
  refine ⟨a₀, ?_⟩
  intro d n M σ S hw
  apply force_safe_spins_preserves_support m t d n M σ S a₀
  · exact fun a => ne_of_gt ((model_pi_positive_simplex m hm t ht).1 a)
  · exact fun a => ne_of_gt (ha a)
  · intro a
    rw [model_interaction_symmetric m t a a₀]
    exact ne_of_gt (ha a)
  · exact hw
