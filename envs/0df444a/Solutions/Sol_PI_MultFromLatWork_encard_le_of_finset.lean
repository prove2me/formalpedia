-- Prove2me | solution 1 for PI.MultFromLatWork.encard_le_of_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:03:51.932874+00:00
-- url     : https://prove2.me/submissions/81220292-e068-4d4c-9723-cfc3bfe1a5a2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatCountG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeMultiplicity_EncardLeOfFinset
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Matrix
open scoped ENNReal
noncomputable section
open PI PI.MultFromLatWork
open Formalism.REAL
namespace PI.MultFromLatWork
theorem _root_.solution {α : Type*} (T : Set α) (B : ℝ)
    (h : ∀ s : Finset α, (↑s : Set α) ⊆ T → (s.card : ℝ) ≤ B) :
    ((T.encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal B := by
  by_cases hT : T.Finite
  · have hs := h hT.toFinset (by simp)
    rw [hT.encard_eq_coe_toFinset_card]
    simp only [ENat.toENNReal_coe]
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hs
  · exfalso
    obtain ⟨t, ht, hc⟩ := Set.Infinite.exists_subset_card_eq hT (⌈B⌉₊ + 1)
    have h1 := h t ht
    rw [hc] at h1
    push_cast at h1
    have h2 := Nat.le_ceil B
    linarith
end PI.MultFromLatWork
