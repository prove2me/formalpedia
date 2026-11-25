-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lowWt_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:32:11.681273+00:00
-- url     : https://prove2.me/submissions/3a272e0f-8151-4684-b732-753d2711ac45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lowWt_ht

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {μ : Fin n → ℝ} {l : List (Fin n × Fin n)} (hl : ∀ p ∈ l, IsKLow ε p) (hne : l ≠ []) :
    lowWt μ l ≠ μ := by
  intro h
  have h2 := lowWt_ht (ε := ε) μ l hl
  rw [h] at h2
  cases l with
  | nil => exact hne rfl
  | cons p l =>
    rw [List.length_cons, Nat.cast_add, Nat.cast_one] at h2
    have : (0 : ℝ) ≤ l.length := Nat.cast_nonneg _
    linarith
end ReciprocityTheory.ChartRestriction.DS
