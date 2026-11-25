-- Prove2me | solution 1 for PI.OneCosetSharp.W.C2.sum_eq_chArg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:00:57.857199+00:00
-- url     : https://prove2.me/submissions/914f8373-ff25-4634-ae91-8b898e70448c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_EntryEmbedMatrix
import Theorems.Thm_PI_OneCosetSharp_W_C2_facts
import Theorems.Thm_PI_OneCosetSharp_W_C2_ent_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W PI.OneCosetSharp.W.C2
open Loc LocE
variable {k : Type} [Field k]
namespace PI.OneCosetSharp.W.C2
theorem _root_.solution {k₀ m t j n' c n : ℕ} (hN : Nums k₀ m t j n' c n) (τ : FC n' (c + 1) n c → k) :
    ∑ i ∈ Finset.range (k₀ + m - 1 - 1), ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) i (i + 1) =
      chArg (n' := n') (c' := c + 1) (n := n) (c := c) (xx1 (xj0 k₀ n' n) τ) := by
  obtain ⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩ := facts hN
  have hsplit : k₀ + m - 1 - 1 = k₀ + (c + (k₀ + m - 1 - 1 - k₀ - c)) := by omega
  rw [hsplit, Finset.sum_range_add, Finset.sum_range_add]
  have hz : ∀ i, i + 1 < n' + (c + 1) → (i + 1 ≤ k₀ ∨ k₀ + c < i + 1) →
      PI.OneCosetSharp.ent k₀ (c + 1) n' c n (PI.OneCosetSharp.Loc.xx1 (xj0 k₀ n' n) τ) i (i + 1) = 0 := by
    intro i hi hcol
    rw [ent_unit hN τ (by omega) hi hcol, if_neg (by omega)]
  have h1 : ∑ i ∈ Finset.range k₀, PI.OneCosetSharp.ent k₀ (c + 1) n' c n (PI.OneCosetSharp.Loc.xx1 (xj0 k₀ n' n) τ) i (i + 1) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_range] at hi
      exact hz i (by omega) (by omega)
  have h3 : ∑ x ∈ Finset.range (k₀ + m - 1 - 1 - k₀ - c),
      PI.OneCosetSharp.ent k₀ (c + 1) n' c n (PI.OneCosetSharp.Loc.xx1 (xj0 k₀ n' n) τ) (k₀ + (c + x)) (k₀ + (c + x) + 1) = 0 :=
    Finset.sum_eq_zero fun x hx => by
      rw [Finset.mem_range] at hx
      exact hz _ (by omega) (by omega)
  simp only [h1, h3, zero_add, add_zero]
  unfold PI.OneCosetSharp.Loc.chArg
  refine Finset.sum_congr rfl fun e he => ?_
  rw [Finset.mem_range] at he
  unfold PI.OneCosetSharp.ent
  have e1 : PI.OneCosetSharp.LocE.fIdx k₀ (c + 1) n' (k₀ + e + 1) = n' + e + 1 := by
    unfold PI.OneCosetSharp.LocE.fIdx
    split_ifs <;> omega
  have e2 : PI.OneCosetSharp.LocE.fIdx k₀ c n (k₀ + e) = n + e := by
    unfold PI.OneCosetSharp.LocE.fIdx
    split_ifs <;> omega
  rw [e1, e2]
end PI.OneCosetSharp.W.C2
