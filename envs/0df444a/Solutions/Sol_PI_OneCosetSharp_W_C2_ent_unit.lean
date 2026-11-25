-- Prove2me | solution 1 for PI.OneCosetSharp.W.C2.ent_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:57:23.947572+00:00
-- url     : https://prove2.me/submissions/2706e77a-dd8c-40c6-a1a6-ea752c35f7f5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_EntryEmbedMatrix
import Theorems.Thm_PI_OneCosetSharp_W_C2_entry_embedMatrix
import Theorems.Thm_PI_OneCosetSharp_W_C2_facts
import Theorems.Thm_PI_OneCosetSharp_W_C2_fIdx_lt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.OneCosetSharp.W.C2
open Loc LocE
variable {k : Type} [Field k]
private theorem fIdx_eq_cases (k₀ c n p : ℕ) :
    (p < k₀ ∧ PI.OneCosetSharp.LocE.fIdx k₀ c n p = p) ∨ (k₀ ≤ p ∧ p < k₀ + c ∧ PI.OneCosetSharp.LocE.fIdx k₀ c n p = n + (p - k₀)) ∨
      (k₀ + c ≤ p ∧ PI.OneCosetSharp.LocE.fIdx k₀ c n p = p - c) := by
  unfold PI.OneCosetSharp.LocE.fIdx
  split_ifs <;> omega
end PI.OneCosetSharp.W.C2
end
end

set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W PI.OneCosetSharp.W.C2
open Loc LocE
variable {k : Type} [Field k]
namespace PI.OneCosetSharp.W.C2
theorem _root_.solution {k₀ m t j n' c n : ℕ} (hN : Nums k₀ m t j n' c n) (τ : FC n' (c + 1) n c → k) {p p' : ℕ}
    (hp : p < n + c) (hp' : p' < n' + (c + 1)) (hcol : p' ≤ k₀ ∨ k₀ + c < p') :
    ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) p p' = if p = p' then 1 else 0 := by
  obtain ⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩ := facts hN
  have hR := fIdx_eq_cases k₀ c n p
  have hS := fIdx_eq_cases k₀ (c + 1) n' p'
  have hrl : PI.OneCosetSharp.LocE.fIdx k₀ c n p < n + c := fIdx_lt (by omega) hp
  have hsl : PI.OneCosetSharp.LocE.fIdx k₀ (c + 1) n' p' < n' + (c + 1) := fIdx_lt hk hp'
  rw [entry_embedMatrix k₀ _ _ p p' hrl hsl]
  generalize PI.OneCosetSharp.LocE.fIdx k₀ c n p = r at hR hrl ⊢
  generalize PI.OneCosetSharp.LocE.fIdx k₀ (c + 1) n' p' = s at hS hsl ⊢
  simp only [xj0, LinearMap.toMatrix'_toLin', Matrix.of_apply]
  split_ifs <;> first | rfl | (exfalso; (try simp only [PI.OneCosetSharp.Loc.IsFree] at *); omega)
end PI.OneCosetSharp.W.C2
