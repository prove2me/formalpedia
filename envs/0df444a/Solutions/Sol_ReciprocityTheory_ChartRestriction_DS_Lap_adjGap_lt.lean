-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.adjGap_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:21:51.660081+00:00
-- url     : https://prove2.me/submissions/1c5fdc86-7505-4497-abbb-ecb4814ba2b4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_adjGap_exists_change

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS.Lap
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (hs : StrictAnti lam)
    (hadj : ∀ (a : Fin n) (ha : a.val + 1 < n), ε a ≠ ε ⟨a.val + 1, ha⟩ →
      h ≤ lam a - lam ⟨a.val + 1, ha⟩)
    (a b : Fin n) (hab : a.val < b.val) (hne : ε a ≠ ε b) : h ≤ lam a - lam b := by
  let f : ℕ → Bool := fun m => if hm : m < n then ε ⟨m, hm⟩ else false
  have hfa : ∀ x : Fin n, f x.val = ε x := fun x => by simp [f, x.2]
  obtain ⟨c, hc1, hc2, hc3⟩ := adjGap_exists_change f (b.val - a.val) a.val (by
    rw [show a.val + (b.val - a.val) = b.val by omega, hfa, hfa]
    exact hne)
  have hcn : c + 1 < n := by have := b.2; omega
  have hcn' : c < n := by omega
  have hne' : ε ⟨c, hcn'⟩ ≠ ε ⟨c + 1, hcn⟩ := by
    rw [← hfa ⟨c, hcn'⟩, ← hfa ⟨c + 1, hcn⟩]
    exact hc3
  have h1 : h ≤ lam ⟨c, hcn'⟩ - lam ⟨c + 1, hcn⟩ := hadj ⟨c, hcn'⟩ hcn hne'
  have h2 : lam ⟨c, hcn'⟩ ≤ lam a := hs.antitone (by rw [Fin.le_iff_val_le_val]; exact hc1)
  have h3 : lam b ≤ lam ⟨c + 1, hcn⟩ := hs.antitone (by rw [Fin.le_iff_val_le_val]; show c + 1 ≤ b.val; omega)
  linarith
end ReciprocityTheory.ChartRestriction.DS.Lap
