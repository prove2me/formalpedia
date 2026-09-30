-- Prove2me | solution 2 for RevenueManagement.second_price_dominant
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T21:44:34.675888+00:00
-- url     : https://prove2.me/submissions/5f9395b6-d015-44f3-afa6-1fd8aaa0eaf0

import Mathlib
import Definitions.Def_RevenueManagement_auctions

namespace RevenueManagement

end RevenueManagement

open RevenueManagement
theorem solution {m : ℕ} (v b : ℝ) (others : Fin m → ℝ) :
    spSurplus v b others ≤ spSurplus v v others := by
  unfold spSurplus
  split_ifs with hb hv hv
  · exact le_refl _
  · -- hb : ∀ j, others j < b ; hv : ¬ ∀ j, others j < v
    push Not at hv
    obtain ⟨j, hj⟩ := hv
    have hbdd : BddAbove (Set.range others) := ⟨b, fun x ⟨i, hi⟩ => hi ▸ (hb i).le⟩
    have : others j ≤ sSup (Set.range others) := le_csSup hbdd ⟨j, rfl⟩
    linarith
  · -- hb: ¬∀ j, others j < b ; hv : ∀ j, others j < v
    push Not at hb
    obtain ⟨j0, hj0⟩ := hb
    have hne : (Set.range others).Nonempty := ⟨others j0, j0, rfl⟩
    have hub : ∀ x ∈ Set.range others, x ≤ v := fun x ⟨i, hi⟩ => hi ▸ (hv i).le
    have : sSup (Set.range others) ≤ v := csSup_le hne hub
    linarith
  · exact le_refl _

