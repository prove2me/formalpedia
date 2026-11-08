-- Prove2me | solution 1 for QBFBackdoor.dual_holds_iff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:28:26.12198+00:00
-- url     : https://prove2.me/submissions/056919c3-811a-49bd-8a50-b09e29e1a861

import Mathlib
import Definitions.Def_QBFBackdoor_dual

open MDPComplexity.PartiallyObserved

open QBFBackdoor in
theorem solution {n m : ℕ} (φ : QBF n m) :
    (QBFBackdoor.dual φ).disj.length = m ∧ (φ.holds ↔ ¬ (QBFBackdoor.dual φ).holds) := by
  have base : ∀ x, φ.Sat x ↔ ¬ (QBFBackdoor.dual φ).Sat x := by
    intro x
    constructor
    · rintro h ⟨ϕ, hϕ, hsat⟩
      simp only [QBFBackdoor.dual, List.mem_ofFn] at hϕ
      obtain ⟨i, rfl⟩ := hϕ
      obtain ⟨l, hl, hx⟩ := h i
      have := hsat (QBFBackdoor.GAtom.unit l.1 (!l.2))
        (List.mem_map.2 ⟨l, Finset.mem_toList.2 hl, rfl⟩)
      simp only [QBFBackdoor.GAtom.Sat] at this
      rw [hx] at this
      cases h2 : l.2 <;> simp [h2] at this
    · intro h i
      by_contra hne
      push_neg at hne
      apply h
      refine ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, ?_⟩
      intro C hC
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hC
      simp only [QBFBackdoor.GAtom.Sat]
      have := hne l (Finset.mem_toList.1 hl)
      cases h1 : x l.1 <;> cases h2 : l.2 <;> simp_all
  have key : ∀ d k x, n - k = d → (φ.holdsFrom k x ↔
      ¬ QBFBackdoor.prefixHoldsFrom (QBFBackdoor.dual φ).q (QBFBackdoor.dual φ).Sat k x) := by
    intro d
    induction d with
    | zero =>
      intro k x hk
      rw [QBF.holdsFrom, QBFBackdoor.prefixHoldsFrom, dif_neg (by omega), dif_neg (by omega)]
      exact base x
    | succ d ih =>
      intro k x hk
      rw [QBF.holdsFrom, QBFBackdoor.prefixHoldsFrom, dif_pos (by omega : k < n),
        dif_pos (by omega : k < n)]
      by_cases hqk : φ.q ⟨k, by omega⟩ = true
      swap
      · rw [if_neg hqk, if_pos (by simp [QBFBackdoor.dual] at hqk ⊢; exact hqk)]
        exact ⟨fun h ⟨b, hb⟩ => (ih (k + 1) _ (by omega)).1 (h b) hb,
          fun h b => (ih (k + 1) _ (by omega)).2 (fun hb => h ⟨b, hb⟩)⟩
      · rw [if_pos hqk, if_neg (by simp [QBFBackdoor.dual, hqk])]
        constructor
        · rintro ⟨b, hb⟩ hall
          exact (ih (k + 1) _ (by omega)).1 hb (hall b)
        · intro h
          by_contra hne
          push_neg at hne
          apply h
          intro b
          by_contra hd
          exact hne b ((ih (k + 1) _ (by omega)).2 hd)
  refine ⟨by simp [QBFBackdoor.dual], ?_⟩
  exact key (n - 0) 0 _ rfl
