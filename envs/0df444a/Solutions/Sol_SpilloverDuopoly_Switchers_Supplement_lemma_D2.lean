-- Prove2me | solution 1 for SpilloverDuopoly.Switchers.Supplement.lemma_D2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:20:51.994407+00:00
-- url     : https://prove2.me/submissions/65ac5893-3272-4c12-8230-eca24e818122

import Mathlib
import Definitions.Def_SpilloverDuopoly_Switchers_Supplement_ThreePeriod

open SpilloverDuopoly
open SpilloverDuopoly.Switchers
open SpilloverDuopoly.Switchers.Supplement

/-- Lemma D.2 (p. 52 (PDF 54)): if neither of the segment's earlier purchases `k`, `l` is firm
`i`'s product (`l = none`, the outside option, included), then in any equilibrium of that segment's
third-period game `π_i^{kl} = 0`. -/
theorem solution (G : ThreePeriod) (o2 : Fin 4 → Fin 4 → Offer)
    (o3 : Fin 4 → (Fin 4 → Offer) → Option (Fin 4) → Fin 4 → Offer) (k : Fin 4) (l : Option (Fin 4))
    (hD : UntriedSubstitutes (ThreePeriod.untried3 k l) (G.demand3 k (o2 k) l))
    (heq : G.IsTermEq k (o2 k) l (o3 k (o2 k) l)) (i : Fin 4) (hk : k ≠ i) (hl : l ≠ some i) :
    G.piKL o2 o3 i k l = 0 := by
      unfold ThreePeriod.piKL
      unfold ThreePeriod.IsTermEq ImbalPricing.IsPureNash at heq
      obtain ⟨-, heq⟩ := heq
      unfold ThreePeriod.termProfit at heq ⊢
      set d := G.demand3 k (o2 k) l with hd
      set o := o3 k (o2 k) l with ho
      set U := ThreePeriod.untried3 k l with hU
      have hdev : ∀ j (a : Offer), margin G.c a * d (Function.update o j a) (some j)
          ≤ margin G.c (o j) * d o (some j) := by
        intro j a
        have := heq j a (Set.mem_univ _)
        simpa using this
      have hge : 0 ≤ margin G.c (o i) * d o (some i) := by
        have := hdev i none
        simpa [margin] using this
      have hiU : i ∈ U := by
        simp [hU, ThreePeriod.untried3]; exact ⟨fun h => hk h.symm, fun h => hl h⟩
      have hex : ∃ j, j ≠ k ∧ l ≠ some j ∧ j ≠ i := by
        clear hdev hge hiU heq hD hd ho hU
        revert hk hl; revert i l k; decide
      obtain ⟨j, hjk, hjl, hji⟩ := hex
      have hjU : j ∈ U := by
        simp [hU, ThreePeriod.untried3]; exact ⟨hjk, hjl⟩
      refine le_antisymm ?_ hge
      by_contra hpos
      push Not at hpos
      cases hoi : o i with
      | none => rw [hoi] at hpos; simp [margin] at hpos
      | some q =>
        rw [hoi] at hpos
        simp only [margin] at hpos
        have hDi0 : 0 ≤ d o (some i) := hD.nonneg _ _
        have hqc : 0 < q - G.c := by
          by_contra h; push Not at h; nlinarith
        have hDi : 0 < d o (some i) := by
          by_contra h; push Not at h; nlinarith
        -- q is the minimum untried price
        have hmin : ∀ j' ∈ U, j' ≠ i → ∀ q', o j' = some q' → q ≤ q' := by
          intro j' hj' _ q' hq'
          by_contra h; push Not at h
          have := hD.cheapest_only o i j' q q' hiU hj' hoi hq' h
          linarith
        set p := (G.c + 3 * q) / 4 with hp
        have hpq : p < q := by rw [hp]; linarith
        have hpc : 0 < p - G.c := by rw [hp]; linarith
        set S := ∑ j' ∈ U, d o (some j') with hS
        have hSij : d o (some i) + d o (some j) ≤ S := by
          have hsub : ({i, j} : Finset (Fin 4)) ⊆ U := by
            intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
          have := Finset.sum_le_sum_of_subset_of_nonneg hsub
            (f := fun j' => d o (some j')) (fun x _ _ => hD.nonneg _ _)
          rw [Finset.sum_pair (Ne.symm hji)] at this
          exact this
        have hDj0 : 0 ≤ d o (some j) := hD.nonneg _ _
        -- deviation of i
        have hdi : (p - G.c) * S ≤ (q - G.c) * d o (some i) := by
          have hu := hD.undercut o i p hiU
            (fun j' hj' hne q' hq' => lt_of_lt_of_le hpq (hmin j' hj' hne q' hq'))
            (fun q' hq' => by rw [hoi] at hq'; cases hq'; exact hpq.le)
          have h2 := hdev i (some p)
          rw [hoi] at h2
          simp only [margin] at h2
          nlinarith
        -- bound on j's profit
        have hj : margin G.c (o j) * d o (some j) ≤ (q - G.c) * d o (some j) := by
          cases hoj : o j with
          | none => simp [margin, hD.no_sale o j hoj]
          | some qj =>
            simp only [margin]
            have hqj := hmin j hjU hji qj hoj
            rcases eq_or_lt_of_le hqj with h | h
            · rw [h]
            · have := hD.cheapest_only o j i qj q hjU hiU hoj hoi h
              rw [this]; simp
        have hdj : (p - G.c) * S ≤ margin G.c (o j) * d o (some j) := by
          have hu := hD.undercut o j p hjU
            (fun j' hj' hne q' hq' => by
              by_cases hji' : j' = i
              · subst hji'; rw [hoi] at hq'; cases hq'; exact hpq
              · exact lt_of_lt_of_le hpq (hmin j' hj' hji' q' hq'))
            (fun q' hq' => le_of_lt (lt_of_lt_of_le hpq (hmin j hjU hji q' hq')))
          have h2 := hdev j (some p)
          change (p - G.c) * _ ≤ margin G.c (o j) * _ at h2
          nlinarith
        have hp2 : 2 * (p - G.c) = (3/2) * (q - G.c) := by rw [hp]; ring
        nlinarith
