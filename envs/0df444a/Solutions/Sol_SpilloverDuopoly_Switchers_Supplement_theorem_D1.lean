-- Prove2me | solution 1 for SpilloverDuopoly.Switchers.Supplement.theorem_D1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:21:03.322551+00:00
-- url     : https://prove2.me/submissions/9e8f87ff-8357-48b0-9306-2fb87ca0420d

import Mathlib
import Definitions.Def_SpilloverDuopoly_Switchers_Supplement_TwoPeriodNFirm

open SpilloverDuopoly
open SpilloverDuopoly.Switchers
open SpilloverDuopoly.Switchers.Supplement

/-- Theorem D.1 (p. 51 (PDF 53)): with `N > 2` firms and two periods, for any second-period
equilibrium in which every firm earns the same repeat profit `π^{R∗}` per unit of its own
first-period share, and any admissible tie shares, a common first-period price `p` at which
consumers buy is a symmetric equilibrium iff `p = c - δ π^{R∗}`, and then every firm's profit in
the two-stage game is zero. -/
theorem solution {N : ℕ} (hN : 2 < N) (G : TwoPeriodNFirm N) (hG : G.Standing)
    (o2 : Fin N → Fin N → Offer) (ho2 : G.IsSecondEq o2) (piR : ℝ)
    (hR : ∀ k, G.piK o2 k k = piR) (p : ℝ) (hcov : G.u0 ≤ G.V - p) :
    (G.IsSymEq o2 p ↔ p = G.c - G.delta * piR) ∧
    (G.IsSymEq o2 p → ∀ i, G.profit o2 (fun _ => p) i = 0) := by
      obtain ⟨⟨hc, hd0, hd1, htie, htie1⟩, hsub⟩ := hG
      have hother : ∀ k : Fin N, ∀ j : Fin N, ∃ j' : Fin N, j' ≠ k ∧ j' ≠ j := by
        intro k j
        have h : ∃ x, x ∉ ({k, j} : Finset (Fin N)) := by
          by_contra hcon
          push Not at hcon
          have h1 : (Finset.univ : Finset (Fin N)) ⊆ {k, j} := fun x _ => hcon x
          have h2 := Finset.card_le_card h1
          have h3 : ({k, j} : Finset (Fin N)).card ≤ 2 := Finset.card_le_two
          simp at h2
          omega
        obtain ⟨x, hx⟩ := h
        simp at hx
        exact ⟨x, hx.1, hx.2⟩
      -- switchers earn nothing
      have hzero : ∀ k j : Fin N, j ≠ k → G.piK o2 k j = 0 := by
        intro k j hjk
        obtain ⟨-, hne⟩ := ho2 k
        have hU := hsub k
        have hnn : 0 ≤ G.piK o2 k j := by
          have h := hne j none (Set.mem_univ _)
          simpa [TwoPeriodNFirm.segProfit, TwoPeriodNFirm.piK, margin] using h
        by_contra hcon
        have hpos : 0 < G.piK o2 k j := lt_of_le_of_ne hnn (Ne.symm hcon)
        clear hcon hnn
        have hpos' : 0 < margin G.c (o2 k j) * G.demand2 k (o2 k) (some j) := hpos
        cases hoj : o2 k j with
        | none =>
          rw [hoj] at hpos'
          simp [margin] at hpos'
        | some q =>
          rw [hoj] at hpos'
          simp only [margin] at hpos'
          have hdj : 0 ≤ G.demand2 k (o2 k) (some j) := hU.nonneg _ _
          have hdj' : 0 < G.demand2 k (o2 k) (some j) := by
            rcases hdj.lt_or_eq with h | h
            · exact h
            · rw [← h] at hpos'; simp at hpos'
          have hqc : 0 < q - G.c := by
            by_contra h
            push Not at h
            nlinarith
          obtain ⟨j', hj'k, hj'j⟩ := hother k j
          have hjU : j ∈ Finset.univ.erase k := by simp [hjk]
          have hj'U : j' ∈ Finset.univ.erase k := by simp [hj'k]
          have hlow : ∀ i ∈ Finset.univ.erase k, ∀ q', o2 k i = some q' → q ≤ q' := by
            intro i hi q' hq'
            by_contra h
            push Not at h
            have := hU.cheapest_only (o2 k) j i q q' hjU hi hoj hq' h
            linarith
          have hDge : G.demand2 k (o2 k) (some j) + G.demand2 k (o2 k) (some j') ≤
              ∑ i ∈ Finset.univ.erase k, G.demand2 k (o2 k) (some i) := by
            rw [← Finset.sum_pair (Ne.symm hj'j) (f := fun i => G.demand2 k (o2 k) (some i))]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl
              · exact hjU
              · exact hj'U
            · intro i _ _
              exact hU.nonneg _ _
          obtain ⟨D, hD⟩ : ∃ D, D = ∑ i ∈ Finset.univ.erase k, G.demand2 k (o2 k) (some i) := ⟨_, rfl⟩
          rw [← hD] at hDge
          have hd'nn : 0 ≤ G.demand2 k (o2 k) (some j') := hU.nonneg _ _
          have hdev : ∀ e : ℝ, 0 < e → e < q - G.c →
              (q - e - G.c) * D ≤ margin G.c (o2 k j') * G.demand2 k (o2 k) (some j') := by
            intro e he1 he2
            have h1 := hne j' (some (q - e)) (Set.mem_univ _)
            have h2 := hU.undercut (o2 k) j' (q - e) hj'U
              (fun i hi _ q' hq' => by have := hlow i hi q' hq'; linarith)
              (fun q' hq' => by have := hlow j' hj'U q' hq'; linarith)
            rw [← hD] at h2
            simp only [TwoPeriodNFirm.segProfit, Function.update_self, margin] at h1
            refine le_trans ?_ h1
            exact mul_le_mul_of_nonneg_left h2 (by linarith)
          have hlim : (q - G.c) * D ≤ margin G.c (o2 k j') * G.demand2 k (o2 k) (some j') := by
            by_contra h
            push Not at h
            have hDpos : 0 < D := by linarith
            obtain ⟨g, hg⟩ : ∃ g, g = (q - G.c) * D -
              margin G.c (o2 k j') * G.demand2 k (o2 k) (some j') := ⟨_, rfl⟩
            have hgpos : 0 < g := by linarith
            have he1 : 0 < min ((q - G.c) / 2) (g / (2 * D)) := by positivity
            have he2 : min ((q - G.c) / 2) (g / (2 * D)) < q - G.c :=
              lt_of_le_of_lt (min_le_left _ _) (by linarith)
            have h1 := hdev _ he1 he2
            have h2 : min ((q - G.c) / 2) (g / (2 * D)) * D ≤ g / 2 := by
              calc _ ≤ g / (2 * D) * D := mul_le_mul_of_nonneg_right (min_le_right _ _) hDpos.le
                _ = g / 2 := by field_simp
            nlinarith
          cases hoj' : o2 k j' with
          | none =>
            rw [hoj'] at hlim
            simp only [margin, zero_mul] at hlim
            nlinarith
          | some q' =>
            rw [hoj'] at hlim
            simp only [margin] at hlim
            have hqq := hlow j' hj'U q' hoj'
            rcases hqq.lt_or_eq with h | h
            · have h0 := hU.cheapest_only (o2 k) j' j q' q hj'U hjU hoj' hoj h
              rw [h0] at hlim
              nlinarith
            · subst h
              nlinarith
      have hprofit : ∀ (P : Fin N → ℝ) (i : Fin N),
          G.profit o2 P i = G.share P i * (P i - G.c + G.delta * piR) := by
        intro P i
        unfold TwoPeriodNFirm.profit
        rw [Finset.sum_eq_single i]
        · rw [hR i]; ring
        · intro k _ hk
          rw [hzero k i (Ne.symm hk)]; ring
        · intro h; exact absurd (Finset.mem_univ i) h
      have hbest : G.best (fun _ => p) = Finset.univ := by
        ext j
        simp [FirstPeriod.best, hcov]
      have hshare : ∀ i, G.share (fun _ => p) i = G.tie Finset.univ i := by
        intro i
        simp [FirstPeriod.share, hbest]
      have hNpos : 0 < N := by omega
      have hsum : ∑ j, G.tie Finset.univ j = 1 :=
        htie1 Finset.univ ⟨⟨0, hNpos⟩, Finset.mem_univ _⟩
      have hhigh : ∀ (i : Fin N) (a : ℝ), p < a →
          G.share (Function.update (fun _ => p) i a) i = 0 := by
        intro i a ha
        obtain ⟨j, hj, -⟩ := hother i i
        have : i ∉ G.best (Function.update (fun _ => p) i a) := by
          intro h
          simp only [FirstPeriod.best, Finset.mem_filter] at h
          have h1 := h.2.2 j
          rw [Function.update_self, Function.update_of_ne hj] at h1
          linarith
        simp [FirstPeriod.share, this]
      have hsnn : ∀ P i, 0 ≤ G.share P i := by
        intro P i
        unfold FirstPeriod.share
        split_ifs
        · exact htie _ _
        · exact le_rfl
      have hlow : ∀ (i : Fin N) (a : ℝ), a < p →
          G.share (Function.update (fun _ => p) i a) i = 1 := by
        intro i a ha
        have hb : G.best (Function.update (fun _ => p) i a) = {i} := by
          ext j
          simp only [FirstPeriod.best, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton]
          constructor
          · rintro ⟨-, h⟩
            by_contra hji
            have h1 := h i
            rw [Function.update_self, Function.update_of_ne hji] at h1
            linarith
          · rintro rfl
            refine ⟨by rw [Function.update_self]; linarith, fun j' => ?_⟩
            rw [Function.update_self]
            by_cases hj : j' = j
            · subst hj; rw [Function.update_self]
            · rw [Function.update_of_ne hj]; exact ha.le
        have h1 := htie1 {i} (Finset.singleton_nonempty i)
        rw [Finset.sum_singleton] at h1
        simp [FirstPeriod.share, hb, h1]
      have hiff : G.IsSymEq o2 p ↔ p = G.c - G.delta * piR := by
        constructor
        · rintro ⟨-, hne⟩
          simp only [Set.mem_univ, forall_true_left, hprofit, hshare, Function.update_self] at hne
          rcases lt_trichotomy (p - G.c + G.delta * piR) 0 with hm | hm | hm
          · exfalso
            obtain ⟨i, -, hi⟩ : ∃ i ∈ (Finset.univ : Finset (Fin N)), 0 < G.tie Finset.univ i := by
              apply Finset.exists_lt_of_sum_lt
              rw [hsum]; simp
            have h1 := hne i (p + 1)
            rw [hhigh i (p + 1) (by linarith)] at h1
            nlinarith
          · linarith
          · exfalso
            have hge : ∀ i, 1 ≤ G.tie Finset.univ i := by
              intro i
              by_contra h
              push Not at h
              have hpos : 0 < (1 - G.tie Finset.univ i) * (p - G.c + G.delta * piR) / 2 := by
                have : 0 < 1 - G.tie Finset.univ i := by linarith
                positivity
              have h1 := hne i (p - (1 - G.tie Finset.univ i) * (p - G.c + G.delta * piR) / 2)
              rw [hlow i _ (by linarith)] at h1
              nlinarith
            have h2 : ∑ _j : Fin N, (1:ℝ) ≤ ∑ j, G.tie Finset.univ j :=
              Finset.sum_le_sum (fun i _ => hge i)
            rw [hsum] at h2
            simp at h2
            omega
        · intro hp
          refine ⟨fun i => Set.mem_univ _, fun i a _ => ?_⟩
          simp only [hprofit, Function.update_self]
          have h0 : p - G.c + G.delta * piR = 0 := by linarith
          rw [h0, mul_zero]
          rcases le_or_gt a p with h | h
          · exact mul_nonpos_of_nonneg_of_nonpos (hsnn _ _) (by linarith)
          · rw [hhigh i a h, zero_mul]
      refine ⟨hiff, fun h i => ?_⟩
      have hp := hiff.1 h
      rw [hprofit]
      have h0 : p - G.c + G.delta * piR = 0 := by linarith
      simp only [h0, mul_zero]
