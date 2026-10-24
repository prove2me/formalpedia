-- Prove2me | solution 1 for PricingWithTips.buyerMatching_prices_of_maximum
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T23:15:52.957557+00:00
-- url     : https://prove2.me/submissions/1d4bc1e7-b218-4e61-9dbd-48204d52c2bf

import Definitions.Def_PricingWithTips_Model
import Definitions.Def_AssignmentGame_CoreCorners_Game
import Theorems.Thm_PricingWithTips_maximumMatching_max_zero
import Theorems.Thm_AssignmentGame_CoreCorners_core_nonempty
import Theorems.Thm_AssignmentGame_CoreCorners_core_dual_constraints
import Theorems.Thm_AssignmentGame_CoreCorners_core_tight_on_optimal_matching

open PricingWithTips
open AssignmentGame.CoreCorners

variable {B S : Type*} [Fintype B] [Fintype S]
  [DecidableEq B] [DecidableEq S]

private noncomputable def buyerPairs (z : BuyerMatching B S) : Finset (B × S) :=
  Finset.univ.filter (fun bs => z.assigned bs.1 = some bs.2)

private theorem buyerPairs_matching (z : BuyerMatching B S) :
    IsMatching Finset.univ Finset.univ (buyerPairs z) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    simp
  · intro p hp q hq hfirst
    have hp' : z.assigned p.1 = some p.2 := (Finset.mem_filter.mp hp).2
    have hq' : z.assigned q.1 = some q.2 := (Finset.mem_filter.mp hq).2
    have hsecond : p.2 = q.2 := by
      have h : some p.2 = some q.2 := by
        calc
          some p.2 = z.assigned p.1 := hp'.symm
          _ = z.assigned q.1 := by rw [hfirst]
          _ = some q.2 := hq'
      exact Option.some.inj h
    exact Prod.ext hfirst hsecond
  · intro p hp q hq hsecond
    have hp' : z.assigned p.1 = some p.2 := (Finset.mem_filter.mp hp).2
    have hq' : z.assigned q.1 = some q.2 := (Finset.mem_filter.mp hq).2
    have hfirst : p.1 = q.1 := z.store_unique hp' (by simpa [hsecond] using hq')
    exact Prod.ext hfirst hsecond

private theorem buyerPairs_weight (z : BuyerMatching B S) (a : B → S → ℝ) :
    (∑ bs ∈ buyerPairs z, a bs.1 bs.2) = matchingWeight z a := by
  classical
  simp only [buyerPairs, Finset.sum_filter, matchingWeight]
  rw [← Finset.univ_product_univ]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro b _
  cases h : z.assigned b with
  | none => simp [h]
  | some s => simp [h]

private theorem buyerPairs_surjective
    (Q : Finset (B × S)) (hQ : IsMatching Finset.univ Finset.univ Q) :
    ∃ z : BuyerMatching B S, buyerPairs z = Q := by
  classical
  let z : BuyerMatching B S := {
    assigned := fun b => if h : ∃ s, (b, s) ∈ Q then some (Classical.choose h) else none
    store_unique := by
      intro b₁ b₂ s h₁ h₂
      have he₁ : ∃ s, (b₁, s) ∈ Q := by
        by_contra hn
        simp [hn] at h₁
      have he₂ : ∃ s, (b₂, s) ∈ Q := by
        by_contra hn
        simp [hn] at h₂
      have hc₁ : (b₁, Classical.choose he₁) ∈ Q := Classical.choose_spec he₁
      have hc₂ : (b₂, Classical.choose he₂) ∈ Q := Classical.choose_spec he₂
      have hs₁ : Classical.choose he₁ = s := by
        have h := h₁
        simp only [dif_pos he₁] at h
        exact Option.some.inj h
      have hs₂ : Classical.choose he₂ = s := by
        have h := h₂
        simp only [dif_pos he₂] at h
        exact Option.some.inj h
      have hpair := hQ.2.2 (b₁, s) (by simpa [hs₁] using hc₁)
        (b₂, s) (by simpa [hs₂] using hc₂) rfl
      exact congrArg Prod.fst hpair
  }
  refine ⟨z, ?_⟩
  ext bs
  rcases bs with ⟨b, s⟩
  simp only [buyerPairs, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hassign
    have he : ∃ s, (b, s) ∈ Q := by
      by_contra hn
      simp [z, hn] at hassign
    have hc : (b, Classical.choose he) ∈ Q := Classical.choose_spec he
    have hs : Classical.choose he = s := by
      simp only [z, dif_pos he] at hassign
      exact Option.some.inj hassign
    simpa [hs] using hc
  · intro hmem
    have he : ∃ s, (b, s) ∈ Q := ⟨s, hmem⟩
    have hc : (b, Classical.choose he) ∈ Q := Classical.choose_spec he
    have hp := hQ.2.1 (b, Classical.choose he) hc (b, s) hmem rfl
    have hs : Classical.choose he = s := congrArg Prod.snd hp
    simp [z, he, hs]

private theorem maximumMatching_optimal_pairs
    (z : BuyerMatching B S) (a : B → S → ℝ)
    (hmax : IsMaximumWeight z a) :
    (∑ bs ∈ buyerPairs z, a bs.1 bs.2) =
      worth a Finset.univ Finset.univ := by
  classical
  let P := buyerPairs z
  have hP : IsMatching Finset.univ Finset.univ P := buyerPairs_matching z
  have hPmem : P ∈ matchings (Finset.univ : Finset B) (Finset.univ : Finset S) := by
    simp [matchings, hP, P]
  apply le_antisymm
  · unfold worth
    exact Finset.le_sup' (fun Q : Finset (B × S) => ∑ bs ∈ Q, a bs.1 bs.2) hPmem
  · unfold worth
    apply Finset.sup'_le
    intro Q hQmem
    have hQ : IsMatching (Finset.univ : Finset B) (Finset.univ : Finset S) Q := by
      simpa [matchings] using hQmem
    obtain ⟨zQ, hzQ⟩ := buyerPairs_surjective Q hQ
    rw [← hzQ, buyerPairs_weight, buyerPairs_weight]
    exact hmax zQ

private theorem maximumMatching_matched_nonnegative
    (z : BuyerMatching B S) (q : B → S → ℝ)
    (hmax : IsMaximumWeight z q)
    {b : B} {s : S} (hmatch : z.assigned b = some s) :
    0 ≤ q b s := by
  classical
  let z' : BuyerMatching B S := {
    assigned := fun b' => if b' = b then none else z.assigned b'
    store_unique := by
      intro b₁ b₂ s' h₁ h₂
      by_cases hb₁ : b₁ = b
      · simp [hb₁] at h₁
      · by_cases hb₂ : b₂ = b
        · simp [hb₂] at h₂
        · exact z.store_unique (by simpa [hb₁] using h₁) (by simpa [hb₂] using h₂)
  }
  let f : B → ℝ := fun x => match z.assigned x with | none => 0 | some s' => q x s'
  let g : B → ℝ := fun x => match z'.assigned x with | none => 0 | some s' => q x s'
  have hpoint : ∀ x, f x = g x + if x = b then q b s else 0 := by
    intro x
    by_cases hx : x = b
    · subst x
      simp [f, g, z', hmatch]
    · simp only [f, g, z', if_neg hx]
      simp
  have hweight : matchingWeight z q = matchingWeight z' q + q b s := by
    change (∑ x, f x) = (∑ x, g x) + q b s
    calc
      (∑ x, f x) = ∑ x, (g x + if x = b then q b s else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        exact hpoint x
      _ = (∑ x, g x) + q b s := by simp [Finset.sum_add_distrib]
  have hle := hmax z'
  rw [hweight] at hle
  linarith

theorem solution
    (z : BuyerMatching B S) (q : B → S → ℝ)
    (hmax : IsMaximumWeight z q) :
    ∃ p : S → ℝ,
      (∀ s, 0 ≤ p s) ∧
      (∀ b,
        match z.assigned b with
        | none => ∀ s, q b s - p s ≤ 0
        | some s => 0 ≤ q b s - p s ∧
            ∀ s', q b s' - p s' ≤ q b s - p s) ∧
      (∀ s, (¬ ∃ b, z.assigned b = some s) → p s = 0) := by
  classical
  let a : B → S → ℝ := fun b s => max 0 (q b s)
  have ha : ∀ b s, 0 ≤ a b s := by
    intro b s
    exact le_max_left _ _
  have hmaxa : IsMaximumWeight z a := maximumMatching_max_zero z q hmax
  let P := buyerPairs z
  have hP : IsMatching Finset.univ Finset.univ P := buyerPairs_matching z
  have hopt : (∑ bs ∈ P, a bs.1 bs.2) = worth a Finset.univ Finset.univ :=
    maximumMatching_optimal_pairs z a hmaxa
  obtain ⟨⟨u, v⟩, hcore⟩ := core_nonempty a ha
  obtain ⟨hu, hv, hdual⟩ := core_dual_constraints a u v hcore
  obtain ⟨htight, hunmatched, hunsold⟩ :=
    core_tight_on_optimal_matching a ha P hP hopt u v hcore
  refine ⟨v, hv, ?_, ?_⟩
  · intro b
    cases h : z.assigned b with
    | none =>
        simp only [h]
        intro s
        have hu0 : u b = 0 := by
          apply hunmatched b
          intro pair hp hfirst
          have hp' : z.assigned pair.1 = some pair.2 := (Finset.mem_filter.mp hp).2
          simp only [P, buyerPairs] at hp
          rw [hfirst] at hp'
          simp [h] at hp'
        have hd := hdual b s
        have hq : q b s ≤ a b s := le_max_right _ _
        linarith
    | some s₀ =>
        simp only [h]
        have hmem : (b, s₀) ∈ P := by simp [P, buyerPairs, h]
        have hqnonneg : 0 ≤ q b s₀ := maximumMatching_matched_nonnegative z q hmax h
        have haeq : a b s₀ = q b s₀ := max_eq_right hqnonneg
        have hqeq : u b + v s₀ = q b s₀ := by
          simpa [a, haeq] using htight (b, s₀) hmem
        constructor
        · linarith [hu b]
        · intro s'
          have hd := hdual b s'
          have hq : q b s' ≤ a b s' := le_max_right _ _
          linarith
  · intro s hs
    apply hunsold s
    intro pair hp hsecond
    have hp' : z.assigned pair.1 = some pair.2 := (Finset.mem_filter.mp hp).2
    apply hs
    refine ⟨pair.1, ?_⟩
    simpa [hsecond] using hp'
