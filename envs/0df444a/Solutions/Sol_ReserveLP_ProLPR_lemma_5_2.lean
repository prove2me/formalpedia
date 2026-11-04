-- Prove2me | solution 1 for ReserveLP.ProLPR.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T09:09:47.791797+00:00
-- url     : https://prove2.me/submissions/f8692299-0ce8-417a-833d-14e33acb7073

import Mathlib
import Definitions.Def_ReserveLP_ProLPR_Model

open ReserveLP.ProLPR Finset

section
variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]

theorem rlp52_mem_valid (D : DataSet A B) (a : A) (p : Profile B) :
    p ∈ validProfiles D a ↔ (p.2.2.1 ∈ reserves D ∧ p.2.2.2 ∈ reserves D) ∧ p.1 ≠ p.2.1 ∧
      D.bid a p.2.1 ≤ D.bid a p.1 ∧ p.2.2.1 ≤ D.bid a p.1 ∧ p.2.2.2 ≤ D.bid a p.2.1 := by
  simp [validProfiles, mem_filter, mem_product]

theorem rlp52_min_le (D : DataSet A B) (a : A) (b b' : B) (h : b ≠ b') :
    min (D.bid a b) (D.bid a b') ≤ secondBid D a := by
  unfold secondBid
  exact le_sup' (fun bb : B × B => min (D.bid a bb.1) (D.bid a bb.2))
    (show (b, b') ∈ (univ.offDiag : Finset (B × B)) by simp [h])

theorem rlp52_marginal (D : DataSet A B) (q : B → ℝ → ℝ) (bs : B) (R' : Finset ℝ)
    (hq1 : ∀ b, ∑ r ∈ reserves D, q b r = 1) :
    ∑ ρ ∈ roundings D, roundProb q ρ * (if ρ bs ∈ R' then 1 else 0) =
      ∑ x ∈ reserves D, q bs x * (if x ∈ R' then 1 else 0) := by
  let f : B → ℝ → ℝ := fun b x => q b x * (if b = bs then (if x ∈ R' then 1 else 0) else 1)
  have h1 : ∀ ρ : B → ℝ, roundProb q ρ * (if ρ bs ∈ R' then 1 else 0) = ∏ b, f b (ρ b) := by
    intro ρ
    simp only [f, roundProb, prod_mul_distrib]
    congr 1
    rw [prod_ite_eq' univ bs (fun b => if ρ b ∈ R' then (1:ℝ) else 0)]
    simp
  simp only [h1]
  unfold roundings
  rw [← Finset.prod_univ_sum]
  have h2 : ∀ b, ∑ x ∈ reserves D, f b x =
      if b = bs then ∑ x ∈ reserves D, q bs x * (if x ∈ R' then 1 else 0) else 1 := by
    intro b
    by_cases hb : b = bs
    · subst hb; simp [f]
    · simp [f, hb, hq1 b]
  simp only [h2]
  rw [prod_ite_eq' univ bs (fun _ => ∑ x ∈ reserves D, q bs x * (if x ∈ R' then 1 else 0))]
  simp

end

theorem solution {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (D : DataSet A B)
    (s : A → Profile B → ℝ) (q : B → ℝ → ℝ) (hopt : LPOptimal D s q) :
    ∀ a : A, ∀ t : ℝ, secondBid D a < t →
      profileMassGe D s a t - probRevGe D q a t ≤ 0 := by
  classical
  intro a t ht
  obtain ⟨⟨hs0, _, hQ, hq1, hq0⟩, _⟩ := hopt
  have hπ0 : ∀ ρ ∈ roundings D, 0 ≤ roundProb q ρ := by
    intro ρ hρ
    exact prod_nonneg fun b _ => hq0 b _ (Fintype.mem_piFinset.mp hρ b)
  have hprob0 : 0 ≤ probRevGe D q a t := by
    unfold probRevGe
    exact sum_nonneg fun ρ hρ => mul_nonneg (hπ0 ρ hρ) (by split_ifs <;> norm_num)
  set F := (validProfiles D a).filter (fun p => t ≤ revProfile D a p) with hF
  -- structure of profiles in F
  have hFp : ∀ p ∈ F, p ∈ validProfiles D a ∧ t ≤ p.2.2.1 ∧ secondBid D a < D.bid a p.1 := by
    intro p hp
    obtain ⟨hpv, hpt⟩ := mem_filter.mp hp
    obtain ⟨_, hne, h12, hr1, _⟩ := (rlp52_mem_valid D a p).mp hpv
    have hb2 : D.bid a p.2.1 ≤ secondBid D a := by
      have := rlp52_min_le D a p.1 p.2.1 hne
      rwa [min_eq_right h12] at this
    have hr1t : t ≤ p.2.2.1 := by
      unfold revProfile at hpt
      rcases le_max_iff.mp hpt with h | h
      · linarith
      · exact h
    exact ⟨hpv, hr1t, by linarith⟩
  by_cases hFne : F.Nonempty
  swap
  · have : profileMassGe D s a t = 0 := by
      unfold profileMassGe; rw [← hF, not_nonempty_iff_eq_empty.mp hFne, sum_empty]
    linarith
  obtain ⟨p0, hp0⟩ := hFne
  set bs := p0.1
  have hbs : secondBid D a < D.bid a bs := (hFp p0 hp0).2.2
  have honly : ∀ b, b ≠ bs → D.bid a b ≤ secondBid D a := by
    intro b hb
    by_contra hcon
    push_neg at hcon
    have := rlp52_min_le D a b bs hb
    rcases le_total (D.bid a b) (D.bid a bs) with h | h
    · rw [min_eq_left h] at this; linarith
    · rw [min_eq_right h] at this; linarith
  have hF1 : ∀ p ∈ F, p.1 = bs := by
    intro p hp
    by_contra hne
    have h1 := honly p.1 hne
    obtain ⟨_, _, h3⟩ := hFp p hp
    linarith
  set R' := (reserves D).filter (fun x => t ≤ x ∧ x ≤ D.bid a bs) with hR'
  -- upper bound on the mass
  have hmass : profileMassGe D s a t ≤ ∑ x ∈ R', q bs x := by
    unfold profileMassGe
    rw [← hF]
    have hmaps : ∀ p ∈ F, p.2.2.1 ∈ R' := by
      intro p hp
      obtain ⟨hpv, hr1t, _⟩ := hFp p hp
      obtain ⟨⟨hr1R, _⟩, _, _, hr1b, _⟩ := (rlp52_mem_valid D a p).mp hpv
      rw [hF1 p hp] at hr1b
      exact mem_filter.mpr ⟨hr1R, hr1t, hr1b⟩
    rw [← sum_fiberwise_of_maps_to hmaps]
    apply sum_le_sum
    intro x hx
    refine le_trans ?_ (hQ a bs x (mem_filter.mp hx).1)
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpF, hpx⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨(hFp p hpF).1, Or.inr ⟨hF1 p hpF, hpx⟩⟩
    · intro p hp _
      exact hs0 a p (mem_filter.mp hp).1
  -- lower bound on the probability
  have hprob : ∑ x ∈ R', q bs x ≤ probRevGe D q a t := by
    have e : ∑ x ∈ R', q bs x = ∑ x ∈ reserves D, q bs x * (if x ∈ R' then 1 else 0) := by
      rw [hR', sum_filter]
      refine sum_congr rfl fun x hx => ?_
      simp [hx]
    rw [e, ← rlp52_marginal D q bs R' hq1]
    unfold probRevGe
    apply sum_le_sum
    intro ρ hρ
    apply mul_le_mul_of_nonneg_left _ (hπ0 ρ hρ)
    split_ifs with h1 h2 <;> try norm_num
    exfalso; apply h2
    obtain ⟨_, htx, hxb⟩ := mem_filter.mp h1
    have hcl : bs ∈ cleared D a ρ := by simp [cleared, hxb]
    have htop : bs ∈ topBidders D a ρ := by
      simp only [topBidders, mem_filter]
      refine ⟨hcl, fun b _ => ?_⟩
      by_cases hb : b = bs
      · rw [hb]
      · linarith [honly b hb]
    unfold revA
    rw [dif_pos ⟨bs, htop⟩]
    exact le_trans htx (le_trans (le_max_left _ _)
      (le_sup' (fun w => max (ρ w) (otherMax D a ρ w)) htop))
  linarith
