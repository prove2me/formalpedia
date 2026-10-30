-- Prove2me | solution 1 for SubscriptionPlanning.GrandOptimal.mechanism_1_revenue
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T02:39:34.329794+00:00
-- url     : https://prove2.me/submissions/f20950ee-62ed-40a0-b052-8163c26500af

import Mathlib
import Definitions.Def_SubscriptionPlanning_GrandOptimal_Setting
import Theorems.Thm_SubscriptionPlanning_GrandOptimal_lemma_2

open MeasureTheory SubscriptionPlanning.GrandOptimal

namespace SubPlanMech1Aux

variable {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem util_mono (M : Model n m Ω) (i : Fin n) {S S' : Finset (Fin m)} (h : S ⊆ S')
    (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) (ω : Ω) (o : WithBot (Fin m)) :
    util M i S r ω o ≤ util M i S' r ω o := by
  induction o using WithBot.recBotCoe with
  | bot => simp [util]
  | coe j =>
    simp only [util, WithBot.recBotCoe_coe]
    by_cases hj : j ∈ S
    · simp [hj, h hj]
    · rw [if_neg hj]
      split_ifs
      · linarith [hr j]
      · exact le_rfl

theorem best_mono (M : Model n m Ω) (i : Fin n) {S S' : Finset (Fin m)} (h : S ⊆ S')
    (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) (ω : Ω) :
    best M i S r ω ≤ best M i S' r ω := by
  unfold best
  refine Finset.sup'_le _ _ (fun o _ => ?_)
  exact le_trans (util_mono M i h r hr ω o) (Finset.le_sup' _ (Finset.mem_univ o))

theorem best_integrable (M : Model n m Ω) (hM : M.Valid) (i : Fin n) (S : Finset (Fin m))
    (r : Fin m → ℝ) : Integrable (fun ω => best M i S r ω) M.P := by
  have := hM.isProb
  have heq : (fun ω => best M i S r ω) =
      Finset.univ.sup' Finset.univ_nonempty (fun o => fun ω => util M i S r ω o) := by
    funext ω
    simp [best, Finset.sup'_apply]
  rw [heq]
  refine Finset.sup'_induction _ _ (p := fun f => Integrable f M.P) ?_ ?_
  · intro a ha b hb
    exact ha.sup hb
  · intro o _
    induction o using WithBot.recBotCoe with
    | bot => simpa [util] using hM.intV0
    | coe j =>
      by_cases hj : j ∈ S
      · simpa [util, hj] using hM.intV i j
      · have := (hM.intV i j).sub (integrable_const (r j))
        simp only [util, WithBot.recBotCoe_coe, hj, if_false]
        exact this

theorem subGain_nonneg (M : Model n m Ω) (hM : M.Valid) (i : Fin n) (S : Finset (Fin m))
    (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) : 0 ≤ subGain M i S r := by
  unfold subGain
  have := integral_mono (best_integrable M hM i ∅ r) (best_integrable M hM i S r)
    (fun ω => best_mono M i (Finset.empty_subset S) r hr ω)
  linarith

theorem subGain_le (M : Model n m Ω) (hM : M.Valid) (i : Fin n) (S : Finset (Fin m))
    (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) : subGain M i S r ≤ subGain M i Finset.univ r := by
  unfold subGain
  have := integral_mono (best_integrable M hM i S r) (best_integrable M hM i Finset.univ r)
    (fun ω => best_mono M i (Finset.subset_univ S) r hr ω)
  linarith

theorem rent_nonneg (M : Model n m Ω) (i : Fin n) (S : Finset (Fin m)) (r : Fin m → ℝ)
    (hr : ∀ j, 0 ≤ r j) : 0 ≤ rent M i S r := by
  unfold rent
  refine integral_nonneg (fun ω => ?_)
  unfold rentPaid
  refine Finset.sum_nonneg (fun j _ => ?_)
  split_ifs
  · exact hr j
  · exact le_rfl

theorem subGain_empty (M : Model n m Ω) (i : Fin n) (r : Fin m → ℝ) : subGain M i ∅ r = 0 := by
  unfold subGain; ring

end SubPlanMech1Aux

open SubPlanMech1Aux in
theorem solution {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : SubscriptionPlanning.GrandOptimal.Model n m Ω)
    (hM : M.Valid) (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) (hC : SubscriptionPlanning.GrandOptimal.Condition2 M r)
    (p : Finset (Fin m) → ℝ) (S : Fin n → Finset (Fin m)) (hF : SubscriptionPlanning.GrandOptimal.IsFeasible M r p S)
    (hsortA : Monotone (fun k : Fin n => M.lam k * SubscriptionPlanning.GrandOptimal.subGain M k Finset.univ r))
    (hsortG : Monotone (fun k : Fin n => SubscriptionPlanning.GrandOptimal.relGain M k (S k) r)) :
    SubscriptionPlanning.GrandOptimal.revenue M r p S ≤
      ∑ k, SubscriptionPlanning.GrandOptimal.lotteryWeight M r S k *
          SubscriptionPlanning.GrandOptimal.grandRevenue M r (SubscriptionPlanning.GrandOptimal.grandFee M r k)
            (fun i => decide (SubscriptionPlanning.GrandOptimal.grandFee M r k ≤
              SubscriptionPlanning.GrandOptimal.grandFee M r i)) +
        (1 - ∑ k, SubscriptionPlanning.GrandOptimal.lotteryWeight M r S k) *
          ∑ i, M.q i * (M.lam i * M.T * SubscriptionPlanning.GrandOptimal.rent M i ∅ r) := by
  set A : Fin n → ℝ := fun i => M.lam i * M.T * subGain M i Finset.univ r with hA
  set B : Fin n → ℝ := fun i => M.lam i * M.T * rent M i ∅ r with hBdef
  have hlT : ∀ i, 0 < M.lam i * M.T := fun i => mul_pos (hM.lam_pos i) hM.T_pos
  have hG0 : ∀ i, 0 ≤ subGain M i Finset.univ r := fun i => subGain_nonneg M hM i _ r hr
  have hs0 : ∀ i S, 0 ≤ subGain M i S r := fun i S => subGain_nonneg M hM i S r hr
  have hsG : ∀ i S, subGain M i S r ≤ subGain M i Finset.univ r := fun i S => subGain_le M hM i S r hr
  have hR0 : ∀ i S, 0 ≤ rent M i S r := fun i S => rent_nonneg M i S r hr
  have hL2 : ∀ i S, subGain M i S r + rent M i S r ≤ subGain M i Finset.univ r := fun i S =>
    SubscriptionPlanning.GrandOptimal.lemma_2 M hM r hr i S
  have hBA : ∀ i, B i ≤ A i := by
    intro i
    have h := hL2 i ∅
    rw [subGain_empty, zero_add] at h
    exact mul_le_mul_of_nonneg_left h (hlT i).le
  have hq := hM.q_nonneg
  have hAmono : Monotone A := by
    intro a b hab
    have := hsortA hab
    have hT := hM.T_pos
    simp only [hA]
    have e1 : M.lam a * M.T * subGain M a Finset.univ r = (M.lam a * subGain M a Finset.univ r) * M.T := by ring
    have e2 : M.lam b * M.T * subGain M b Finset.univ r = (M.lam b * subGain M b Finset.univ r) * M.T := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right this hT.le
  set x : Fin n → ℝ := fun i => relGain M i (S i) r with hx
  set pp : Fin n → ℝ := fun i => p (S i) with hpp
  have hAx : ∀ i, A i * x i = M.lam i * M.T * subGain M i (S i) r := by
    intro i
    simp only [hA, hx, relGain]
    rcases (hG0 i).lt_or_eq with hpos | hzero
    · have hne := hpos.ne'
      field_simp
    · have : subGain M i (S i) r = 0 := le_antisymm (by rw [hzero]; exact hsG i _) (hs0 i _)
      rw [this, ← hzero]; simp
  have hAxj : ∀ i j, A i * x j ≤ M.lam i * M.T * subGain M i (S j) r := by
    intro i j
    simp only [hA, hx, relGain]
    rcases (hG0 j).lt_or_eq with hpos | hzero
    · have hc := hC.2 i j (S j)
      have : subGain M i Finset.univ r * (subGain M j (S j) r / subGain M j Finset.univ r) = subGain M i (S j) r := by
        rw [mul_div_assoc', div_eq_iff hpos.ne']
        linarith
      rw [mul_assoc, this]
    · have h0 : subGain M j Finset.univ r = 0 := by simpa using hzero.symm
      rw [h0, div_zero, mul_zero]
      exact mul_nonneg (hlT i).le (hs0 i _)
  have hIC : ∀ i j, A i * x j - pp j ≤ A i * x i - pp i := by
    intro i j
    have h1 := hF.2 i (S j)
    have h2 := hAxj i j
    have h3 := hAx i
    simp only [hpp]
    linarith
  have hIR : ∀ i, pp i ≤ A i * x i := by
    intro i
    have h1 := hF.2 i ∅
    rw [subGain_empty, hF.1, mul_zero, sub_zero] at h1
    rw [hAx i]
    simp only [hpp]
    linarith
  have hrent : ∀ i, M.lam i * M.T * rent M i (S i) r ≤ (1 - x i) * B i := by
    intro i
    show _ ≤ (1 - x i) * (M.lam i * M.T * rent M i ∅ r)
    rcases (hG0 i).lt_or_eq with hpos | hzero
    · have hc := hC.1 i (S i)
      have : rent M i (S i) r ≤ (1 - x i) * rent M i ∅ r := by
        have key : x i * rent M i ∅ r ≤ rent M i ∅ r - rent M i (S i) r := by
          simp only [hx, relGain]
          rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
          linarith
        linarith
      calc M.lam i * M.T * rent M i (S i) r ≤ M.lam i * M.T * ((1 - x i) * rent M i ∅ r) :=
            mul_le_mul_of_nonneg_left this (hlT i).le
        _ = (1 - x i) * (M.lam i * M.T * rent M i ∅ r) := by ring
    · have hxi : x i = 0 := by
        simp only [hx, relGain]
        rw [← hzero, div_zero]
      rw [hxi, sub_zero, one_mul]
      have h := hL2 i (S i)
      rw [← hzero] at h
      have h' : rent M i (S i) r ≤ rent M i ∅ r := by linarith [hs0 i (S i), hR0 i ∅]
      exact mul_le_mul_of_nonneg_left h' (hlT i).le
  -- lottery weights
  set π : Fin n → ℝ := fun k => lotteryWeight M r S k with hπdef
  have hπ0 : ∀ k, 0 ≤ π k := by
    intro k
    simp only [hπdef, lotteryWeight]
    split_ifs with hk
    · have : (⟨k.val - 1, by omega⟩ : Fin n) ≤ k := by
        rw [Fin.mk_le_mk]; omega
      have := hsortG this
      linarith
    · have := div_nonneg (hs0 k (S k)) (hG0 k)
      simpa [relGain] using this
  have hπsucc : ∀ t (ht : t + 1 < n), π ⟨t + 1, ht⟩ = x ⟨t + 1, ht⟩ - x ⟨t, by omega⟩ := by
    intro t ht
    simp only [hπdef, lotteryWeight, hx]
    rw [dif_pos (by simp)]
    rfl
  have hπzero : ∀ (h0 : 0 < n), π ⟨0, h0⟩ = x ⟨0, h0⟩ := by
    intro h0
    simp only [hπdef, lotteryWeight, hx]
    rw [dif_neg (by simp), sub_zero]
  -- telescoping bound on fees
  have htel : ∀ t (ht : t < n) (b : ℝ), pp ⟨t, ht⟩ - x ⟨t, ht⟩ * b ≤
      ∑ k : Fin n, (if k.val ≤ t then π k * (A k - b) else 0) := by
    intro t
    induction t with
    | zero =>
      intro ht b
      rw [Finset.sum_eq_single ⟨0, ht⟩]
      · rw [if_pos le_rfl, hπzero ht]
        have := hIR ⟨0, ht⟩
        nlinarith
      · intro k _ hk
        rw [if_neg]
        intro hk0
        exact hk (Fin.ext (by simp; omega))
      · intro h; exact absurd (Finset.mem_univ _) h
    | succ t ih =>
      intro ht b
      have ih' := ih (by omega) b
      have hsplit : ∑ k : Fin n, (if k.val ≤ t + 1 then π k * (A k - b) else 0) =
          (∑ k : Fin n, (if k.val ≤ t then π k * (A k - b) else 0)) +
            π ⟨t + 1, ht⟩ * (A ⟨t + 1, ht⟩ - b) := by
        have e : ∀ k : Fin n, (if k.val ≤ t + 1 then π k * (A k - b) else 0) =
            (if k.val ≤ t then π k * (A k - b) else 0) +
              (if k = ⟨t + 1, ht⟩ then π k * (A k - b) else 0) := by
          intro k
          by_cases h1 : k.val ≤ t
          · have h2 : k.val ≤ t + 1 := by omega
            have h3 : k ≠ ⟨t + 1, ht⟩ := by intro h; rw [h] at h1; simp at h1
            rw [if_pos h2, if_pos h1, if_neg h3, add_zero]
          · by_cases h2 : k.val ≤ t + 1
            · have h3 : k = ⟨t + 1, ht⟩ := Fin.ext (by simp; omega)
              rw [if_pos h2, if_neg h1, if_pos h3, zero_add, h3]
            · have h3 : k ≠ ⟨t + 1, ht⟩ := by intro h; rw [h] at h2; simp at h2
              rw [if_neg h2, if_neg h1, if_neg h3, add_zero]
        rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp
      rw [hsplit, hπsucc t ht]
      have hic := hIC ⟨t + 1, ht⟩ ⟨t, by omega⟩
      have e2 : (x ⟨t + 1, ht⟩ - x ⟨t, by omega⟩) * (A ⟨t + 1, ht⟩ - b) =
          A ⟨t + 1, ht⟩ * x ⟨t + 1, ht⟩ - A ⟨t + 1, ht⟩ * x ⟨t, by omega⟩ -
            x ⟨t + 1, ht⟩ * b + x ⟨t, by omega⟩ * b := by ring
      linarith
  -- per-type bound
  set f : Fin n → ℝ := fun k => ∑ i, M.q i * (if A k ≤ A i then A k - B i else 0) with hf
  have hper : ∀ i, pp i - x i * B i ≤ ∑ k, π k * (if A k ≤ A i then A k - B i else 0) := by
    intro i
    refine le_trans (htel i.val i.isLt (B i)) (Finset.sum_le_sum (fun k _ => ?_))
    by_cases hk : k.val ≤ i.val
    · have hAk : A k ≤ A i := hAmono (Fin.mk_le_mk.mpr hk)
      rw [if_pos hk, if_pos hAk]
    · rw [if_neg hk]
      split_ifs with h
      · have hAk : A i ≤ A k := hAmono (Fin.mk_le_mk.mpr (by omega))
        have : A k = A i := le_antisymm h hAk
        exact mul_nonneg (hπ0 k) (by rw [this]; linarith [hBA i])
      · simp
  have hsum : ∑ i, M.q i * (pp i - x i * B i) ≤ ∑ k, π k * f k := by
    calc ∑ i, M.q i * (pp i - x i * B i)
        ≤ ∑ i, M.q i * ∑ k, π k * (if A k ≤ A i then A k - B i else 0) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hper i) (hq i))
      _ = ∑ k, π k * f k := by
          simp only [hf, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => ?_))
          ring
  have hrev : revenue M r p S ≤ ∑ i, M.q i * B i + ∑ i, M.q i * (pp i - x i * B i) := by
    unfold revenue
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have := mul_le_mul_of_nonneg_left (hrent i) (hq i)
    simp only [hpp]
    nlinarith
  have hgrand : ∀ k, ∑ i, M.q i * B i + f k ≤
      grandRevenue M r (grandFee M r k) (fun i => decide (grandFee M r k ≤ grandFee M r i)) := by
    intro k
    show _ ≤ grandRevenue M r (A k) (fun i => decide (A k ≤ A i))
    unfold grandRevenue
    simp only [hf]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun i _ => ?_)
    by_cases h : A k ≤ A i
    · rw [if_pos h]
      simp only [h, decide_true, if_true]
      have := mul_nonneg (hlT i).le (hR0 i Finset.univ)
      have := mul_le_mul_of_nonneg_left (show A k ≤ A k + M.lam i * M.T * rent M i Finset.univ r
        by linarith) (hq i)
      nlinarith
    · rw [if_neg h]
      simp only [h, decide_false, Bool.false_eq_true, if_false, mul_zero, add_zero]
      exact le_rfl
  have hfinal : ∑ k, π k * (∑ i, M.q i * B i + f k) ≤
      ∑ k, π k * grandRevenue M r (grandFee M r k) (fun i => decide (grandFee M r k ≤ grandFee M r i)) :=
    Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hgrand k) (hπ0 k))
  have hexp : ∑ k, π k * (∑ i, M.q i * B i + f k) =
      (∑ k, π k) * ∑ i, M.q i * B i + ∑ k, π k * f k := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  show revenue M r p S ≤ ∑ k, π k * grandRevenue M r (grandFee M r k)
      (fun i => decide (grandFee M r k ≤ grandFee M r i)) + (1 - ∑ k, π k) * ∑ i, M.q i * B i
  nlinarith
