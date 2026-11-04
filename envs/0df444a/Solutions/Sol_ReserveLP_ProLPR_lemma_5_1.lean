-- Prove2me | solution 1 for ReserveLP.ProLPR.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T09:08:26.181199+00:00
-- url     : https://prove2.me/submissions/2d807cef-2ae6-4a60-86a9-26e1d3adae40

import Mathlib
import Definitions.Def_ReserveLP_ProLPR_Model
import Theorems.Thm_ReserveLP_ProLPR_lemma_4_3

open ReserveLP.ProLPR Finset

theorem rlp_ind_ii (x a b : ℝ) : IntervalIntegrable (fun t => if t ≤ x then (1:ℝ) else 0)
    MeasureTheory.volume a b := by
  apply Antitone.intervalIntegrable
  intro a b hab
  show (if b ≤ x then (1:ℝ) else 0) ≤ (if a ≤ x then 1 else 0)
  split_ifs with h1 h2 <;> norm_num
  exact h2 (hab.trans h1)

theorem rlp_sum_ii {ι : Type} (S : Finset ι) (w v : ι → ℝ) (a b : ℝ) :
    IntervalIntegrable (fun t => ∑ i ∈ S, w i * (if t ≤ v i then (1:ℝ) else 0))
      MeasureTheory.volume a b := by
  have h := IntervalIntegrable.sum S (fun i _ => (rlp_ind_ii (v i) a b).const_mul (w i))
  have e : (fun t => ∑ i ∈ S, w i * (if t ≤ v i then (1:ℝ) else 0)) =
      ∑ i ∈ S, fun t => w i * (if t ≤ v i then (1:ℝ) else 0) := by
    funext t; simp only [Finset.sum_apply]
  rw [e]; exact h

theorem rlp_ind_int (x M : ℝ) (hx : 0 ≤ x) (hxM : x ≤ M) :
    ∫ t in (0:ℝ)..M, (if t ≤ x then (1:ℝ) else 0) = x := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := x)
    (rlp_ind_ii x 0 x) (rlp_ind_ii x x M)]
  have h1 : ∫ t in (0:ℝ)..x, (if t ≤ x then (1:ℝ) else 0) = ∫ t in (0:ℝ)..x, (1:ℝ) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le hx] at ht
    simp [ht.2]
  have h2 : ∫ t in x..M, (if t ≤ x then (1:ℝ) else 0) = ∫ t in x..M, (0:ℝ) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le hxM] at ht
    simp [not_le.mpr ht.1]
  rw [h1, h2]; simp

theorem rlp_key {ι κ : Type} (S : Finset ι) (T : Finset κ) (w v : ι → ℝ) (π u : κ → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hv : ∀ i ∈ S, 0 ≤ v i) (hu : ∀ k ∈ T, 0 ≤ u k)
    (β c : ℝ) (hβ : 0 ≤ β)
    (h2 : ∀ t : ℝ, 0 ≤ t → β < t →
      ∑ i ∈ S.filter (fun i => t ≤ v i), w i - ∑ k ∈ T, π k * (if t ≤ u k then 1 else 0) ≤ 0)
    (h3 : ∀ t : ℝ, 0 ≤ t → t ≤ β →
      ∑ i ∈ S.filter (fun i => t ≤ v i), w i - ∑ k ∈ T, π k * (if t ≤ u k then 1 else 0) ≤ c) :
    ∑ i ∈ S, w i * v i - ∑ k ∈ T, π k * u k ≤ c * β := by
  set M := β + ∑ i ∈ S, v i + ∑ k ∈ T, u k with hM
  have hSv : 0 ≤ ∑ i ∈ S, v i := sum_nonneg hv
  have hTu : 0 ≤ ∑ k ∈ T, u k := sum_nonneg hu
  have hvM : ∀ i ∈ S, v i ≤ M := fun i hi => by
    have := single_le_sum hv hi; linarith
  have huM : ∀ k ∈ T, u k ≤ M := fun k hk => by
    have := single_le_sum hu hk; linarith
  have hβM : β ≤ M := by linarith
  let G : ℝ → ℝ := fun t => ∑ i ∈ S, w i * (if t ≤ v i then 1 else 0) -
    ∑ k ∈ T, π k * (if t ≤ u k then 1 else 0)
  have hGeq : ∀ t, G t = ∑ i ∈ S.filter (fun i => t ≤ v i), w i -
      ∑ k ∈ T, π k * (if t ≤ u k then 1 else 0) := by
    intro t; simp only [G, sum_filter, mul_ite, mul_one, mul_zero]
  have hGii : ∀ a b, IntervalIntegrable G MeasureTheory.volume a b := by
    intro a b
    apply IntervalIntegrable.sub
    · exact rlp_sum_ii S w v a b
    · exact rlp_sum_ii T π u a b
  have hint : ∫ t in (0:ℝ)..M, G t = ∑ i ∈ S, w i * v i - ∑ k ∈ T, π k * u k := by
    simp only [G]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_finsetSum,
      intervalIntegral.integral_finsetSum]
    · congr 1
      · refine sum_congr rfl fun i hi => ?_
        rw [intervalIntegral.integral_const_mul, rlp_ind_int _ _ (hv i hi) (hvM i hi)]
      · refine sum_congr rfl fun k hk => ?_
        rw [intervalIntegral.integral_const_mul, rlp_ind_int _ _ (hu k hk) (huM k hk)]
    · exact fun k _ => (rlp_ind_ii _ _ _).const_mul _
    · exact fun i _ => (rlp_ind_ii _ _ _).const_mul _
    · exact rlp_sum_ii S w v _ _
    · exact rlp_sum_ii T π u _ _
  rw [← hint, ← intervalIntegral.integral_add_adjacent_intervals (hGii 0 β) (hGii β M)]
  have hA : ∫ t in (0:ℝ)..β, G t ≤ ∫ t in (0:ℝ)..β, c := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hβ (hGii 0 β) intervalIntegrable_const
    intro t ht
    rw [hGeq]; exact h3 t ht.1.le ht.2.le
  have hB : ∫ t in β..M, G t ≤ ∫ t in β..M, (0:ℝ) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hβM (hGii β M) intervalIntegrable_const
    intro t ht
    rw [hGeq]; exact h2 t (hβ.trans ht.1.le) ht.1
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_zero] at hA hB
  linarith [mul_comm β c]

section
variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]

theorem rlp_otherMax_nonneg (D : DataSet A B) (a : A) (r : B → ℝ) (w : B) :
    0 ≤ otherMax D a r w := by
  unfold otherMax
  exact le_max' _ _ (mem_insert_self _ _)

theorem rlp_revA_nonneg (D : DataSet A B) (a : A) (r : B → ℝ) : 0 ≤ revA D a r := by
  unfold revA
  split_ifs with h
  · obtain ⟨w, hw⟩ := h
    exact le_trans (le_max_of_le_right (rlp_otherMax_nonneg D a r w))
      (le_sup' (fun w => max (r w) (otherMax D a r w)) hw)
  · exact le_rfl

theorem rlp_secondBid_nonneg (D : DataSet A B) (a : A) : 0 ≤ secondBid D a := by
  unfold secondBid
  refine le_trans ?_ (le_sup' _ (show (D.b0, D.b00) ∈ (univ.offDiag : Finset (B × B)) by
    simp [D.b0_ne_b00]))
  simp [D.bid_b0, D.bid_b00]

theorem rlp_secondBid_le (D : DataSet A B) (a : A) :
    secondBid D a ≤ revA D a (fun _ => 0) := by
  have hcl : cleared D a (fun _ => 0) = univ := by
    ext b; simp [cleared, D.bid_nonneg]
  obtain ⟨w, -, hw⟩ := exists_max_image (univ : Finset B) (D.bid a) ⟨D.b0, mem_univ _⟩
  have hwt : w ∈ topBidders D a (fun _ => 0) := by
    simp only [topBidders, hcl, mem_filter, mem_univ, true_and]
    exact fun b _ => hw b (mem_univ _)
  have hge : ∀ b, b ≠ w → D.bid a b ≤ revA D a (fun _ => 0) := by
    intro b hb
    unfold revA
    rw [dif_pos ⟨w, hwt⟩]
    refine le_trans ?_ (le_sup' (fun w => max ((fun _ => (0:ℝ)) w) (otherMax D a (fun _ => 0) w)) hwt)
    refine le_trans ?_ (le_max_right _ _)
    unfold otherMax
    apply le_max'
    apply mem_insert_of_mem
    apply mem_image_of_mem
    rw [hcl]; exact mem_erase.mpr ⟨hb, mem_univ _⟩
  unfold secondBid
  apply sup'_le
  rintro ⟨b, b'⟩ hbb
  have hne : b ≠ b' := (mem_offDiag.mp hbb).2.2
  by_cases h : b = w
  · subst h
    exact (min_le_right _ _).trans (hge b' (Ne.symm hne))
  · exact (min_le_left _ _).trans (hge b h)

theorem rlp_roundProb_nonneg (D : DataSet A B) (q : B → ℝ → ℝ)
    (hq : ∀ b, ∀ r ∈ reserves D, 0 ≤ q b r) : ∀ ρ ∈ roundings D, 0 ≤ roundProb q ρ := by
  intro ρ hρ
  unfold roundProb
  apply prod_nonneg
  intro b _
  exact hq b _ (Fintype.mem_piFinset.mp hρ b)

theorem rlp_roundProb_sum (D : DataSet A B) (q : B → ℝ → ℝ)
    (hq : ∀ b, ∑ r ∈ reserves D, q b r = 1) : ∑ ρ ∈ roundings D, roundProb q ρ = 1 := by
  unfold roundings roundProb
  rw [← Finset.prod_univ_sum]
  simp [hq]

end

theorem solution {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (D : DataSet A B)
    (s : A → Profile B → ℝ) (q : B → ℝ → ℝ) (hopt : LPOptimal D s q)
    (c : ℝ) (hc : 0 < c)
    (h2 : ∀ a : A, ∀ t : ℝ, 0 ≤ t → secondBid D a < t →
      profileMassGe D s a t - probRevGe D q a t ≤ 0)
    (h3 : ∀ a : A, ∀ t : ℝ, 0 ≤ t → t ≤ secondBid D a →
      profileMassGe D s a t - probRevGe D q a t ≤ c) :
    ∀ r : B → ℝ, (∀ b, 0 ≤ r b) → (1 + c)⁻¹ * rev D r ≤ expRevOut D q := by
  intro r hr
  obtain ⟨⟨hs0, _, _, hq1, hq0⟩, _⟩ := hopt
  have hπ0 := rlp_roundProb_nonneg D q hq0
  have hπ1 := rlp_roundProb_sum D q hq1
  -- per-auction inequality
  have hper : ∀ a, ∑ p ∈ validProfiles D a, s a p * revProfile D a p -
      ∑ ρ ∈ roundings D, roundProb q ρ * revA D a ρ ≤ c * secondBid D a := by
    intro a
    apply rlp_key (validProfiles D a) (roundings D) (s a) (revProfile D a) (roundProb q)
      (fun ρ => revA D a ρ) (fun p hp => hs0 a p hp)
      (fun p _ => le_trans (D.bid_nonneg a _) (le_max_left _ _))
      (fun ρ _ => rlp_revA_nonneg D a ρ) _ c (rlp_secondBid_nonneg D a)
    · intro t ht0 ht; exact h2 a t ht0 ht
    · intro t ht0 ht; exact h3 a t ht0 ht
  have hsum : LPObj D s - ∑ ρ ∈ roundings D, roundProb q ρ * rev D ρ ≤
      c * rev D (fun _ => 0) := by
    have e : ∑ ρ ∈ roundings D, roundProb q ρ * rev D ρ =
        ∑ a, ∑ ρ ∈ roundings D, roundProb q ρ * revA D a ρ := by
      unfold rev; simp only [mul_sum]; rw [sum_comm]
    rw [e, LPObj, ← sum_sub_distrib]
    unfold rev; rw [mul_sum]
    exact sum_le_sum fun a _ => (hper a).trans
      (mul_le_mul_of_nonneg_left (rlp_secondBid_le D a) hc.le)
  have hLP : rev D r ≤ LPObj D s := lemma_4_3 D s q ⟨⟨hs0, by assumption, by assumption, hq1, hq0⟩, by assumption⟩ r hr
  have hE1 : ∑ ρ ∈ roundings D, roundProb q ρ * rev D ρ ≤ expRevOut D q := by
    unfold expRevOut
    exact sum_le_sum fun ρ hρ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hπ0 ρ hρ)
  have hE2 : rev D (fun _ => 0) ≤ expRevOut D q := by
    have : rev D (fun _ => 0) = ∑ ρ ∈ roundings D, roundProb q ρ * rev D (fun _ => 0) := by
      rw [← sum_mul, hπ1, one_mul]
    rw [this]; unfold expRevOut
    exact sum_le_sum fun ρ hρ => mul_le_mul_of_nonneg_left (le_max_right _ _) (hπ0 ρ hρ)
  have hfin : rev D r ≤ (1 + c) * expRevOut D q := by nlinarith
  rw [inv_mul_le_iff₀ (by linarith)]
  exact hfin
