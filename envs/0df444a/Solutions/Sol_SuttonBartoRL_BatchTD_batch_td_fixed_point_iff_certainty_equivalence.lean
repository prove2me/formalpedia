-- Prove2me | solution 1 for SuttonBartoRL.BatchTD.batch_td_fixed_point_iff_certainty_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T18:38:43.420057+00:00
-- url     : https://prove2.me/submissions/563e5b01-bbf1-4fc1-a277-50d40ffa11f5

import Mathlib
import Definitions.Def_SuttonBartoRL_BatchTD_Episodes
import Definitions.Def_SuttonBartoRL_BatchTD_BatchUpdating

open Filter Topology
open SuttonBartoRL.BatchTD

section
variable {S : Type} [Fintype S] [DecidableEq S]

lemma sa_lt {e : Episode S} {t : ℕ} {x : S} (h : stateAt e t = some x) : t < e.length := by
  by_contra h'
  simp [stateAt, List.getElem?_eq_none (show e.length ≤ t by omega)] at h

lemma sa_len (e : Episode S) : stateAt e e.length = none := by
  simp [stateAt]

lemma sa_some {e : Episode S} {t : ℕ} (h : t < e.length) : ∃ x, stateAt e t = some x :=
  ⟨(e[t]).1, by simp [stateAt, List.getElem?_eq_getElem h]⟩

/-- per-episode identity behind the TD increment formula -/
lemma ep_td (γ : ℝ) (V : S → ℝ) (s : S) (e : Episode S) :
    (∑ t ∈ Finset.range e.length, if stateAt e t = some s then tdError γ V e t else 0) =
      (∑ j : Option S, ∑ t ∈ Finset.range e.length, if stateAt e t = some s then
          (if stateAt e (t+1) = j then nextReward e t else 0) else 0)
      + γ * ∑ s' : S, (((Finset.range e.length).filter fun t =>
          stateAt e t = some s ∧ stateAt e (t + 1) = some s').card : ℝ) * V s'
      - (((Finset.range e.length).filter fun t => stateAt e t = some s).card : ℝ) * V s := by
  simp only [Finset.natCast_card_filter]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ (α := S))]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hA : stateAt e t = some s
  · simp only [hA, if_true, true_and, tdError, extV]
    rcases hx : stateAt e (t + 1) with _ | x
    · simp [extV]
    · simp [extV, Finset.sum_ite_eq', Finset.sum_ite_eq]
  · simp [hA]

lemma ep_cnt (s : S) (e : Episode S) :
    (((Finset.range e.length).filter fun t => stateAt e t = some s).card : ℝ) =
      ∑ j : Option S, (((Finset.range e.length).filter fun t =>
          stateAt e t = some s ∧ stateAt e (t + 1) = j).card : ℝ) := by
  simp only [Finset.natCast_card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hA : stateAt e t = some s <;> simp [hA]

variable (b : Batch S)

lemma KF (γ : ℝ) (V : S → ℝ) (s : S) :
    tdIncrement γ b V s = (∑ j, transRewardSum b s j)
      + γ * ∑ s' : S, (transCount b s (some s') : ℝ) * V s' - (visitCount b s : ℝ) * V s := by
  induction b with
  | nil => simp [tdIncrement, visitSum, transRewardSum, transCount, visitCount]
  | cons e b ih =>
    have h1 : tdIncrement γ (e :: b) V s = (∑ t ∈ Finset.range e.length,
        if stateAt e t = some s then tdError γ V e t else 0) + tdIncrement γ b V s := by
      simp [tdIncrement, visitSum]
    have h2 : ∀ j, transRewardSum (e :: b) s j = (∑ t ∈ Finset.range e.length, if stateAt e t = some s then
          (if stateAt e (t+1) = j then nextReward e t else 0) else 0) + transRewardSum b s j := by
      intro j; simp [transRewardSum, visitSum]
    have h3 : ∀ j, (transCount (e :: b) s j : ℝ) = (((Finset.range e.length).filter fun t =>
          stateAt e t = some s ∧ stateAt e (t + 1) = j).card : ℝ) + transCount b s j := by
      intro j; simp [transCount]
    have h4 : (visitCount (e :: b) s : ℝ) = (((Finset.range e.length).filter fun t =>
          stateAt e t = some s).card : ℝ) + visitCount b s := by
      simp [visitCount]
    rw [h1, ih, ep_td, h4]
    simp only [h2, h3, Finset.sum_add_distrib, add_mul]
    ring

lemma cnt_sum (s : S) : (visitCount b s : ℝ) = ∑ j, (transCount b s j : ℝ) := by
  induction b with
  | nil => simp [transCount, visitCount]
  | cons e b ih =>
    have h3 : ∀ j, (transCount (e :: b) s j : ℝ) = (((Finset.range e.length).filter fun t =>
          stateAt e t = some s ∧ stateAt e (t + 1) = j).card : ℝ) + transCount b s j := by
      intro j; simp [transCount]
    have h4 : (visitCount (e :: b) s : ℝ) = (((Finset.range e.length).filter fun t =>
          stateAt e t = some s).card : ℝ) + visitCount b s := by
      simp [visitCount]
    rw [h4, ih, ep_cnt]; simp only [h3, Finset.sum_add_distrib]

lemma trs_zero (s : S) (j : Option S) (h : transCount b s j = 0) : transRewardSum b s j = 0 := by
  induction b with
  | nil => simp [transRewardSum, visitSum]
  | cons e b ih =>
    have hc : transCount (e :: b) s j = ((Finset.range e.length).filter fun t =>
          stateAt e t = some s ∧ stateAt e (t + 1) = j).card + transCount b s j := by
      simp [transCount]
    rw [hc] at h
    have h2 : transRewardSum (e :: b) s j = (∑ t ∈ Finset.range e.length, if stateAt e t = some s then
          (if stateAt e (t+1) = j then nextReward e t else 0) else 0) + transRewardSum b s j := by
      simp [transRewardSum, visitSum]
    rw [h2, ih (by omega)]
    simp only [add_zero]
    apply Finset.sum_eq_zero
    intro t ht
    have : t ∉ (Finset.range e.length).filter fun t =>
        stateAt e t = some s ∧ stateAt e (t + 1) = j := by
      intro hmem; have := Finset.card_pos.mpr ⟨t, hmem⟩; omega
    simp only [Finset.mem_filter, ht, true_and, not_and] at this
    split_ifs with h1 h2
    · exact absurd h2 (this h1)
    · rfl
    · rfl

/-- a visit witnessed in some episode gives a positive count -/
lemma tc_pos (s : S) (j : Option S) (e : Episode S) (he : e ∈ b) (t : ℕ) (ht : t < e.length)
    (h1 : stateAt e t = some s) (h2 : stateAt e (t + 1) = j) : 1 ≤ transCount b s j := by
  induction b with
  | nil => simp at he
  | cons e' b ih =>
    have hc : transCount (e' :: b) s j = ((Finset.range e'.length).filter fun t =>
          stateAt e' t = some s ∧ stateAt e' (t + 1) = j).card + transCount b s j := by
      simp [transCount]
    rw [hc]
    rcases List.mem_cons.mp he with rfl | he
    · have : 0 < ((Finset.range e.length).filter fun t =>
          stateAt e t = some s ∧ stateAt e (t + 1) = j).card :=
        Finset.card_pos.mpr ⟨t, by simp [ht, h1, h2]⟩
      omega
    · have := ih he; omega

lemma vc_pos_of (s : S) (e : Episode S) (he : e ∈ b) (t : ℕ)
    (h1 : stateAt e t = some s) : 1 ≤ visitCount b s := by
  have := tc_pos b s _ e he t (sa_lt h1) h1 rfl
  have h := cnt_sum b s
  have hle : (transCount b s (stateAt e (t+1)) : ℝ) ≤ ∑ j, (transCount b s j : ℝ) :=
    Finset.single_le_sum (f := fun j => (transCount b s j : ℝ)) (fun _ _ => by positivity)
      (Finset.mem_univ _)
  have : (1 : ℝ) ≤ visitCount b s := by
    rw [h]; exact le_trans (by exact_mod_cast this) hle
  exact_mod_cast this

lemma tc_witness (s : S) (j : Option S) (h : transCount b s j ≠ 0) :
    ∃ e ∈ b, ∃ t, stateAt e t = some s ∧ stateAt e (t + 1) = j := by
  induction b with
  | nil => simp [transCount] at h
  | cons e b ih =>
    have hc : transCount (e :: b) s j = ((Finset.range e.length).filter fun t =>
          stateAt e t = some s ∧ stateAt e (t + 1) = j).card + transCount b s j := by
      simp [transCount]
    rw [hc] at h
    by_cases h0 : transCount b s j = 0
    · rw [h0, add_zero] at h
      obtain ⟨t, ht⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
      simp only [Finset.mem_filter] at ht
      exact ⟨e, List.mem_cons_self .., t, ht.2⟩
    · obtain ⟨e', he', t, ht⟩ := ih h0
      exact ⟨e', List.mem_cons_of_mem _ he', t, ht⟩

lemma vc_witness (s : S) (h : visitCount b s ≠ 0) : ∃ e ∈ b, ∃ t, stateAt e t = some s := by
  have h' : (visitCount b s : ℝ) ≠ 0 := by exact_mod_cast h
  rw [cnt_sum] at h'
  obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h'
  obtain ⟨e, he, t, h1, _⟩ := tc_witness b s j (by exact_mod_cast hj)
  exact ⟨e, he, t, h1⟩

lemma tc_target (s s' : S) (h : transCount b s (some s') ≠ 0) : visitCount b s' ≠ 0 := by
  obtain ⟨e, he, t, _, h2⟩ := tc_witness b s _ h
  have := vc_pos_of b s' e he (t+1) h2
  omega

end

open Matrix
section
variable {S : Type} [Fintype S] [DecidableEq S] (b : Batch S)

lemma P_nonneg (s s' : S) : 0 ≤ mlMatrix b s s' := by
  unfold mlMatrix mlProb; positivity

lemma P_unv (s s' : S) (h : visitCount b s = 0) : mlMatrix b s s' = 0 := by
  simp [mlMatrix, mlProb, h]

lemma P_tgt (s s' : S) (h : mlMatrix b s s' ≠ 0) : visitCount b s' ≠ 0 := by
  apply tc_target b s s'
  intro h0; apply h; simp [mlMatrix, mlProb, h0]

lemma P_mul (s s' : S) (h : visitCount b s ≠ 0) :
    (transCount b s (some s') : ℝ) = (visitCount b s : ℝ) * mlMatrix b s s' := by
  have : (visitCount b s : ℝ) ≠ 0 := by exact_mod_cast h
  simp only [mlMatrix, mlProb]; field_simp

lemma row_eq (s : S) (h : visitCount b s ≠ 0) :
    ∑ s', mlMatrix b s s' = 1 - (transCount b s none : ℝ) / visitCount b s := by
  have hn : (visitCount b s : ℝ) ≠ 0 := by exact_mod_cast h
  have hc := cnt_sum b s
  rw [Fintype.sum_option] at hc
  simp only [mlMatrix, mlProb, ← Finset.sum_div]
  field_simp
  linarith

lemma row_le (s : S) : ∑ s', mlMatrix b s s' ≤ 1 := by
  by_cases h : visitCount b s = 0
  · simp [P_unv b s _ h]
  · rw [row_eq b s h]
    have : 0 ≤ (transCount b s none : ℝ) / visitCount b s := by positivity
    linarith

lemma rhat_mul (s : S) (h : visitCount b s ≠ 0) :
    (visitCount b s : ℝ) * mlExpectedReward b s = ∑ j, transRewardSum b s j := by
  have hn : (visitCount b s : ℝ) ≠ 0 := by exact_mod_cast h
  simp only [mlExpectedReward, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hc : transCount b s j = 0
  · simp [hc, trs_zero b s j hc, mlProb]
  · have hc' : (transCount b s j : ℝ) ≠ 0 := by exact_mod_cast hc
    simp only [mlProb, mlReward]; field_simp

lemma td_vis (γ : ℝ) (V : S → ℝ) (s : S) (h : visitCount b s ≠ 0) :
    tdIncrement γ b V s = (visitCount b s : ℝ) *
      (mlExpectedReward b s + γ * ∑ s', mlMatrix b s s' * V s' - V s) := by
  rw [KF, ← rhat_mul b s h]
  simp only [P_mul b s _ h]
  have : ∑ s', (visitCount b s : ℝ) * mlMatrix b s s' * V s' =
      (visitCount b s : ℝ) * ∑ s', mlMatrix b s s' * V s' := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro _ _; ring
  rw [this]; ring

lemma td_unv (γ : ℝ) (V : S → ℝ) (s : S) (h : visitCount b s = 0) :
    tdIncrement γ b V s = 0 := by
  have hc : ∀ j, transCount b s j = 0 := by
    intro j
    have h0 := cnt_sum b s
    simp only [h, Nat.cast_zero] at h0
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => (Nat.cast_nonneg (α := ℝ) (transCount b s j)))).mp h0.symm j (Finset.mem_univ _)
    exact_mod_cast this
  rw [KF]
  simp [hc, trs_zero b s _ (hc _), h]

/-- survival mass -/
noncomputable def uu (k : ℕ) (s : S) : ℝ := ∑ s', (mlMatrix b ^ k) s s'

lemma Pk_nonneg (k : ℕ) (s s' : S) : 0 ≤ (mlMatrix b ^ k) s s' := by
  induction k generalizing s s' with
  | zero => simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg fun _ _ => mul_nonneg (P_nonneg b _ _) (ih _ _)

lemma uu_succ (k : ℕ) (s : S) : uu b (k+1) s = ∑ s', mlMatrix b s s' * uu b k s' := by
  simp only [uu, pow_succ', Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma uu_le (k : ℕ) (s : S) : uu b k s ≤ 1 := by
  induction k generalizing s with
  | zero => simp [uu, Matrix.one_apply]
  | succ k ih =>
    rw [uu_succ]
    calc ∑ s', mlMatrix b s s' * uu b k s' ≤ ∑ s', mlMatrix b s s' * 1 :=
          Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (ih s') (P_nonneg b _ _)
      _ ≤ 1 := by simpa using row_le b s

noncomputable def NN : ℝ := ∑ s, (visitCount b s : ℝ)
noncomputable def δδ : ℝ := 1 / (NN b + 2)

lemma NN_nonneg : 0 ≤ NN b := by unfold NN; positivity
lemma δ_pos : 0 < δδ b := by unfold δδ; have := NN_nonneg b; positivity
lemma δ_le : δδ b ≤ 1/2 := by
  unfold δδ; have := NN_nonneg b
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith

lemma inv_ge (s : S) (h : visitCount b s ≠ 0) : δδ b ≤ 1 / (visitCount b s : ℝ) := by
  have h1 : (1 : ℝ) ≤ visitCount b s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
  have h2 : (visitCount b s : ℝ) ≤ NN b :=
    Finset.single_le_sum (f := fun s => (visitCount b s : ℝ)) (fun _ _ => by positivity)
      (Finset.mem_univ s)
  unfold δδ
  apply one_div_le_one_div_of_le (by linarith); linarith

lemma decay (d : ℕ) : ∀ (e : Episode S), e ∈ b → ∀ t s, stateAt e t = some s →
    e.length = t + d + 1 → ∀ k, d + 1 ≤ k → uu b k s ≤ 1 - δδ b ^ (d + 1) := by
  induction d with
  | zero =>
    intro e he t s hs hl k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hv : visitCount b s ≠ 0 := by have := vc_pos_of b s e he t hs; omega
    have hnone : stateAt e (t+1) = none := by rw [show t + 1 = e.length by omega]; exact sa_len e
    have hc := tc_pos b s none e he t (by omega) hs hnone
    rw [uu_succ]
    calc ∑ s', mlMatrix b s s' * uu b k s' ≤ ∑ s', mlMatrix b s s' * 1 :=
          Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (uu_le b _ s') (P_nonneg b _ _)
      _ = 1 - (transCount b s none : ℝ) / visitCount b s := by simp [row_eq b s hv]
      _ ≤ 1 - δδ b ^ (0 + 1) := by
          have h1 : (1:ℝ) ≤ transCount b s none := by exact_mod_cast hc
          have h2 := inv_ge b s hv
          have h3 : 1 / (visitCount b s : ℝ) ≤ (transCount b s none : ℝ) / visitCount b s :=
            div_le_div_of_nonneg_right h1 (by positivity)
          simp only [zero_add, pow_one]; linarith
  | succ d ih =>
    intro e he t s hs hl k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hv : visitCount b s ≠ 0 := by have := vc_pos_of b s e he t hs; omega
    obtain ⟨s2, hs2⟩ := sa_some (e := e) (t := t + 1) (by omega)
    have hc := tc_pos b s (some s2) e he t (by omega) hs hs2
    have hIH := ih e he (t+1) s2 hs2 (by omega) k (by omega)
    have hP : δδ b ≤ mlMatrix b s s2 := by
      have h1 : (1:ℝ) ≤ transCount b s (some s2) := by exact_mod_cast hc
      have h2 := inv_ge b s hv
      have h3 : 1 / (visitCount b s : ℝ) ≤ (transCount b s (some s2) : ℝ) / visitCount b s :=
        div_le_div_of_nonneg_right h1 (by positivity)
      show δδ b ≤ (transCount b s (some s2) : ℝ) / visitCount b s
      linarith
    rw [uu_succ]
    calc ∑ s', mlMatrix b s s' * uu b k s'
        ≤ ∑ s', mlMatrix b s s' * (1 - if s' = s2 then δδ b ^ (d + 1) else 0) := by
          apply Finset.sum_le_sum; intro s' _
          apply mul_le_mul_of_nonneg_left _ (P_nonneg b _ _)
          split_ifs with h
          · subst h; exact hIH
          · simpa using uu_le b k s'
      _ = ∑ s', mlMatrix b s s' - mlMatrix b s s2 * δδ b ^ (d + 1) := by
          simp only [mul_sub, mul_one, Finset.sum_sub_distrib, mul_ite, mul_zero,
            Finset.sum_ite_eq', Finset.mem_univ, if_true]
      _ ≤ 1 - δδ b ^ (d + 1 + 1) := by
          have := row_le b s
          have hd : 0 ≤ δδ b ^ (d + 1) := pow_nonneg (δ_pos b).le _
          have : δδ b * δδ b ^ (d + 1) ≤ mlMatrix b s s2 * δδ b ^ (d + 1) :=
            mul_le_mul_of_nonneg_right hP hd
          have e2 : δδ b ^ (d + 1 + 1) = δδ b * δδ b ^ (d + 1) := pow_succ' _ _
          linarith

lemma len_le (e : Episode S) (he : e ∈ b) : e.length ≤ (b.map List.length).sum := by
  induction b with
  | nil => simp at he
  | cons e' b ih =>
    rcases List.mem_cons.mp he with rfl | he
    · simp
    · have := ih he; simp; omega

noncomputable def LL : ℕ := (b.map List.length).sum + 1
noncomputable def ρρ : ℝ := 1 - δδ b ^ LL b

lemma ρ_lt : ρρ b < 1 := by
  unfold ρρ; have := pow_pos (δ_pos b) (LL b); linarith
lemma ρ_ge : 1/2 ≤ ρρ b := by
  unfold ρρ
  have h1 : δδ b ^ LL b ≤ δδ b := pow_le_of_le_one (δ_pos b).le (by linarith [δ_le b])
    (by unfold LL; omega)
  linarith [δ_le b]

lemma uu_L (s : S) : uu b (LL b) s ≤ ρρ b := by
  by_cases hv : visitCount b s = 0
  · have : LL b = (b.map List.length).sum + 1 := rfl
    rw [this, uu_succ]
    simp [P_unv b s _ hv]
    linarith [ρ_ge b]
  · obtain ⟨e, he, t, hs⟩ := vc_witness b s hv
    have ht := sa_lt hs
    have hl := len_le b e he
    have := decay b (e.length - t - 1) e he t s hs (by omega) (LL b) (by unfold LL; omega)
    unfold ρρ
    have : δδ b ^ LL b ≤ δδ b ^ (e.length - t - 1 + 1) :=
      pow_le_pow_of_le_one (δ_pos b).le (by linarith [δ_le b]) (by unfold LL; omega)
    linarith

lemma mv_bound (k : ℕ) (w : S → ℝ) (s : S) :
    |(mlMatrix b ^ k *ᵥ w) s| ≤ uu b k s * ‖w‖ := by
  simp only [Matrix.mulVec, dotProduct, uu, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s' _ => ?_)
  rw [abs_mul, abs_of_nonneg (Pk_nonneg b _ _ _)]
  apply mul_le_mul_of_nonneg_left _ (Pk_nonneg b _ _ _)
  have := norm_le_pi_norm w s'
  rwa [Real.norm_eq_abs] at this

lemma nrm_le (k : ℕ) (w : S → ℝ) : ‖mlMatrix b ^ k *ᵥ w‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun s => ?_
  rw [Real.norm_eq_abs]
  refine (mv_bound b k w s).trans ?_
  have := uu_le b k s
  nlinarith [norm_nonneg w]

lemma nrm_L (w : S → ℝ) : ‖mlMatrix b ^ LL b *ᵥ w‖ ≤ ρρ b * ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (by have := ρ_ge b; positivity)).mpr fun s => ?_
  rw [Real.norm_eq_abs]
  refine (mv_bound b _ w s).trans ?_
  have := uu_L b s
  nlinarith [norm_nonneg w]

lemma LL_pos : 0 < LL b := by unfold LL; omega

lemma nrm_decay (k : ℕ) (w : S → ℝ) : ‖mlMatrix b ^ k *ᵥ w‖ ≤ ρρ b ^ (k / LL b) * ‖w‖ := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < LL b
    · rw [Nat.div_eq_of_lt hk, pow_zero, one_mul]; exact nrm_le b k w
    · have hL := LL_pos b
      have e1 : k = LL b + (k - LL b) := by omega
      have e2 : k / LL b = (k - LL b) / LL b + 1 := Nat.div_eq_sub_div hL (by omega)
      rw [e2, e1, pow_add, ← Matrix.mulVec_mulVec, ← e1]
      refine (nrm_L b _).trans ?_
      have := ih (k - LL b) (by omega)
      rw [pow_succ]
      have hρ : 0 ≤ ρρ b := by have := ρ_ge b; linarith
      nlinarith [pow_nonneg hρ ((k - LL b) / LL b)]

lemma geom_bd (k : ℕ) : ρρ b ^ (k / LL b) ≤ (ρρ b ^ ((1:ℝ) / LL b)) ^ k / ρρ b := by
  have hρ0 : 0 < ρρ b := by have := ρ_ge b; linarith
  have hL : (0:ℝ) < LL b := by exact_mod_cast LL_pos b
  rw [le_div_iff₀ hρ0, ← pow_succ, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul hρ0.le]
  apply Real.rpow_le_rpow_of_exponent_ge hρ0 (ρ_lt b).le
  have := Nat.lt_mul_div_succ k (LL_pos b)
  have h2 : (k : ℝ) ≤ (LL b : ℝ) * ((k / LL b : ℕ) + 1 : ℕ) := by exact_mod_cast this.le
  push_cast at h2 ⊢
  rw [one_div_mul_eq_div, div_le_iff₀ hL]; linarith

lemma summ (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (w : S → ℝ) (s : S) :
    Summable fun k : ℕ => γ ^ k * (mlMatrix b ^ k *ᵥ w) s := by
  have hρ0 : 0 < ρρ b := by have := ρ_ge b; linarith
  set σ := ρρ b ^ ((1:ℝ) / LL b)
  have hσ0 : 0 ≤ σ := Real.rpow_nonneg hρ0.le _
  have hσ1 : σ < 1 := Real.rpow_lt_one hρ0.le (ρ_lt b) (by have := LL_pos b; positivity)
  refine Summable.of_norm_bounded (g := fun k => σ ^ k * (‖w‖ / ρρ b))
    ((summable_geometric_of_lt_one hσ0 hσ1).mul_right _) (fun k => ?_)
  rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hγ0]
  have h1 : ‖(mlMatrix b ^ k *ᵥ w) s‖ ≤ ‖mlMatrix b ^ k *ᵥ w‖ := norm_le_pi_norm _ s
  have h2 := nrm_decay b k w
  have h3 := geom_bd b k
  have hγk : γ ^ k ≤ 1 := pow_le_one₀ hγ0 hγ1
  calc γ ^ k * ‖(mlMatrix b ^ k *ᵥ w) s‖ ≤ 1 * (ρρ b ^ (k / LL b) * ‖w‖) :=
        mul_le_mul hγk (h1.trans h2) (norm_nonneg _) zero_le_one
    _ ≤ σ ^ k / ρρ b * ‖w‖ := by
        rw [one_mul]; exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    _ = σ ^ k * (‖w‖ / ρρ b) := by ring

lemma bellman (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (s : S) :
    ceEstimate γ b s = mlExpectedReward b s + γ * ∑ s', mlMatrix b s s' * ceEstimate γ b s' := by
  unfold ceEstimate
  rw [(summ b γ hγ0 hγ1 _ s).tsum_eq_zero_add]
  simp only [pow_zero, one_mul, Matrix.one_mulVec]
  congr 1
  have hf : ∀ k, γ ^ (k+1) * (mlMatrix b ^ (k+1) *ᵥ mlExpectedReward b) s =
      γ * ∑ s', mlMatrix b s s' * (γ ^ k * (mlMatrix b ^ k *ᵥ mlExpectedReward b) s') := by
    intro k
    rw [show mlMatrix b ^ (k+1) = mlMatrix b * mlMatrix b ^ k from pow_succ' _ _,
      ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, pow_succ]
    apply Finset.sum_congr rfl; intro s' _; ring
  simp only [hf]
  rw [tsum_mul_left]
  congr 1
  rw [Summable.tsum_finsetSum (fun s' _ => (summ b γ hγ0 hγ1 _ s').mul_left _)]
  apply Finset.sum_congr rfl; intro s' _
  rw [tsum_mul_left]

theorem solution_main (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (∀ s : S, Summable fun k : ℕ => γ ^ k * (Matrix.mulVec (mlMatrix b ^ k) (mlExpectedReward b)) s) ∧
    ∀ V : S → ℝ,
      (∀ s : S, tdIncrement γ b V s = 0) ↔
        ∀ s : S, visitCount b s ≠ 0 → V s = ceEstimate γ b s := by
  refine ⟨fun s => summ b γ hγ0 hγ1 _ s, fun V => ⟨fun hV => ?_, fun hV s => ?_⟩⟩
  · set v := ceEstimate γ b
    let W : S → ℝ := fun s => if visitCount b s ≠ 0 then V s - v s else 0
    have hPW : ∀ s, ∑ s', mlMatrix b s s' * W s' = ∑ s', mlMatrix b s s' * (V s' - v s') := by
      intro s; apply Finset.sum_congr rfl; intro s' _
      by_cases hP : mlMatrix b s s' = 0
      · simp [hP]
      · simp [W, P_tgt b s s' hP]
    have hW : ∀ s, W s = γ * ∑ s', mlMatrix b s s' * W s' := by
      intro s
      by_cases hv : visitCount b s = 0
      · simp [W, hv, P_unv b s _ hv]
      · have h1 := hV s
        rw [td_vis b γ V s hv] at h1
        have hn : (visitCount b s : ℝ) ≠ 0 := by exact_mod_cast hv
        have h2 : V s = mlExpectedReward b s + γ * ∑ s', mlMatrix b s s' * V s' := by
          rcases mul_eq_zero.mp h1 with h | h
          · exact absurd h hn
          · linarith
        have h3 : v s = mlExpectedReward b s + γ * ∑ s', mlMatrix b s s' * v s' :=
          bellman b γ hγ0 hγ1 s
        simp only [W, ne_eq, hv, not_false_eq_true, if_true]
        rw [hPW, h2, h3]
        simp only [mul_sub, Finset.sum_sub_distrib]; ring
    have hWv : W = γ • (mlMatrix b *ᵥ W) := by
      funext s; rw [hW s]; simp [Matrix.mulVec, dotProduct]
    have hk : ∀ k : ℕ, W = γ ^ k • (mlMatrix b ^ k *ᵥ W) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have e : γ ^ (k+1) • (mlMatrix b ^ (k+1) *ᵥ W) =
            γ ^ k • (mlMatrix b ^ k *ᵥ (γ • (mlMatrix b *ᵥ W))) := by
          rw [Matrix.mulVec_smul, smul_smul, Matrix.mulVec_mulVec, ← pow_succ, ← pow_succ]
        rw [e, ← hWv]; exact ih
    have hn : ‖W‖ ≤ ρρ b * ‖W‖ := by
      calc ‖W‖ = ‖γ ^ LL b • (mlMatrix b ^ LL b *ᵥ W)‖ := by rw [← hk]
        _ = γ ^ LL b * ‖mlMatrix b ^ LL b *ᵥ W‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hγ0 _)]
        _ ≤ 1 * (ρρ b * ‖W‖) :=
            mul_le_mul (pow_le_one₀ hγ0 hγ1) (nrm_L b W) (norm_nonneg _) zero_le_one
        _ = ρρ b * ‖W‖ := one_mul _
    have h0 : ‖W‖ = 0 := by
      have := ρ_lt b; have := norm_nonneg W; nlinarith
    intro s hs
    have : W s = 0 := by rw [norm_eq_zero.mp h0]; rfl
    simp only [W, ne_eq, hs, not_false_eq_true, if_true] at this
    linarith
  · by_cases hv : visitCount b s = 0
    · exact td_unv b γ V s hv
    · rw [td_vis b γ V s hv]
      have hPV : ∑ s', mlMatrix b s s' * V s' = ∑ s', mlMatrix b s s' * ceEstimate γ b s' := by
        apply Finset.sum_congr rfl; intro s' _
        by_cases hP : mlMatrix b s s' = 0
        · simp [hP]
        · rw [hV s' (P_tgt b s s' hP)]
      rw [hPV, hV s hv, ← bellman b γ hγ0 hγ1 s]; ring

end

theorem solution {S : Type} [Fintype S] [DecidableEq S]
    (b : Batch S) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (∀ s : S, Summable fun k : ℕ => γ ^ k * (Matrix.mulVec (mlMatrix b ^ k) (mlExpectedReward b)) s) ∧
    ∀ V : S → ℝ,
      (∀ s : S, tdIncrement γ b V s = 0) ↔
        ∀ s : S, visitCount b s ≠ 0 → V s = ceEstimate γ b s :=
  solution_main b γ hγ0 hγ1
