-- Prove2me | solution 1 for OceanicGames.Limit.appendix_A3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:24:58.462978+00:00
-- url     : https://prove2.me/submissions/ba3a4375-8b0f-47a7-949a-90854d416bb5

import Mathlib
import Definitions.Def_OceanicGames_Limit_Basic

open MeasureTheory Set Finset Filter Topology

namespace OceanicGames.Limit

set_option autoImplicit false

theorem beta_int_step (s k : ℕ) :
    ((s:ℝ)+1) * ∫ t in (0:ℝ)..1, t^s * (1-t)^(k+1) =
      ((k:ℝ)+1) * ∫ t in (0:ℝ)..1, t^(s+1) * (1-t)^k := by
  have hd : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun t : ℝ => t^(s+1) * (1-t)^(k+1))
      (((s:ℝ)+1) * (t^s * (1-t)^(k+1)) - ((k:ℝ)+1) * (t^(s+1) * (1-t)^k)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => t^(s+1)) (((s+1 : ℕ):ℝ) * t^s) t := by
      simpa using hasDerivAt_pow (s+1) t
    have h2 : HasDerivAt (fun t : ℝ => (1-t)^(k+1)) (((k+1 : ℕ):ℝ) * (1-t)^k * (-1)) t := by
      have := (hasDerivAt_id t).const_sub (1:ℝ)
      simpa using this.fun_pow (k+1)
    refine (h1.mul h2).congr_deriv ?_
    push_cast
    ring
  have hint : IntervalIntegrable (fun t : ℝ => ((s:ℝ)+1) * (t^s * (1-t)^(k+1)) -
      ((k:ℝ)+1) * (t^(s+1) * (1-t)^k)) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  simp at h
  rw [intervalIntegral.integral_sub] at h
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
    linarith
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop

theorem beta_int (s k : ℕ) :
    ∫ t in (0:ℝ)..1, t^s * (1-t)^k = (s.factorial * k.factorial : ℝ) / (s + k + 1).factorial := by
  induction k generalizing s with
  | zero =>
    simp only [pow_zero, mul_one, integral_pow, Nat.factorial_zero, Nat.cast_one, add_zero]
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    simp
  | succ k ih =>
    have h := beta_int_step s k
    rw [ih (s+1)] at h
    have hs : ((s:ℝ)+1) ≠ 0 := by positivity
    have e : s + 1 + k + 1 = s + (k+1) + 1 := by ring
    rw [e] at h
    have h2 : ∫ t in (0:ℝ)..1, t^s * (1-t)^(k+1) =
        ((k:ℝ)+1) * (((s+1).factorial * k.factorial : ℝ) / (s + (k+1) + 1).factorial) / ((s:ℝ)+1) := by
      rw [eq_div_iff hs]
      linarith
    rw [h2, Nat.factorial_succ s, Nat.factorial_succ k]
    push_cast
    field_simp


/-- Bernoulli weight of a subset `T` of a set of size `n`. -/
noncomputable def bw {ι : Type*} (t : ℝ) (n : ℕ) (T : Finset ι) : ℝ := t ^ T.card * (1 - t) ^ (n - T.card)

theorem bern_insert {ι : Type*} [DecidableEq ι] (t : ℝ) (s : Finset ι) (a : ι) (ha : a ∉ s)
    (g : Finset ι → ℝ) :
    ∑ T ∈ (insert a s).powerset, bw t (insert a s).card T * g T =
      ∑ T ∈ s.powerset, bw t s.card T * ((1 - t) * g T + t * g (insert a T)) := by
  rw [Finset.sum_powerset_insert ha, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  have hTs : T ⊆ s := Finset.mem_powerset.1 hT
  have haT : a ∉ T := fun h => ha (hTs h)
  have hle : T.card ≤ s.card := Finset.card_le_card hTs
  unfold bw
  rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem haT,
    show s.card + 1 - T.card = (s.card - T.card) + 1 by omega,
    show s.card + 1 - (T.card + 1) = s.card - T.card by omega]
  ring

theorem bern_sum_one {ι : Type*} [DecidableEq ι] (t : ℝ) (s : Finset ι) :
    ∑ T ∈ s.powerset, bw t s.card T = 1 := by
  have := Finset.sum_pow_mul_eq_add_pow t (1 - t) s
  simpa [bw] using this

theorem bern_sum_mean {ι : Type*} [DecidableEq ι] (t : ℝ) (a : ι → ℝ) (s : Finset ι) :
    ∑ T ∈ s.powerset, bw t s.card T * (∑ j ∈ T, a j) = t * ∑ j ∈ s, a j := by
  induction s using Finset.induction_on with
  | empty => simp [bw]
  | insert x s hx ih =>
    rw [bern_insert t s x hx, Finset.sum_insert hx]
    have e : ∀ T ∈ s.powerset, bw t s.card T * ((1 - t) * (∑ j ∈ T, a j) +
        t * (∑ j ∈ insert x T, a j)) =
        bw t s.card T * (∑ j ∈ T, a j) + t * a x * bw t s.card T := by
      intro T hT
      have haT : x ∉ T := fun h => hx (Finset.mem_powerset.1 hT h)
      rw [Finset.sum_insert haT]; ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ih, ← Finset.mul_sum, bern_sum_one]
    ring

theorem bern_sum_sq {ι : Type*} [DecidableEq ι] (t : ℝ) (a : ι → ℝ) (s : Finset ι) :
    ∑ T ∈ s.powerset, bw t s.card T * (∑ j ∈ T, a j) ^ 2 =
      t ^ 2 * (∑ j ∈ s, a j) ^ 2 + t * (1 - t) * ∑ j ∈ s, (a j) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp [bw]
  | insert x s hx ih =>
    rw [bern_insert t s x hx, Finset.sum_insert hx, Finset.sum_insert hx]
    have e : ∀ T ∈ s.powerset, bw t s.card T * ((1 - t) * (∑ j ∈ T, a j) ^ 2 +
        t * (∑ j ∈ insert x T, a j) ^ 2) =
        bw t s.card T * (∑ j ∈ T, a j) ^ 2 + 2 * t * a x * (bw t s.card T * ∑ j ∈ T, a j)
          + t * (a x) ^ 2 * bw t s.card T := by
      intro T hT
      have haT : x ∉ T := fun h => hx (Finset.mem_powerset.1 hT h)
      rw [Finset.sum_insert haT]; ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib, ih,
      ← Finset.mul_sum, ← Finset.mul_sum, bern_sum_mean, bern_sum_one]
    ring

theorem bern_sum_var {ι : Type*} [DecidableEq ι] (t : ℝ) (a : ι → ℝ) (s : Finset ι) :
    ∑ T ∈ s.powerset, bw t s.card T * ((∑ j ∈ T, a j) - t * ∑ j ∈ s, a j) ^ 2 =
      t * (1 - t) * ∑ j ∈ s, (a j) ^ 2 := by
  have e : ∀ T ∈ s.powerset, bw t s.card T * ((∑ j ∈ T, a j) - t * ∑ j ∈ s, a j) ^ 2 =
      bw t s.card T * (∑ j ∈ T, a j) ^ 2 - 2 * t * (∑ j ∈ s, a j) * (bw t s.card T * ∑ j ∈ T, a j)
        + t ^ 2 * (∑ j ∈ s, a j) ^ 2 * bw t s.card T := by
    intro T _; ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_sub_distrib, bern_sum_sq,
    ← Finset.mul_sum, ← Finset.mul_sum, bern_sum_mean, bern_sum_one]
  ring

/-- The probability that the random sum of minor weights lies in `[lo, hi)`. -/
noncomputable def Qf {n : ℕ} (a : Fin n → ℝ) (t lo hi : ℝ) : ℝ :=
  ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset, bw t n T *
    (if lo ≤ ∑ j ∈ T, a j ∧ ∑ j ∈ T, a j < hi then 1 else 0)

theorem bw_nonneg {ι : Type*} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) (T : Finset ι) :
    0 ≤ bw t n T := by
  unfold bw
  exact mul_nonneg (pow_nonneg ht0 _) (pow_nonneg (by linarith) _)

theorem bern_one' (n : ℕ) (t : ℝ) :
    ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset, bw t n T = 1 := by
  have := bern_sum_one t (Finset.univ : Finset (Fin n))
  simpa using this

theorem Qf_nonneg {n : ℕ} (a : Fin n → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (lo hi : ℝ) :
    0 ≤ Qf a t lo hi := by
  unfold Qf
  apply Finset.sum_nonneg
  intro T _
  exact mul_nonneg (bw_nonneg ht0 ht1 _ _) (by split_ifs <;> norm_num)

theorem Qf_le_one {n : ℕ} (a : Fin n → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (lo hi : ℝ) :
    Qf a t lo hi ≤ 1 := by
  unfold Qf
  refine le_trans (Finset.sum_le_sum (g := fun T => bw t n T) ?_) (bern_one' n t).le
  intro T _
  have := bw_nonneg ht0 ht1 n T
  split_ifs <;> nlinarith

theorem cheb {n : ℕ} (a : Fin n → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset, bw t n T *
      (if δ ≤ |(∑ j ∈ T, a j) - t * ∑ j, a j| then 1 else 0) ≤ (∑ j, (a j) ^ 2) / δ ^ 2 := by
  have hvar := bern_sum_var t a (Finset.univ : Finset (Fin n))
  simp only [Finset.card_univ, Fintype.card_fin] at hvar
  have h1 : ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset, bw t n T *
      (if δ ≤ |(∑ j ∈ T, a j) - t * ∑ j, a j| then 1 else 0) ≤
      ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        bw t n T * ((∑ j ∈ T, a j) - t * ∑ j, a j) ^ 2 / δ ^ 2 := by
    apply Finset.sum_le_sum
    intro T _
    have hb := bw_nonneg ht0 ht1 n T
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hb
    split_ifs with h
    · rw [le_div_iff₀ (by positivity)]
      have : δ ^ 2 ≤ |(∑ j ∈ T, a j) - t * ∑ j, a j| ^ 2 := by
        exact pow_le_pow_left₀ hδ.le h 2
      rw [sq_abs] at this
      linarith
    · positivity
  refine h1.trans ?_
  rw [← Finset.sum_div, hvar]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hs : 0 ≤ ∑ j, (a j) ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have : t * (1 - t) ≤ 1 := by nlinarith
  nlinarith

theorem Qf_lower {n : ℕ} (a : Fin n → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    {lo hi : ℝ} (h1 : lo ≤ t * ∑ j, a j - δ) (h2 : t * ∑ j, a j + δ ≤ hi) :
    1 - (∑ j, (a j) ^ 2) / δ ^ 2 ≤ Qf a t lo hi := by
  have hc := cheb a ht0 ht1 hδ
  have : 1 - ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset, bw t n T *
      (if δ ≤ |(∑ j ∈ T, a j) - t * ∑ j, a j| then 1 else 0) ≤ Qf a t lo hi := by
    calc 1 - ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset, bw t n T *
      (if δ ≤ |(∑ j ∈ T, a j) - t * ∑ j, a j| then 1 else 0)
        = ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset, (bw t n T - bw t n T *
          (if δ ≤ |(∑ j ∈ T, a j) - t * ∑ j, a j| then 1 else 0)) := by
          rw [Finset.sum_sub_distrib, bern_one']
      _ ≤ Qf a t lo hi := by
          unfold Qf
          apply Finset.sum_le_sum
          intro T _
          have hb := bw_nonneg ht0 ht1 n T
          by_cases hT : δ ≤ |(∑ j ∈ T, a j) - t * ∑ j, a j|
          · simp only [hT, if_true]
            have : (0:ℝ) ≤ bw t n T * (if lo ≤ ∑ j ∈ T, a j ∧ ∑ j ∈ T, a j < hi then 1 else 0) :=
              mul_nonneg hb (by split_ifs <;> norm_num)
            linarith
          · simp only [hT, if_false]
            rw [not_le, abs_lt] at hT
            have hg : lo ≤ ∑ j ∈ T, a j ∧ ∑ j ∈ T, a j < hi := ⟨by linarith, by linarith⟩
            simp only [hg, and_self, if_true]
            linarith
  linarith

theorem Qf_upper {n : ℕ} (a : Fin n → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    {lo hi : ℝ} (h : t * ∑ j, a j + δ ≤ lo ∨ hi ≤ t * ∑ j, a j - δ) :
    Qf a t lo hi ≤ (∑ j, (a j) ^ 2) / δ ^ 2 := by
  refine le_trans ?_ (cheb a ht0 ht1 hδ)
  unfold Qf
  apply Finset.sum_le_sum
  intro T _
  have hb := bw_nonneg ht0 ht1 n T
  apply mul_le_mul_of_nonneg_left _ hb
  by_cases hg : lo ≤ ∑ j ∈ T, a j ∧ ∑ j ∈ T, a j < hi
  · have hT : δ ≤ |(∑ j ∈ T, a j) - t * ∑ j, a j| := by
      rcases h with h | h
      · exact le_trans (by linarith [hg.1]) (le_abs_self _)
      · rw [abs_sub_comm]
        exact le_trans (by linarith [hg.2]) (le_abs_self _)
    simp [hg, hT]
  · simp only [hg, if_false]
    split_ifs <;> norm_num

theorem sumsq_tendsto {n : ℕ → ℕ} (a : (l : ℕ) → Fin (n l) → ℝ) (ha : ∀ l j, 0 ≤ a l j) {α : ℝ}
    (halim : Tendsto (fun l => ∑ j, a l j) atTop (𝓝 α))
    (hamax : ∀ ε : ℝ, 0 < ε → ∀ᶠ l in atTop, ∀ j, a l j ≤ ε) :
    Tendsto (fun l => ∑ j, (a l j) ^ 2) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hb : ∀ᶠ l in atTop, ∑ j, a l j < |α| + 1 :=
    Filter.Tendsto.eventually_lt_const (by linarith [le_abs_self α]) halim
  have hpos : 0 < |α| + 2 := by positivity
  filter_upwards [hamax (ε / (|α| + 2)) (by positivity), hb] with l h1 h2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg _))]
  calc ∑ j, (a l j) ^ 2 ≤ ∑ j, (ε / (|α| + 2)) * a l j :=
        Finset.sum_le_sum (fun j _ => by nlinarith [ha l j, h1 j])
    _ = ε / (|α| + 2) * ∑ j, a l j := by rw [Finset.mul_sum]
    _ < ε / (|α| + 2) * (|α| + 1) := mul_lt_mul_of_pos_left h2 (by positivity)
    _ ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      nlinarith

theorem Qf_tendsto {n : ℕ → ℕ} (a : (l : ℕ) → Fin (n l) → ℝ) (ha : ∀ l j, 0 ≤ a l j) {α : ℝ}
    (halim : Tendsto (fun l => ∑ j, a l j) atTop (𝓝 α))
    (hamax : ∀ ε : ℝ, 0 < ε → ∀ᶠ l in atTop, ∀ j, a l j ≤ ε)
    (lo hi : ℕ → ℝ) {lo0 hi0 : ℝ} (hlo : Tendsto lo atTop (𝓝 lo0)) (hhi : Tendsto hi atTop (𝓝 hi0))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hne1 : t * α ≠ lo0) (hne2 : t * α ≠ hi0) :
    Tendsto (fun l => Qf (a l) t (lo l) (hi l)) atTop
      (𝓝 (if lo0 ≤ t * α ∧ t * α ≤ hi0 then 1 else 0)) := by
  have hS := sumsq_tendsto a ha halim hamax
  have hμ : Tendsto (fun l => t * ∑ j, a l j) atTop (𝓝 (t * α)) := halim.const_mul t
  have heps : ∀ δ : ℝ, Tendsto (fun l => (∑ j, (a l j) ^ 2) / δ ^ 2) atTop (𝓝 0) := by
    intro δ
    simpa using hS.div_const (δ ^ 2)
  rcases lt_or_gt_of_ne hne1 with h1 | h1
  · -- t * α < lo0
    have hδ : 0 < (lo0 - t * α) / 3 := by linarith
    have hE : ∀ᶠ l in atTop, (lo0 - t * α) / 3 < lo l - t * ∑ j, a l j :=
      Filter.Tendsto.eventually_const_lt (by linarith) (hlo.sub hμ)
    have hcond : ¬ (lo0 ≤ t * α ∧ t * α ≤ hi0) := fun h => by linarith [h.1]
    rw [if_neg hcond]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (heps ((lo0 - t * α) / 3))
      (Eventually.of_forall fun l => Qf_nonneg _ ht0 ht1 _ _) ?_
    filter_upwards [hE] with l hl
    exact Qf_upper _ ht0 ht1 hδ (Or.inl (by linarith))
  · rcases lt_or_gt_of_ne hne2 with h2 | h2
    · -- lo0 < t * α < hi0
      have hδ : 0 < min (t * α - lo0) (hi0 - t * α) / 3 := by
        have := lt_min (sub_pos.2 h1) (sub_pos.2 h2)
        linarith
      have hm1 := min_le_left (t * α - lo0) (hi0 - t * α)
      have hm2 := min_le_right (t * α - lo0) (hi0 - t * α)
      have hE1 : ∀ᶠ l in atTop, lo l - t * ∑ j, a l j < - (min (t * α - lo0) (hi0 - t * α) / 3) :=
        Filter.Tendsto.eventually_lt_const (by linarith) (hlo.sub hμ)
      have hE2 : ∀ᶠ l in atTop, min (t * α - lo0) (hi0 - t * α) / 3 < hi l - t * ∑ j, a l j :=
        Filter.Tendsto.eventually_const_lt (by linarith) (hhi.sub hμ)
      have hcond : lo0 ≤ t * α ∧ t * α ≤ hi0 := ⟨h1.le, h2.le⟩
      rw [if_pos hcond]
      have hg : Tendsto (fun l => 1 - (∑ j, (a l j) ^ 2) / (min (t * α - lo0) (hi0 - t * α) / 3) ^ 2)
          atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds (x := (1:ℝ))).sub (heps (min (t * α - lo0) (hi0 - t * α) / 3))
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg tendsto_const_nhds ?_
        (Eventually.of_forall fun l => Qf_le_one _ ht0 ht1 _ _)
      filter_upwards [hE1, hE2] with l hl1 hl2
      exact Qf_lower _ ht0 ht1 hδ (by linarith) (by linarith)
    · -- hi0 < t * α
      have hδ : 0 < (t * α - hi0) / 3 := by linarith
      have hE : ∀ᶠ l in atTop, hi l - t * ∑ j, a l j < -((t * α - hi0) / 3) :=
        Filter.Tendsto.eventually_lt_const (by linarith) (hhi.sub hμ)
      have hcond : ¬ (lo0 ≤ t * α ∧ t * α ≤ hi0) := fun h => by linarith [h.2]
      rw [if_neg hcond]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (heps ((t * α - hi0) / 3))
        (Eventually.of_forall fun l => Qf_nonneg _ ht0 ht1 _ _) ?_
      filter_upwards [hE] with l hl
      exact Qf_upper _ ht0 ht1 hδ (Or.inr (by linarith))


/-- Combine a set of major players and a set of minor players. -/
def emb {m n : ℕ} (S : Finset (Fin m)) (T : Finset (Fin n)) : Finset (Fin (m + n)) :=
  S.map (Fin.castAddEmb n) ∪ T.map (Fin.natAddEmb m)

theorem castAdd_ne_natAdd' {m n : ℕ} (j : Fin m) (j' : Fin n) :
    Fin.castAdd n j ≠ Fin.natAdd m j' := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem mem_emb_castAdd {m n : ℕ} (S : Finset (Fin m)) (T : Finset (Fin n)) (j : Fin m) :
    Fin.castAdd n j ∈ emb S T ↔ j ∈ S := by
  unfold emb
  simp only [Finset.mem_union, Finset.mem_map, Fin.castAddEmb_apply, Fin.natAddEmb_apply]
  constructor
  · rintro (⟨j', hj', h⟩ | ⟨j', _, h⟩)
    · rw [Fin.castAdd_injective _ _ h] at hj'; exact hj'
    · exact absurd h.symm (castAdd_ne_natAdd' j j')
  · intro h; exact Or.inl ⟨j, h, rfl⟩

theorem mem_emb_natAdd {m n : ℕ} (S : Finset (Fin m)) (T : Finset (Fin n)) (j : Fin n) :
    Fin.natAdd m j ∈ emb S T ↔ j ∈ T := by
  unfold emb
  simp only [Finset.mem_union, Finset.mem_map, Fin.castAddEmb_apply, Fin.natAddEmb_apply]
  constructor
  · rintro (⟨j', _, h⟩ | ⟨j', hj', h⟩)
    · exact absurd h (castAdd_ne_natAdd' j' j)
    · rw [Fin.natAdd_injective _ _ h] at hj'; exact hj'
  · intro h; exact Or.inr ⟨j, h, rfl⟩

theorem card_emb {m n : ℕ} (S : Finset (Fin m)) (T : Finset (Fin n)) :
    (emb S T).card = S.card + T.card := by
  unfold emb
  rw [Finset.card_union_of_disjoint, Finset.card_map, Finset.card_map]
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_map, Fin.castAddEmb_apply, Fin.natAddEmb_apply] at hx hx'
  obtain ⟨j, _, rfl⟩ := hx
  obtain ⟨j', _, h⟩ := hx'
  exact castAdd_ne_natAdd' j j' h.symm

theorem sum_emb {m n : ℕ} (w : Fin m → ℝ) (a : Fin n → ℝ) (S : Finset (Fin m))
    (T : Finset (Fin n)) :
    ∑ j ∈ emb S T, (Fin.append w a) j = ∑ j ∈ S, w j + ∑ j ∈ T, a j := by
  unfold emb
  rw [Finset.sum_union, Finset.sum_map, Finset.sum_map]
  · simp [Fin.append_left, Fin.append_right]
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_map, Fin.castAddEmb_apply, Fin.natAddEmb_apply] at hx hx'
    obtain ⟨j, _, rfl⟩ := hx
    obtain ⟨j', _, h⟩ := hx'
    exact castAdd_ne_natAdd' j j' h.symm

theorem emb_surj {m n : ℕ} (S' : Finset (Fin (m + n))) :
    emb (Finset.univ.filter fun j : Fin m => Fin.castAdd n j ∈ S')
      (Finset.univ.filter fun j : Fin n => Fin.natAdd m j ∈ S') = S' := by
  ext x
  induction x using Fin.addCases with
  | left j => rw [mem_emb_castAdd]; simp
  | right j => rw [mem_emb_natAdd]; simp

theorem sum_reindex {m n : ℕ} (i : Fin m) (g : Finset (Fin (m + n)) → ℝ) :
    ∑ S' ∈ (Finset.univ.erase (Fin.castAdd n i)).powerset, g S' =
      ∑ S ∈ (Finset.univ.erase i).powerset, ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        g (emb S T) := by
  classical
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun x _ => emb x.1 x.2) ?_ ?_ ?_ ?_
  · rintro ⟨S, T⟩ hx
    simp only [Finset.mem_product, Finset.mem_powerset] at hx ⊢
    intro x hxe
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro hxp
    rw [hxp, mem_emb_castAdd] at hxe
    have := hx.1 hxe
    simp at this
  · rintro ⟨S, T⟩ _ ⟨S2, T2⟩ _ h
    simp only at h
    have h1 : S = S2 := by
      ext j
      rw [← mem_emb_castAdd S T j, h, mem_emb_castAdd]
    have h2 : T = T2 := by
      ext j
      rw [← mem_emb_natAdd S T j, h, mem_emb_natAdd]
    rw [h1, h2]
  · intro S' hS'
    refine ⟨(Finset.univ.filter fun j : Fin m => Fin.castAdd n j ∈ S',
      Finset.univ.filter fun j : Fin n => Fin.natAdd m j ∈ S'), ?_, emb_surj S'⟩
    simp only [Finset.mem_product, Finset.mem_powerset, Finset.subset_univ, and_true]
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have := Finset.mem_powerset.1 hS' hj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at this ⊢
    intro h; exact this (by rw [h])
  · intro x _; rfl



theorem ind_diff (c' wi' x y : ℝ) (h : 0 ≤ wi') :
    ((if c' ≤ wi' + (x + y) then (1:ℝ) else 0) - (if c' ≤ x + y then 1 else 0) =
      if c' - x - wi' ≤ y ∧ y < c' - x then 1 else 0) := by
  by_cases h1 : c' ≤ wi' + (x + y) <;> by_cases h2 : c' ≤ x + y <;>
    by_cases h3 : (c' - x - wi' ≤ y ∧ y < c' - x)
  all_goals first
    | (simp only [h1, h2, h3, if_true, if_false]; norm_num; done)
    | (exfalso; linarith [h3.1, h3.2])
    | (exfalso; apply h3; exact ⟨by linarith, by linarith⟩)
    | (exfalso; linarith)

theorem finiteValue_eq {m n : ℕ} (c : ℝ) (w : Fin m → ℝ) (a : Fin n → ℝ) (i : Fin m)
    (hwi : 0 ≤ w i) :
    finiteValue c w a i = ∑ S ∈ (Finset.univ.erase i).powerset,
      ∫ t in (0:ℝ)..1, t ^ S.card * (1 - t) ^ (m - S.card - 1) *
        Qf a t (c - OceanicGames.Interior.wsum w S - w i)
          (c - OceanicGames.Interior.wsum w S) := by
  classical
  unfold finiteValue Supermodularity.Cooperative.ShapleyValue
  rw [sum_reindex]
  apply Finset.sum_congr rfl
  intro S hS
  have hS' : S ⊆ Finset.univ.erase i := Finset.mem_powerset.1 hS
  have hiS : i ∉ S := fun h => by simpa using hS' h
  have hSm : S.card + 1 ≤ m := by
    have h1 := Finset.card_le_card hS'
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] at h1
    have : 0 < m := Fin.pos i
    omega
  have hQ : ∀ t : ℝ, t ^ S.card * (1 - t) ^ (m - S.card - 1) *
      Qf a t (c - OceanicGames.Interior.wsum w S - w i) (c - OceanicGames.Interior.wsum w S) =
      ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        (if c - OceanicGames.Interior.wsum w S - w i ≤ ∑ j ∈ T, a j ∧
          ∑ j ∈ T, a j < c - OceanicGames.Interior.wsum w S then (1:ℝ) else 0) *
        (t ^ (S.card + T.card) * (1 - t) ^ ((m - S.card - 1) + (n - T.card))) := by
    intro t
    unfold Qf bw
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    rw [pow_add, pow_add]
    ring
  simp_rw [hQ]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro T hT
    rw [intervalIntegral.integral_const_mul, beta_int]
    have hTn : T.card ≤ n := by
      have := Finset.card_le_card (Finset.subset_univ T)
      simpa using this
    have e1 : m + n - (S.card + T.card) - 1 = m - S.card - 1 + (n - T.card) := by omega
    have e2 : S.card + T.card + (m - S.card - 1 + (n - T.card)) + 1 = m + n := by omega
    rw [card_emb, e1, e2]
    have hp : Fin.castAdd n i ∉ emb S T := by rw [mem_emb_castAdd]; exact hiS
    have hD : wmGame c (Fin.append w a) (insert (Fin.castAdd n i) (emb S T)) -
        wmGame c (Fin.append w a) (emb S T) =
        if c - OceanicGames.Interior.wsum w S - w i ≤ ∑ j ∈ T, a j ∧
          ∑ j ∈ T, a j < c - OceanicGames.Interior.wsum w S then (1:ℝ) else 0 := by
      unfold wmGame
      rw [Finset.sum_insert hp, sum_emb, Fin.append_left]
      unfold OceanicGames.Interior.wsum
      exact ind_diff c (w i) (∑ j ∈ S, w j) (∑ j ∈ T, a j) hwi
    rw [hD]
    ring
  · intro T _
    apply Continuous.intervalIntegrable
    fun_prop

theorem Qf_continuous {n : ℕ} (a : Fin n → ℝ) (lo hi : ℝ) : Continuous fun t => Qf a t lo hi := by
  unfold Qf bw
  exact continuous_finsetSum _ fun T _ => by fun_prop

theorem term_tendsto (s r : ℕ) {n : ℕ → ℕ} (a : (l : ℕ) → Fin (n l) → ℝ) (ha : ∀ l j, 0 ≤ a l j)
    {α : ℝ} (hα : 0 < α)
    (halim : Tendsto (fun l => ∑ j, a l j) atTop (𝓝 α))
    (hamax : ∀ ε : ℝ, 0 < ε → ∀ᶠ l in atTop, ∀ j, a l j ≤ ε)
    (A B : ℕ → ℝ) {A0 B0 : ℝ} (hA : Tendsto A atTop (𝓝 A0)) (hB : Tendsto B atTop (𝓝 B0)) :
    Tendsto (fun l => ∫ t in (0:ℝ)..1, t ^ s * (1 - t) ^ r * Qf (a l) t (A l) (B l)) atTop
      (𝓝 (∫ t in Set.Icc (0:ℝ) 1 ∩ Set.Icc (A0 / α) (B0 / α), t ^ s * (1 - t) ^ r)) := by
  classical
  have hconv : ∀ l, ∫ t in (0:ℝ)..1, t ^ s * (1 - t) ^ r * Qf (a l) t (A l) (B l) =
      ∫ t in Set.Icc (0:ℝ) 1, t ^ s * (1 - t) ^ r * Qf (a l) t (A l) (B l) := by
    intro l
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  simp only [hconv]
  have hlim : ∫ t in Set.Icc (0:ℝ) 1 ∩ Set.Icc (A0 / α) (B0 / α), t ^ s * (1 - t) ^ r =
      ∫ t in Set.Icc (0:ℝ) 1, t ^ s * (1 - t) ^ r * (if A0 ≤ t * α ∧ t * α ≤ B0 then 1 else 0) := by
    rw [← setIntegral_indicator measurableSet_Icc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t _
    simp only [Set.indicator_apply, Set.mem_Icc, div_le_iff₀ hα, le_div_iff₀ hα]
    split_ifs <;> ring
  rw [hlim]
  refine tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ)) ?_ ?_ ?_ ?_
  · intro l
    refine Continuous.aestronglyMeasurable ?_
    exact (by fun_prop : Continuous fun t : ℝ => t ^ s * (1 - t) ^ r).mul (Qf_continuous _ _ _)
  · exact integrable_const _
  · intro l
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun t ht => ?_)
    have h0 : 0 ≤ t := ht.1
    have h1 : t ≤ 1 := ht.2
    have hq0 := Qf_nonneg (a l) h0 h1 (A l) (B l)
    have hq1 := Qf_le_one (a l) h0 h1 (A l) (B l)
    have hp1 : t ^ s ≤ 1 := pow_le_one₀ h0 h1
    have hp2 : (1 - t) ^ r ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hp3 : 0 ≤ t ^ s * (1 - t) ^ r := mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp3 hq0)]
    have : t ^ s * (1 - t) ^ r ≤ 1 := by nlinarith [pow_nonneg h0 s, pow_nonneg (sub_nonneg.2 h1) r]
    nlinarith
  · have hnull : ∀ᵐ t : ℝ, t ∉ ({A0 / α, B0 / α} : Set ℝ) :=
      (Set.toFinite _).countable.ae_notMem _
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [hnull] with t ht hmem
    have hne1 : t * α ≠ A0 := fun h =>
      ht (Or.inl ((eq_div_iff hα.ne').2 h))
    have hne2 : t * α ≠ B0 := fun h =>
      ht (Or.inr ((eq_div_iff hα.ne').2 h))
    exact (Qf_tendsto a ha halim hamax A B hA hB hmem.1 hmem.2 hne1 hne2).const_mul _


theorem appendix_A3_core {m : ℕ} (c alpha : ℝ) (w : Fin m → ℝ)
    (n : ℕ → ℕ) (cl : ℕ → ℝ) (wl : ℕ → Fin m → ℝ)
    (a : (l : ℕ) → Fin (n l) → ℝ) (i : Fin m)
    (halpha : 0 < alpha)
    (hwl : ∀ l j, 0 ≤ wl l j) (ha : ∀ l j, 0 ≤ a l j)
    (hclim : Tendsto cl atTop (𝓝 c))
    (hwlim : ∀ j, Tendsto (fun l => wl l j) atTop (𝓝 (w j)))
    (halim : Tendsto (fun l => ∑ j, a l j) atTop (𝓝 alpha))
    (hamax : ∀ ε : ℝ, 0 < ε → ∀ᶠ l in atTop, ∀ j, a l j ≤ ε) :
    Tendsto (fun l => finiteValue (cl l) (wl l) (a l) i)
      atTop (𝓝 (limitFormula c alpha w i)) := by
  have h1 : (fun l => finiteValue (cl l) (wl l) (a l) i) = fun l =>
      ∑ S ∈ (Finset.univ.erase i).powerset,
      ∫ t in (0:ℝ)..1, t ^ S.card * (1 - t) ^ (m - S.card - 1) *
        Qf (a l) t (cl l - OceanicGames.Interior.wsum (wl l) S - wl l i)
          (cl l - OceanicGames.Interior.wsum (wl l) S) :=
    funext fun l => finiteValue_eq _ _ _ _ (hwl l i)
  rw [h1]
  unfold limitFormula
  apply tendsto_finset_sum
  intro S _
  have hsum : Tendsto (fun l => OceanicGames.Interior.wsum (wl l) S) atTop
      (𝓝 (OceanicGames.Interior.wsum w S)) :=
    tendsto_finset_sum _ fun j _ => hwlim j
  have hA : Tendsto (fun l => cl l - OceanicGames.Interior.wsum (wl l) S - wl l i) atTop
      (𝓝 (c - OceanicGames.Interior.wsum w S - w i)) :=
    (hclim.sub hsum).sub (hwlim i)
  have hB : Tendsto (fun l => cl l - OceanicGames.Interior.wsum (wl l) S) atTop
      (𝓝 (c - OceanicGames.Interior.wsum w S)) :=
    hclim.sub hsum
  exact term_tendsto S.card (m - S.card - 1) a ha halpha halim hamax _ _ hA hB


end OceanicGames.Limit

open OceanicGames.Limit
open MeasureTheory Set Finset Filter Topology

theorem solution {m : ℕ} (c alpha : ℝ) (w : Fin m → ℝ)
    (n : ℕ → ℕ) (cl : ℕ → ℝ) (wl : ℕ → Fin m → ℝ)
    (a : (l : ℕ) → Fin (n l) → ℝ) (i : Fin m)
    (hc : 0 ≤ c) (halpha : 0 < alpha) (hw : ∀ j, 0 ≤ w j)
    (hwl : ∀ l j, 0 ≤ wl l j) (ha : ∀ l j, 0 ≤ a l j)
    (hclim : Tendsto cl atTop (𝓝 c))
    (hwlim : ∀ j, Tendsto (fun l => wl l j) atTop (𝓝 (w j)))
    (halim : Tendsto (fun l => ∑ j, a l j) atTop (𝓝 alpha))
    (hamax : ∀ ε : ℝ, 0 < ε → ∀ᶠ l in atTop, ∀ j, a l j ≤ ε) :
    Tendsto (fun l => finiteValue (cl l) (wl l) (a l) i)
      atTop (𝓝 (limitFormula c alpha w i)) := by
  exact appendix_A3_core c alpha w n cl wl a i halpha hwl ha hclim hwlim halim hamax
