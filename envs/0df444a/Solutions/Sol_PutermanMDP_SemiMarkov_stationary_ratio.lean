-- Prove2me | solution 1 for PutermanMDP.SemiMarkov.stationary_ratio
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T05:35:36.137409+00:00
-- url     : https://prove2.me/submissions/ca72cfcf-e03f-4515-90f8-6cb5387d7e45

import Mathlib
import Definitions.Def_PutermanMDP_SemiMarkov_Stationary

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace S226M_40d4ce74

open PutermanMDP.SemiMarkov

noncomputable def Tf (i j : ℕ) : ℝ≥0∞ :=
  if i = 0 then (if j = 0 then 1 else 0)
  else (if j = 0 then 1/2 else if j = i + 1 then 1/2 else 0)

noncomputable def T (i : ℕ) : PMF ℕ :=
  PMF.ofFinset (Tf i) {0, i + 1}
    (by
      rw [Finset.sum_pair (by omega)]
      by_cases hi : i = 0
      · subst hi; simp [Tf]
      · simp [Tf, hi, ENNReal.inv_two_add_inv_two])
    (by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      by_cases hi : i = 0
      · simp [Tf, hi, ha.1]
      · simp [Tf, ha.1, ha.2, hi])

noncomputable def rw' (s : ℕ) : ℝ := if s = 0 then 0 else 2 ^ s

noncomputable def M : Model ℕ where
  Action := fun _ => Unit
  action_nonempty := fun _ => ⟨()⟩
  transition := fun s _ => T s
  holding := fun _ _ => Measure.dirac (1 : ℝ≥0)
  holding_probability := fun _ _ => inferInstance
  holding_integrable := fun _ _ => integrable_dirac (by simp)
  reward := fun s _ => rw' s

lemma meanTime_eq (s : ℕ) (a : M.Action s) : meanTime M s a = 1 := by
  simp [meanTime, M, integral_dirac]

noncomputable def d : Rule M where
  action := fun _ => PMF.pure ()
  reward_summable := fun s => by
    change Summable (fun a : Unit => _); exact (hasSum_fintype _).summable
  time_summable := fun s => by
    change Summable (fun a : Unit => _); exact (hasSum_fintype _).summable

lemma ruleReward_eq (s : ℕ) : ruleReward M d s = rw' s := by
  unfold ruleReward
  change ∑' a : Unit, ((PMF.pure ()) a).toReal * rw' s = rw' s
  simp

lemma ruleTime_eq (s : ℕ) : ruleTime M d s = 1 := by
  unfold ruleTime
  simp only [meanTime_eq, mul_one]
  change ∑' a : Unit, ((PMF.pure ()) a).toReal = 1
  simp

lemma embedded_eq (s : ℕ) : embedded M d s = T s := by
  simp [embedded, d, M]

lemma law0 (n : ℕ) : epochLaw M d n 0 = PMF.pure 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [epochLaw, ih, PMF.pure_bind, embedded_eq]
    ext j
    simp [T, Tf, PMF.ofFinset_apply, PMF.pure_apply]

lemma lawS (n s : ℕ) : ∀ j, epochLaw M d n (s + 1) j =
    if j = 0 then ∑ k ∈ Finset.range n, (1/2 : ℝ≥0∞) ^ (k + 1)
    else if j = s + 1 + n then (1/2) ^ n else 0 := by
  induction n with
  | zero =>
    intro j
    simp only [epochLaw, PMF.pure_apply]
    by_cases h0 : j = 0
    · subst h0; simp
    · by_cases h1 : j = s + 1
      · subst h1; simp
      · simp [h0, h1]
  | succ n ih =>
    intro j
    simp only [epochLaw, PMF.bind_apply, embedded_eq, T, PMF.ofFinset_apply]
    simp_rw [ih]
    have hfin : ∀ i ∉ ({0, s + 1 + n} : Finset ℕ),
        (if i = 0 then ∑ k ∈ Finset.range n, (1/2 : ℝ≥0∞) ^ (k + 1)
          else if i = s + 1 + n then (1/2) ^ n else 0) * Tf i j = 0 := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      simp [hi.1, hi.2]
    rw [tsum_eq_sum hfin, Finset.sum_pair (by omega)]
    have hne : s + 1 + n ≠ 0 := by omega
    simp only [if_true, if_neg hne]
    by_cases hj : j = 0
    · subst hj
      simp [Tf, hne, Finset.sum_range_succ, pow_succ]
    · have : Tf 0 j = 0 := by simp [Tf, hj]
      rw [this, mul_zero, zero_add, if_neg hj]
      simp only [Tf, if_neg hne, if_neg hj]
      by_cases h2 : j = s + 1 + n + 1
      · rw [if_pos h2, if_pos (by omega), pow_succ]
      · rw [if_neg h2, if_neg (by omega), mul_zero]

lemma hasSum_half : HasSum (fun j : ℕ => (1/2 : ℝ)^(j+1)) 1 := by
  have := hasSum_geometric_two' 1
  convert this using 1
  funext n
  rw [pow_succ, div_div, mul_comm, ← div_div, div_pow, one_pow]; ring

lemma law_tendsto (s j : ℕ) :
    Tendsto (fun k => (epochLaw M d k s j).toReal) atTop
      (𝓝 (if j = 0 then 1 else 0)) := by
  rcases s with _ | s
  · apply tendsto_const_nhds.congr (fun k => ?_)
    rw [law0, PMF.pure_apply]
    split_ifs <;> simp
  · by_cases hj : j = 0
    · subst hj
      rw [if_pos rfl]
      refine hasSum_half.tendsto_sum_nat.congr (fun k => ?_)
      rw [lawS, if_pos rfl, ENNReal.toReal_sum (fun i _ => by simp)]
      simp
    · rw [if_neg hj]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop j] with k hk
      rw [lawS, if_neg hj, if_neg (by omega)]
      simp

lemma ces (s j : ℕ) :
    Tendsto (fun n => cesaro M d n s j) atTop (𝓝 (if j = 0 then 1 else 0)) := by
  refine (law_tendsto s j).cesaro.congr (fun n => ?_)
  simp [cesaro, div_eq_inv_mul]

lemma limit_eq (s j : ℕ) : limitingMatrix M d s j = if j = 0 then 1 else 0 :=
  (ces s j).liminf_eq

lemma limit_fun (s : ℕ) : limitingMatrix M d s = fun j => if j = 0 then 1 else 0 := by
  funext j; exact limit_eq s j

lemma NE : Nonexplosive M := by
  refine ⟨1/2, 1/2, by norm_num, by norm_num, fun s a => ⟨?_, by norm_num⟩⟩
  simp [M]
  norm_num

lemma P : CesaroProbability M d := by
  refine ⟨fun s j => ?_, fun s j => ?_, fun s => ?_⟩
  · rw [limit_eq]; exact ces s j
  · rw [limit_eq]; split_ifs <;> norm_num
  · rw [limit_fun]; exact hasSum_ite_eq 0 1

lemma E : FiniteEpochMoments M d := by
  intro n s
  simp only [ruleTime_eq, mul_one]
  refine ⟨?_, ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)⟩
  rcases s with _ | s
  · apply summable_of_ne_finset_zero (s := {0})
    intro j hj
    simp only [Finset.mem_singleton] at hj
    rw [law0, PMF.pure_apply, if_neg hj]; simp
  · apply summable_of_ne_finset_zero (s := {0, s + 1 + n})
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    rw [lawS, if_neg hj.1, if_neg hj.2]; simp

lemma L : FiniteLimitMoments M d := by
  intro s
  rw [limit_fun]
  constructor
  · apply summable_of_ne_finset_zero (s := {0})
    intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [hj]
  · apply summable_of_ne_finset_zero (s := {0})
    intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [hj]

lemma ratio1 : limitingRatio M d 1 = 0 := by
  unfold limitingRatio
  rw [limit_fun]
  have : (fun j : ℕ => (if j = 0 then (1:ℝ) else 0) * ruleReward M d j) = fun _ => 0 := by
    funext j
    by_cases hj : j = 0
    · subst hj; simp [ruleReward_eq, rw']
    · simp [hj]
  rw [this, tsum_zero, zero_div]

lemma stepReward (k : ℕ) :
    ∑' j, (epochLaw M d k 1 j).toReal * ruleReward M d j = 2 := by
  have hl : ∀ j, epochLaw M d k 1 j =
      if j = 0 then ∑ i ∈ Finset.range k, (1/2 : ℝ≥0∞) ^ (i + 1)
      else if j = 0 + 1 + k then (1/2) ^ k else 0 := lawS k 0
  rw [tsum_eq_single (0 + 1 + k)]
  · rw [hl, if_neg (by omega), if_pos rfl, ruleReward_eq, rw',
      if_neg (by omega)]
    simp only [ENNReal.toReal_pow]
    rw [show (0 + 1 + k) = k + 1 by omega, pow_succ]
    have : ((1:ℝ≥0∞)/2).toReal = 1/2 := by simp
    rw [this, ← mul_assoc, ← mul_pow]
    norm_num
  · intro j hj
    rw [hl]
    by_cases h0 : j = 0
    · subst h0; simp [ruleReward_eq, rw']
    · rw [if_neg h0, if_neg hj]; simp

lemma stepTime (k : ℕ) :
    ∑' j, (epochLaw M d k 1 j).toReal * ruleTime M d j = 1 := by
  simp only [ruleTime_eq, mul_one]
  rw [← ENNReal.tsum_toReal_eq (fun _ => PMF.apply_ne_top _ _), PMF.tsum_coe]
  simp

lemma rewardRatio_eq (n : ℕ) : rewardRatio M d n 1 = 2 * (n + 1) / n := by
  simp only [rewardRatio, expectedReward, expectedTime, stepReward, stepTime,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast
  ring

end S226M_40d4ce74

open Filter in
open scoped Topology in
open PutermanMDP.SemiMarkov in
theorem solution : ¬ (∀ {S : Type} [Countable S] [Nonempty S]
    (M : Model S) (d : Rule M) (hNE : Nonexplosive M)
    (hP : CesaroProbability M d) (hE : FiniteEpochMoments M d)
    (hL : FiniteLimitMoments M d),
    ((∀ s, Tendsto (fun n => rewardRatio M d n s) atTop
        (𝓝 (limitingRatio M d s))) ∧
      (∀ s, gain M d s = (limitingRatio M d s : EReal))) ∧
    (Unichain M d → ∃ g : ℝ, ∀ s, gain M d s = (g : EReal))) := by
  intro H
  have h1 := (H S226M_40d4ce74.M S226M_40d4ce74.d S226M_40d4ce74.NE S226M_40d4ce74.P
    S226M_40d4ce74.E S226M_40d4ce74.L).1.1 1
  rw [S226M_40d4ce74.ratio1] at h1
  have h2 : (2:ℝ) ≤ 0 := by
    refine ge_of_tendsto h1 ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [S226M_40d4ce74.rewardRatio_eq]
    have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    rw [le_div_iff₀ (by linarith)]
    linarith
  norm_num at h2
