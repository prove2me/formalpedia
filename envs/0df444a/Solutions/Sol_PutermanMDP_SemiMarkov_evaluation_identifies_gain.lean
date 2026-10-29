-- Prove2me | solution 1 for PutermanMDP.SemiMarkov.evaluation_identifies_gain
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T05:14:58.705228+00:00
-- url     : https://prove2.me/submissions/4e517570-3f38-484d-a359-b4e538ca7424

import Mathlib
import Definitions.Def_PutermanMDP_SemiMarkov_Stationary

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace S226A

open PutermanMDP.SemiMarkov

noncomputable def s226a_f (s : ℕ) (j : ℕ) : ℝ≥0∞ :=
  if j = 0 then 1/2 else if j = s + 1 then 1/2 else 0

noncomputable def s226a_T (s : ℕ) : PMF ℕ :=
  PMF.ofFinset (s226a_f s) {0, s + 1}
    (by
      rw [Finset.sum_pair (by omega)]
      simp [s226a_f, ENNReal.inv_two_add_inv_two])
    (by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      simp [s226a_f, ha.1, ha.2])

noncomputable def s226a_M : Model ℕ where
  Action := fun _ => Unit
  action_nonempty := fun _ => ⟨()⟩
  transition := fun s _ => s226a_T s
  holding := fun _ _ => Measure.dirac (1 : ℝ≥0)
  holding_probability := fun _ _ => inferInstance
  holding_integrable := fun _ _ => integrable_dirac (by simp)
  reward := fun _ _ => 0

lemma s226a_meanTime (s : ℕ) (a : s226a_M.Action s) : meanTime s226a_M s a = 1 := by
  simp [meanTime, s226a_M, integral_dirac]

noncomputable def s226a_d : Rule s226a_M where
  action := fun _ => PMF.pure ()
  reward_summable := fun s => by
    change Summable (fun a : Unit => _); exact (hasSum_fintype _).summable
  time_summable := fun s => by
    change Summable (fun a : Unit => _); exact (hasSum_fintype _).summable

lemma s226a_ruleReward (s : ℕ) : ruleReward s226a_M s226a_d s = 0 := by
  simp [ruleReward, s226a_M]

lemma s226a_ruleTime (s : ℕ) : ruleTime s226a_M s226a_d s = 1 := by
  unfold ruleTime
  simp only [s226a_meanTime, mul_one]
  change ∑' a : Unit, ((PMF.pure ()) a).toReal = 1
  simp

lemma s226a_embedded (s : ℕ) : embedded s226a_M s226a_d s = s226a_T s := by
  simp [embedded, s226a_d, s226a_M]

lemma s226a_step0 (n s : ℕ) : epochLaw s226a_M s226a_d (n + 1) s 0 = 1/2 := by
  simp only [epochLaw, PMF.bind_apply, s226a_embedded, s226a_T, PMF.ofFinset_apply, s226a_f,
    ↓reduceIte]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

lemma s226a_stepS (n s j : ℕ) :
    epochLaw s226a_M s226a_d (n + 1) s (j + 1) = 1/2 * epochLaw s226a_M s226a_d n s j := by
  simp only [epochLaw, PMF.bind_apply, s226a_embedded, s226a_T, PMF.ofFinset_apply, s226a_f]
  rw [tsum_eq_single j]
  · simp [mul_comm]
  · intro i hi
    have : j + 1 ≠ i + 1 := by omega
    simp only [this, ↓reduceIte, Nat.add_one_ne_zero, mul_zero]

lemma s226a_law (n s j : ℕ) : epochLaw s226a_M s226a_d n s j =
    if j < n then (1/2 : ℝ≥0∞)^(j+1) else if j = s + n then (1/2)^n else 0 := by
  induction n generalizing j with
  | zero =>
    simp only [epochLaw, PMF.pure_apply]
    by_cases h : j = s <;> simp [h]
  | succ n ih =>
    cases j with
    | zero => rw [s226a_step0]; simp
    | succ j =>
      rw [s226a_stepS, ih]
      by_cases h1 : j < n
      · simp [h1, pow_succ]; ring
      · by_cases h2 : j = s + n
        · subst h2
          have : ¬ s + n + 1 < n + 1 := by omega
          rw [if_neg h1, if_pos rfl, if_neg this, if_pos (by omega), pow_succ, mul_comm]
        · have h3 : ¬ j + 1 < n + 1 := by omega
          have h4 : j + 1 ≠ s + (n + 1) := by omega
          simp [h1, h2, h3, h4]

lemma s226a_cesaro (s j : ℕ) :
    Tendsto (fun n => cesaro s226a_M s226a_d n s j) atTop (𝓝 ((1/2 : ℝ)^(j+1))) := by
  have hu : Tendsto (fun k => (epochLaw s226a_M s226a_d k s j).toReal) atTop
      (𝓝 ((1/2 : ℝ)^(j+1))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop j] with k hk
    rw [s226a_law, if_pos hk]
    simp
  have := hu.cesaro
  refine this.congr (fun n => ?_)
  simp [cesaro, div_eq_inv_mul]

lemma s226a_limit (s j : ℕ) : limitingMatrix s226a_M s226a_d s j = (1/2 : ℝ)^(j+1) :=
  (s226a_cesaro s j).liminf_eq

lemma s226a_hasSum : HasSum (fun j : ℕ => (1/2 : ℝ)^(j+1)) 1 := by
  have := hasSum_geometric_two' 1
  convert this using 1
  funext n
  rw [pow_succ, div_div, mul_comm, ← div_div, div_pow, one_pow]; ring

lemma s226a_summable_law (n s : ℕ) :
    Summable (fun j => (epochLaw s226a_M s226a_d n s j).toReal) :=
  ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)

noncomputable def s226a_h (s : ℕ) : ℝ := 2 ^ (s + 1) - 2

lemma s226a_T_toReal (s j : ℕ) : (s226a_T s j).toReal * s226a_h j =
    if j = 0 then 0 else if j = s + 1 then (1/2) * s226a_h (s+1) else 0 := by
  simp only [s226a_T, PMF.ofFinset_apply, s226a_f]
  by_cases h0 : j = 0
  · subst h0; simp [s226a_h]
  · by_cases h1 : j = s + 1
    · subst h1; simp
    · simp [h0, h1]

lemma s226a_eq : EvaluationEquation s226a_M s226a_d (fun _ => (1 : ℝ)) s226a_h := by
  intro s
  simp only [s226a_embedded, s226a_ruleReward, s226a_ruleTime, s226a_T_toReal]
  have hfin : ∀ j ∉ ({s + 1} : Finset ℕ),
      (if j = 0 then (0:ℝ) else if j = s + 1 then 1/2 * s226a_h (s+1) else 0) = 0 := by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [hj]
  refine ⟨summable_of_ne_finset_zero hfin, ?_⟩
  rw [tsum_eq_sum hfin]
  simp only [Finset.sum_singleton, if_neg (Nat.succ_ne_zero s), if_true]
  simp only [s226a_h]
  ring

lemma s226a_gain (s : ℕ) : gain s226a_M s226a_d s = 0 := by
  have : ∀ n, rewardRatio s226a_M s226a_d n s = 0 := by
    intro n
    simp [rewardRatio, expectedReward, s226a_ruleReward]
  simp [gain, this]

lemma s226a_NE : Nonexplosive s226a_M := by
  refine ⟨1/2, 1/2, by norm_num, by norm_num, fun s a => ⟨?_, by norm_num⟩⟩
  simp [s226a_M]
  norm_num

lemma s226a_U : Unichain s226a_M s226a_d := by
  refine ⟨⟨0, ?_⟩, fun s j _ _ => ⟨j + 1, ?_⟩⟩
  · unfold Recurrent
    refine top_le_iff.mp ?_
    rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) (c := 1/2) (by simp)]
    refine ENNReal.tsum_le_tsum (fun n => ?_)
    rw [s226a_law]
    rcases n with _ | n
    · simp
    · simp
  · rw [s226a_law, if_pos (by omega)]
    exact ENNReal.pow_pos (by norm_num) _

lemma s226a_P : CesaroProbability s226a_M s226a_d := by
  refine ⟨fun s j => ?_, fun s j => ?_, fun s => ?_⟩
  · rw [s226a_limit]; exact s226a_cesaro s j
  · rw [s226a_limit]; positivity
  · have : limitingMatrix s226a_M s226a_d s = fun j => (1/2 : ℝ)^(j+1) := by
      funext j; exact s226a_limit s j
    rw [this]; exact s226a_hasSum

lemma s226a_E : FiniteEpochMoments s226a_M s226a_d := by
  intro n s
  simp only [s226a_ruleReward, s226a_ruleTime, mul_zero, mul_one]
  exact ⟨summable_zero, s226a_summable_law n s⟩

end S226A

open PutermanMDP.SemiMarkov in
theorem solution : ¬ (∀ {S : Type} [Countable S] [Nonempty S]
    (M : Model S) (d : Rule M) (hNE : Nonexplosive M)
    (hU : Unichain M d) (hP : CesaroProbability M d)
    (hE : FiniteEpochMoments M d)
    (g : ℝ) (h : S → ℝ) (hEq : EvaluationEquation M d (fun _ => g) h),
    ∀ s, gain M d s = (g : EReal)) := by
  intro H
  have := H S226A.s226a_M S226A.s226a_d S226A.s226a_NE S226A.s226a_U S226A.s226a_P
    S226A.s226a_E 1 S226A.s226a_h S226A.s226a_eq 0
  rw [S226A.s226a_gain] at this
  norm_num at this
