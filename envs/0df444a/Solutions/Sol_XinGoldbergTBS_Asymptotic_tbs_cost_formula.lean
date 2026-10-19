-- Prove2me | solution 1 for XinGoldbergTBS.Asymptotic.tbs_cost_formula
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T09:17:09.11558+00:00
-- url     : https://prove2.me/submissions/257462c6-8517-44e7-a621-45a4e96ab5d8

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Constants
import Definitions.Def_XinGoldbergTBS_Asymptotic_RandomWalk

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace XGCF

open XinGoldbergTBS.Asymptotic

/-! ## Dynamics of the TBS policy -/

/-- Expedited position read off a state at period `t`. -/
def EPos (L₀ L t : ℕ) (s : State) : ℝ := expeditedPosition (observe L₀ L t s)

lemma filter_sum (L₀ L : ℕ) (hL : L₀ < L) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin L => i.val ≤ L₀), f i.val =
      ∑ i ∈ Finset.range (L₀ + 1), f i := by
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun i => if i ≤ L₀ then f i else 0),
    ← Finset.sum_filter]
  congr 1
  ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega

lemma epos_eq (L₀ L t : ℕ) (hL : L₀ < L) (s : State) :
    EPos L₀ L t s = s.2.2 + ∑ i ∈ Finset.range L₀, s.2.1 ((t : ℤ) - L₀ + (i : ℤ)) +
      ∑ i ∈ Finset.range (L₀ + 1), s.1 ((t : ℤ) - L + (i : ℤ)) := by
  unfold EPos expeditedPosition observe
  simp only
  rw [Fin.sum_univ_eq_sum_range (fun i => s.2.1 ((t : ℤ) - L₀ + (i : ℤ))),
    filter_sum L₀ L hL (fun i => s.1 ((t : ℤ) - L + (i : ℤ)))]

lemma epos_step (L₀ L t : ℕ) (hL : L₀ + 1 < L) (a : ℝ≥0 × ℝ≥0) (d : ℝ) (s : State) :
    EPos L₀ L (t + 1) (step L₀ L t a d s) =
      EPos L₀ L t s + a.2 - d + s.1 ((t : ℤ) - L + L₀ + 1) := by
  rw [epos_eq L₀ L (t + 1) (by omega), epos_eq L₀ L t (by omega)]
  simp only [step]
  set qR := Function.update s.1 (t : ℤ) (a.1 : ℝ) with hqR
  set qE := Function.update s.2.1 (t : ℤ) (a.2 : ℝ) with hqE
  -- express part
  have hE : qE ((t : ℤ) - L₀) + ∑ i ∈ Finset.range L₀, qE (((t + 1 : ℕ) : ℤ) - L₀ + (i : ℤ)) =
      ∑ i ∈ Finset.range L₀, s.2.1 ((t : ℤ) - L₀ + (i : ℤ)) + a.2 := by
    have h1 : qE ((t : ℤ) - L₀) + ∑ i ∈ Finset.range L₀, qE (((t + 1 : ℕ) : ℤ) - L₀ + (i : ℤ)) =
        ∑ i ∈ Finset.range (L₀ + 1), qE ((t : ℤ) - L₀ + (i : ℤ)) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1; ring
    rw [h1, Finset.sum_range_succ]
    have h2 : qE ((t : ℤ) - L₀ + (L₀ : ℤ)) = a.2 := by simp [hqE]
    rw [h2]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    rw [hqE, Function.update_of_ne]; omega
  -- regular part
  have hR : qR ((t : ℤ) - L) + ∑ i ∈ Finset.range (L₀ + 1), qR (((t + 1 : ℕ) : ℤ) - L + (i : ℤ)) =
      ∑ i ∈ Finset.range (L₀ + 1), s.1 ((t : ℤ) - L + (i : ℤ)) + s.1 ((t : ℤ) - L + L₀ + 1) := by
    have h1 : qR ((t : ℤ) - L) + ∑ i ∈ Finset.range (L₀ + 1), qR (((t + 1 : ℕ) : ℤ) - L + (i : ℤ)) =
        ∑ i ∈ Finset.range (L₀ + 1 + 1), qR ((t : ℤ) - L + (i : ℤ)) := by
      rw [Finset.sum_range_succ' _ (L₀ + 1)]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1; ring
    rw [h1, Finset.sum_range_succ]
    have h3 : ∀ i ∈ Finset.range (L₀ + 1 + 1), qR ((t : ℤ) - L + (i : ℤ)) = s.1 ((t : ℤ) - L + (i : ℤ)) := by
      intro i hi
      have := Finset.mem_range.1 hi
      rw [hqR, Function.update_of_ne]; omega
    rw [Finset.sum_congr rfl (fun i hi => h3 i (Finset.mem_range.2 (by
      have := Finset.mem_range.1 hi; omega))), h3 (L₀ + 1) (by simp)]
    congr 2; push_cast; ring
  linarith

/-- Initial expedited position `x₀ = -∑_{i<Ĝ} D'_i`. -/
def x0 (ω : Sample) : ℝ := -∑ i ∈ Finset.range ω.2.2, ω.2.1 i

/-- Regular arrival entering the expedited position at step `n → n+1`. -/
def rho (L₀ L : ℕ) (r : ℝ) (n : ℕ) : ℝ := if L ≤ n + L₀ + 1 then r else 0

/-- `P n = Î_{n+1}`: expedited position (before ordering) in period `n+1`. -/
def P (L₀ L : ℕ) (r S : ℝ) (ω : Sample) : ℕ → ℝ
  | 0 => x0 ω
  | n + 1 => max S (P L₀ L r S ω n) - ω.1 n + rho L₀ L r n

/-- Express order `q^E_{n+1}`. -/
def q (L₀ L : ℕ) (r S : ℝ) (ω : Sample) (n : ℕ) : ℝ := max S (P L₀ L r S ω n) - P L₀ L r S ω n

lemma q_nonneg (L₀ L : ℕ) (r S : ℝ) (ω : Sample) (n : ℕ) : 0 ≤ q L₀ L r S ω n := by
  unfold q; linarith [le_max_right S (P L₀ L r S ω n)]

lemma sim (L₀ L : ℕ) (hL : L₀ + 1 < L) (r S : ℝ) (hr0 : 0 ≤ r) (ω : Sample) (n : ℕ) :
    (∀ k : ℤ, (run (tbsPolicy L₀ L r S) ω n).1 k = if 1 ≤ k ∧ k ≤ n then r else 0) ∧
    (∀ k : ℤ, (run (tbsPolicy L₀ L r S) ω n).2.1 k =
      if 1 ≤ k ∧ k ≤ n then q L₀ L r S ω (k - 1).toNat else 0) ∧
    EPos L₀ L (n + 1) (run (tbsPolicy L₀ L r S) ω n) = P L₀ L r S ω n := by
  induction n with
  | zero =>
    refine ⟨fun k => ?_, fun k => ?_, ?_⟩
    · simp only [run, initState]; split_ifs with h
      · omega
      · rfl
    · simp only [run, initState]; split_ifs with h
      · omega
      · rfl
    · rw [epos_eq L₀ L _ (by omega)]
      simp [run, initState, P, x0]
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hf : (tbsPolicy L₀ L r S).f (n + 1) (observe L₀ L (n + 1) (run (tbsPolicy L₀ L r S) ω n)) =
        (r.toNNReal, (S - P L₀ L r S ω n).toNNReal) := by
      show (r.toNNReal, (S - EPos L₀ L (n + 1) (run (tbsPolicy L₀ L r S) ω n)).toNNReal) = _
      rw [h3]
    have hrun : run (tbsPolicy L₀ L r S) ω (n + 1) =
        step L₀ L (n + 1) (r.toNNReal, (S - P L₀ L r S ω n).toNNReal) (ω.1 n)
          (run (tbsPolicy L₀ L r S) ω n) := by
      rw [run, hf]
    have hqn : (((S - P L₀ L r S ω n).toNNReal : ℝ≥0) : ℝ) = q L₀ L r S ω n := by
      rw [Real.coe_toNNReal']; unfold q
      rcases le_total S (P L₀ L r S ω n) with h | h
      · rw [max_eq_right h, max_eq_right (by linarith)]; ring
      · rw [max_eq_left h, max_eq_left (by linarith)]
    refine ⟨fun k => ?_, fun k => ?_, ?_⟩
    · rw [hrun]; simp only [step, Function.update_apply]
      split_ifs with ha hb hb
      · rw [Real.coe_toNNReal _ hr0]
      · push_cast at ha hb; omega
      · rw [h1 k, if_pos (by push_cast at ha hb; omega)]
      · rw [h1 k, if_neg (by push_cast at ha hb; omega)]
    · rw [hrun]; simp only [step, Function.update_apply]
      split_ifs with ha hb hb
      · rw [hqn, ha]; congr 1; omega
      · push_cast at ha hb; omega
      · rw [h2 k, if_pos (by push_cast at ha hb; omega)]
      · rw [h2 k, if_neg (by push_cast at ha hb; omega)]
    · rw [hrun, show n + 1 + 1 = (n + 1) + 1 from rfl, epos_step L₀ L (n + 1) hL, h3]
      simp only
      rw [hqn, h1]
      show _ = max S (P L₀ L r S ω n) - ω.1 n + rho L₀ L r n
      unfold q rho
      have e : ((n + 1 : ℕ) : ℤ) - L + L₀ + 1 = (n : ℤ) + 2 - L + L₀ := by push_cast; ring
      rw [e]
      by_cases hc : L ≤ n + L₀ + 1
      · rw [if_pos (by omega), if_pos hc]; ring
      · rw [if_neg (by omega), if_neg hc]; ring

lemma P_succ (L₀ L : ℕ) (r S : ℝ) (ω : Sample) (n : ℕ) :
    P L₀ L r S ω (n + 1) = P L₀ L r S ω n + q L₀ L r S ω n - ω.1 n + rho L₀ L r n := by
  simp only [P, q]; ring

lemma P_add (L₀ L : ℕ) (r S : ℝ) (ω : Sample) (m k : ℕ) :
    P L₀ L r S ω (m + k) = P L₀ L r S ω m +
      ∑ j ∈ Finset.range k, (q L₀ L r S ω (m + j) - ω.1 (m + j) + rho L₀ L r (m + j)) := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, P_succ, ih, Finset.sum_range_succ]; ring

lemma inv_formula (L₀ L : ℕ) (hL : L₀ + 1 < L) (r S : ℝ) (hr0 : 0 ≤ r) (ω : Sample) (m : ℕ) :
    (run (tbsPolicy L₀ L r S) ω (m + L₀ + 1)).2.2 =
      max S (P L₀ L r S ω m) - ∑ j : Fin (L₀ + 1), ω.1 (m + j) := by
  obtain ⟨h1, h2, h3⟩ := sim L₀ L hL r S hr0 ω (m + L₀ + 1)
  rw [epos_eq L₀ L _ (by omega)] at h3
  have hP := P_add L₀ L r S ω m (L₀ + 1)
  rw [show m + (L₀ + 1) = m + L₀ + 1 by ring] at hP
  rw [hP] at h3
  -- express part of the expedited position
  have hx : ∑ i ∈ Finset.range L₀, (run (tbsPolicy L₀ L r S) ω (m + L₀ + 1)).2.1
      (((m + L₀ + 1 + 1 : ℕ) : ℤ) - L₀ + (i : ℤ)) = ∑ i ∈ Finset.range L₀, q L₀ L r S ω (m + 1 + i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    rw [h2, if_pos (by push_cast; omega)]
    congr 1; omega
  have hy : ∑ i ∈ Finset.range (L₀ + 1), (run (tbsPolicy L₀ L r S) ω (m + L₀ + 1)).1
      (((m + L₀ + 1 + 1 : ℕ) : ℤ) - L + (i : ℤ)) = ∑ i ∈ Finset.range (L₀ + 1), rho L₀ L r (m + i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    rw [h1]; unfold rho
    by_cases hc : L ≤ m + i + L₀ + 1
    · rw [if_pos (by push_cast; omega), if_pos hc]
    · rw [if_neg (by push_cast; omega), if_neg hc]
  rw [hx, hy] at h3
  have hq2 : ∑ x ∈ Finset.range (L₀ + 1), q L₀ L r S ω (m + x) =
      ∑ i ∈ Finset.range L₀, q L₀ L r S ω (m + 1 + i) + q L₀ L r S ω m := by
    rw [Finset.sum_range_succ']
    congr 1
    exact Finset.sum_congr rfl fun i _ => by congr 1; ring
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hq2] at h3
  rw [Fin.sum_univ_eq_sum_range (fun j => ω.1 (m + j))]
  have hqm : q L₀ L r S ω m = max S (P L₀ L r S ω m) - P L₀ L r S ω m := rfl
  linarith

lemma qE_formula (L₀ L : ℕ) (hL : L₀ + 1 < L) (r S : ℝ) (hr0 : 0 ≤ r) (ω : Sample) (m : ℕ) :
    (run (tbsPolicy L₀ L r S) ω (m + L₀ + 1)).2.1 (((m + L₀ + 1 : ℕ) : ℤ) - L₀) = q L₀ L r S ω m := by
  rw [(sim L₀ L hL r S hr0 ω (m + L₀ + 1)).2.1, if_pos (by push_cast; omega)]
  congr 1; omega

lemma cost_formula (κ : Costs) (L₀ L : ℕ) (hL : L₀ + 1 < L) (r S : ℝ) (hr0 : 0 ≤ r)
    (ω : Sample) (m : ℕ) :
    periodCost κ (tbsPolicy L₀ L r S) ω (m + L₀ + 1) =
      ENNReal.ofReal (κ.c * q L₀ L r S ω m) +
        ENNReal.ofReal (G κ (max S (P L₀ L r S ω m) - ∑ j : Fin (L₀ + 1), ω.1 (m + j))) := by
  unfold periodCost
  rw [qE_formula L₀ L hL r S hr0 ω m, inv_formula L₀ L hL r S hr0 ω m]

lemma P_local (L₀ L : ℕ) (r S : ℝ) (ω ω' : Sample) (h2 : ω.2 = ω'.2) (m : ℕ)
    (h1 : ∀ n < m, ω.1 n = ω'.1 n) : P L₀ L r S ω m = P L₀ L r S ω' m := by
  induction m with
  | zero => simp [P, x0, h2]
  | succ m ih =>
    simp only [P]
    rw [ih (fun n hn => h1 n (by omega)), h1 m (by omega)]

/-! ## Measure-theoretic infrastructure (from Sol_pv_82fe7a5f) -/

lemma ae_nonneg (μ : DemandLaw) : ∀ᵐ d ∂μ.law, 0 ≤ d := by
  have h := μ.nonneg
  rw [measure_eq_zero_iff_ae_notMem] at h
  filter_upwards [h] with d hd
  simpa using hd

lemma G_nonneg (κ : Costs) (z : ℝ) : 0 ≤ G κ z := by
  unfold G
  have := κ.h_pos; have := κ.b_pos
  positivity

lemma G_ge (κ : Costs) (z : ℝ) : min κ.b κ.h * |z| ≤ G κ z := by
  unfold G
  have hb := min_le_left κ.b κ.h
  have hh := min_le_right κ.b κ.h
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz, max_eq_left hz, max_eq_right (by linarith : -z ≤ 0)]
    nlinarith
  · rw [abs_of_nonpos hz, max_eq_right hz, max_eq_left (by linarith : 0 ≤ -z)]
    nlinarith

lemma G_le (κ : Costs) (z : ℝ) : G κ z ≤ max κ.b κ.h * |z| := by
  unfold G
  have hb := le_max_left κ.b κ.h
  have hh := le_max_right κ.b κ.h
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz, max_eq_left hz, max_eq_right (by linarith : -z ≤ 0)]
    nlinarith
  · rw [abs_of_nonpos hz, max_eq_right hz, max_eq_left (by linarith : 0 ≤ -z)]
    nlinarith

lemma G_lip (κ : Costs) (a c : ℝ) : G κ a ≤ G κ c + max κ.b κ.h * |a - c| := by
  unfold G
  have hb := le_max_left κ.b κ.h
  have hh := le_max_right κ.b κ.h
  have hbp := κ.b_pos
  have hhp := κ.h_pos
  have h1 := le_abs_self (a - c)
  have h2 := neg_abs_le (a - c)
  have h3 := abs_nonneg (a - c)
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 c with hc | hc
  · rw [max_eq_left ha, max_eq_right (by linarith : -a ≤ 0), max_eq_left hc,
      max_eq_right (by linarith : -c ≤ 0)]
    nlinarith
  · rw [max_eq_left ha, max_eq_right (by linarith : -a ≤ 0), max_eq_right hc,
      max_eq_left (by linarith : 0 ≤ -c)]
    nlinarith
  · rw [max_eq_right ha, max_eq_left (by linarith : 0 ≤ -a), max_eq_left hc,
      max_eq_right (by linarith : -c ≤ 0)]
    nlinarith
  · rw [max_eq_right ha, max_eq_left (by linarith : 0 ≤ -a), max_eq_right hc,
      max_eq_left (by linarith : 0 ≤ -c)]
    nlinarith

lemma continuous_G (κ : Costs) : Continuous (G κ) := by
  unfold G
  exact (continuous_const.mul (continuous_id.max continuous_const)).add
    (continuous_const.mul (continuous_neg.max continuous_const))

instance sumLaw_isProb (μ : DemandLaw) (L₀ : ℕ) : IsProbabilityMeasure (sumLaw μ L₀) := by
  unfold sumLaw; infer_instance

lemma integrable_coord (μ : DemandLaw) (L₀ : ℕ) (i : Fin (L₀ + 1)) :
    Integrable (fun y : Fin (L₀ + 1) → ℝ => y i) (sumLaw μ L₀) := by
  unfold sumLaw
  exact integrable_comp_eval (μ := fun _ : Fin (L₀ + 1) => μ.law) (f := fun d : ℝ => d) μ.integrable

lemma integrable_shift (μ : DemandLaw) (L₀ : ℕ) (x : ℝ) :
    Integrable (fun y : Fin (L₀ + 1) → ℝ => x - ∑ i, y i) (sumLaw μ L₀) :=
  (integrable_const x).sub (integrable_finsetSum _ fun i _ => integrable_coord μ L₀ i)

lemma integrable_G_sum (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (x : ℝ) :
    Integrable (fun y : Fin (L₀ + 1) → ℝ => G κ (x - ∑ i, y i)) (sumLaw μ L₀) := by
  have hs := integrable_shift μ L₀ x
  refine Integrable.mono' (hs.norm.const_mul (max κ.b κ.h)) ?_ ?_
  · exact ((continuous_G κ).measurable.comp_aemeasurable hs.aemeasurable).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (G_nonneg _ _), Real.norm_eq_abs]
      exact G_le κ _

instance ghat_isProb : IsProbabilityMeasure ghatLaw := by
  constructor
  unfold ghatLaw
  rw [Measure.sum_apply _ MeasurableSet.univ]
  have h : ∀ i : ℕ, ((2 : ℝ≥0∞) ^ (i + 1))⁻¹ = 2⁻¹ * (2⁻¹) ^ i := by
    intro i; rw [ENNReal.inv_pow, pow_succ, mul_comm]
  calc _ = ∑' i : ℕ, ((2 : ℝ≥0∞) ^ (i + 1))⁻¹ := by simp
    _ = 1 := by
      simp only [h]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
        ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

instance pathLaw_isProb (μ : DemandLaw) : IsProbabilityMeasure (pathLaw μ) := by
  unfold pathLaw; infer_instance

instance sampleLaw_isProb (μ : DemandLaw) : IsProbabilityMeasure (sampleLaw μ) := by
  unfold sampleLaw; infer_instance

/-- Replace the coordinates `m ≤ n < m + k` of `p` by those of `y`. -/
def mix (m k : ℕ) (p y : Path) : Path := fun n => if m ≤ n ∧ n < m + k then y n else p n

lemma measurable_mix (m k : ℕ) : Measurable (fun q : Path × Path => mix m k q.1 q.2) := by
  refine measurable_pi_lambda _ fun n => ?_
  by_cases h : m ≤ n ∧ n < m + k
  · simp only [mix, h, and_self, if_true]; fun_prop
  · simp only [mix, h, if_false]; fun_prop

lemma mp_mix (μ : DemandLaw) (m k : ℕ) :
    MeasurePreserving (fun q : Path × Path => mix m k q.1 q.2)
      ((pathLaw μ).prod (pathLaw μ)) (pathLaw μ) := by
  refine ⟨measurable_mix m k, ?_⟩
  conv_rhs => rw [pathLaw]
  apply Measure.eq_infinitePi
  intro s t ht
  classical
  rw [Measure.map_apply (measurable_mix m k) (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  have hpre : (fun q : Path × Path => mix m k q.1 q.2) ⁻¹' (Set.pi (↑s) t) =
      (Set.pi ↑(s.filter (fun i => ¬ (m ≤ i ∧ i < m + k))) t) ×ˢ
        (Set.pi ↑(s.filter (fun i => m ≤ i ∧ i < m + k)) t) := by
    ext ⟨p, y⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.coe_filter, Set.mem_setOf_eq,
      Finset.mem_coe, mix]
    constructor
    · intro h
      exact ⟨fun i ⟨hi, hw⟩ => by simpa [hw] using h i hi,
        fun i ⟨hi, hw⟩ => by simpa [hw] using h i hi⟩
    · rintro ⟨h1, h2⟩ i hi
      by_cases hw : m ≤ i ∧ i < m + k
      · simpa [hw] using h2 i ⟨hi, hw⟩
      · simpa [hw] using h1 i ⟨hi, hw⟩
  rw [hpre, Measure.prod_prod]
  unfold pathLaw
  rw [Measure.infinitePi_pi _ (fun i _ => ht i), Measure.infinitePi_pi _ (fun i _ => ht i), mul_comm,
    Finset.prod_filter_mul_prod_filter_not]

/-- Reading finitely many distinct coordinates of an i.i.d. path gives the product law. -/
lemma mp_idx (μ : DemandLaw) (k : ℕ) (σ : Fin k → ℕ) (hσ : Function.Injective σ) :
    MeasurePreserving (fun p : Path => fun j : Fin k => p (σ j))
      (pathLaw μ) (Measure.pi fun _ : Fin k => μ.law) := by
  refine ⟨by fun_prop, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  classical
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  set T : ℕ → Set ℝ := fun n => if h : ∃ j, σ j = n then s h.choose else Set.univ with hTdef
  have hT : ∀ j : Fin k, T (σ j) = s j := by
    intro j
    have hex : ∃ j', σ j' = σ j := ⟨j, rfl⟩
    simp only [hTdef, dif_pos hex]
    rw [hσ hex.choose_spec]
  have hpre : (fun p : Path => fun j : Fin k => p (σ j)) ⁻¹' Set.univ.pi s =
      Set.pi ↑(Finset.univ.image σ) T := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_pi, Finset.coe_image, Finset.coe_univ,
      Set.image_univ, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, hT]
    exact ⟨fun h a => h a (Set.mem_univ _), fun h a _ => h a⟩
  have hTm : ∀ n, MeasurableSet (T n) := by
    intro n; simp only [hTdef]; split_ifs
    · exact hs _
    · exact MeasurableSet.univ
  rw [hpre]
  unfold pathLaw
  rw [Measure.infinitePi_pi _ (fun n _ => hTm n),
    Finset.prod_image (fun a _ b _ h => hσ h)]
  exact Finset.prod_congr rfl fun j _ => by rw [hT j]

lemma mp_window (μ : DemandLaw) (L₀ m : ℕ) :
    MeasurePreserving (fun p : Path => fun j : Fin (L₀ + 1) => p (m + j))
      (pathLaw μ) (sumLaw μ L₀) :=
  mp_idx μ (L₀ + 1) (fun j => m + j) (fun a b h => Fin.ext (by simpa using h))

lemma lintegral_mix (μ : DemandLaw) (m k : ℕ) {f : Sample → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f ω ∂sampleLaw μ =
      ∫⁻ ω, ∫⁻ y, f (mix m k ω.1 y, ω.2) ∂pathLaw μ ∂sampleLaw μ := by
  have hg : Measurable (fun q : Sample × Path => f (mix m k q.1.1 q.2, q.1.2)) :=
    hf.comp (((measurable_mix m k).comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
      measurable_fst.snd)
  have hF : Measurable (fun p : Path => ∫⁻ r, f (p, r) ∂((pathLaw μ).prod ghatLaw)) :=
    hf.lintegral_prod_right'
  unfold sampleLaw
  have hFm : Measurable (fun a : Path × Path =>
      ∫⁻ r, f (mix m k a.1 a.2, r) ∂((pathLaw μ).prod ghatLaw)) := hF.comp (measurable_mix m k)
  rw [lintegral_prod _ hf.aemeasurable, lintegral_prod _ hg.lintegral_prod_right'.aemeasurable,
    ← (mp_mix μ m k).lintegral_comp hF, lintegral_prod _ hFm.aemeasurable]
  refine lintegral_congr fun p => ?_
  simp only
  refine lintegral_lintegral_swap ?_
  exact (hf.comp (((measurable_mix m k).comp (measurable_const.prodMk measurable_fst)).prodMk
    measurable_snd)).aemeasurable

lemma mp_fst (μ : DemandLaw) : MeasurePreserving Prod.fst (sampleLaw μ) (pathLaw μ) :=
  ⟨measurable_fst, by unfold sampleLaw; rw [Measure.map_fst_prod, measure_univ, one_smul]⟩

lemma mp_snd (μ : DemandLaw) :
    MeasurePreserving Prod.snd (sampleLaw μ) ((pathLaw μ).prod ghatLaw) :=
  ⟨measurable_snd, by unfold sampleLaw; rw [Measure.map_snd_prod, measure_univ, one_smul]⟩

lemma mp_fst' (μ : DemandLaw) :
    MeasurePreserving Prod.fst ((pathLaw μ).prod ghatLaw) (pathLaw μ) :=
  ⟨measurable_fst, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩

lemma mp_eval (μ : DemandLaw) (n : ℕ) :
    MeasurePreserving (fun p : Path => p n) (pathLaw μ) μ.law := by
  unfold pathLaw; exact measurePreserving_eval_infinitePi _ n

lemma ae_good (μ : DemandLaw) :
    ∀ᵐ ω ∂sampleLaw μ, (∀ n, 0 ≤ ω.1 n) ∧ (∀ n, 0 ≤ ω.2.1 n) := by
  refine (ae_all_iff.2 fun n => ?_).and (ae_all_iff.2 fun n => ?_)
  · have hmp := (mp_eval μ n).comp (mp_fst μ)
    exact ae_of_ae_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact ae_nonneg μ)
  · have hmp := ((mp_eval μ n).comp (mp_fst' μ)).comp (mp_snd μ)
    exact ae_of_ae_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact ae_nonneg μ)

lemma ae_path_nonneg (μ : DemandLaw) : ∀ᵐ d ∂pathLaw μ, ∀ n, 0 ≤ d n :=
  ae_all_iff.2 fun n => ae_of_ae_map (mp_eval μ n).measurable.aemeasurable
    (by rw [(mp_eval μ n).map_eq]; exact ae_nonneg μ)

lemma mean_nonneg (μ : DemandLaw) : 0 ≤ μ.mean :=
  integral_nonneg_of_ae (ae_nonneg μ)

lemma real_bound (i : ℕ) : (1 / 2 : ℝ) ^ (i + 1) * ((i : ℝ) + 1) ≤ (3 / 4) ^ i := by
  have h1 : ((i : ℝ) + 1) ≤ 2 * (3 / 2) ^ i := by
    induction i with
    | zero => norm_num
    | succ n ih =>
      have := one_le_pow₀ (show (1 : ℝ) ≤ 3 / 2 by norm_num) (n := n)
      push_cast; rw [pow_succ]; nlinarith
  calc (1 / 2 : ℝ) ^ (i + 1) * ((i : ℝ) + 1) ≤ (1 / 2) ^ (i + 1) * (2 * (3 / 2) ^ i) := by
        gcongr
    _ = (3 / 4) ^ i := by
        rw [pow_succ, show (3 / 4 : ℝ) = (1 / 2) * (3 / 2) by norm_num, mul_pow]; ring

lemma ghat_mean_ne_top : ∫⁻ k, (k : ℝ≥0∞) ∂ghatLaw ≠ ⊤ := by
  unfold ghatLaw
  rw [lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac]
  refine ne_top_of_le_ne_top (ENNReal.tsum_coe_ne_top_iff_summable.2
    (NNReal.summable_geometric (r := 3 / 4) (by norm_num))) (ENNReal.tsum_le_tsum fun i => ?_)
  rw [ENNReal.smul_def, smul_eq_mul, ← ENNReal.coe_natCast, ← ENNReal.coe_mul,
    ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  push_cast
  exact real_bound i

/-! ## Measurability and integrability of the simulated quantities -/

lemma measurable_x0 : Measurable (fun ω : Sample => x0 ω) := by
  unfold x0
  have : Measurable (fun q : Path × ℕ => -∑ i ∈ Finset.range q.2, q.1 i) := by
    refine measurable_from_prod_countable_left fun k => ?_
    simp only
    exact (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).neg
  exact this.comp measurable_snd

lemma measurable_P (L₀ L : ℕ) (r S : ℝ) (n : ℕ) :
    Measurable (fun ω : Sample => P L₀ L r S ω n) := by
  induction n with
  | zero => exact measurable_x0
  | succ n ih =>
    simp only [P]
    exact ((measurable_const.max ih).sub ((measurable_pi_apply n).comp measurable_fst)).add_const _

lemma measurable_q (L₀ L : ℕ) (r S : ℝ) (n : ℕ) :
    Measurable (fun ω : Sample => q L₀ L r S ω n) := by
  unfold q
  exact (measurable_const.max (measurable_P L₀ L r S n)).sub (measurable_P L₀ L r S n)

lemma integrable_D (μ : DemandLaw) (n : ℕ) : Integrable (fun ω : Sample => ω.1 n) (sampleLaw μ) := by
  have hmp := (mp_eval μ n).comp (mp_fst μ)
  exact (hmp.integrable_comp (g := fun d : ℝ => d) measurable_id.aestronglyMeasurable).2 μ.integrable

lemma x0_abs_lintegral (μ : DemandLaw) :
    ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.range ω.2.2, |ω.2.1 i|) ∂sampleLaw μ ≠ ⊤ := by
  have hq : Measurable (fun q : Path × ℕ => ENNReal.ofReal (∑ i ∈ Finset.range q.2, |q.1 i|)) := by
    refine measurable_from_prod_countable_left fun k => ?_
    simp only
    exact ENNReal.measurable_ofReal.comp
      (Finset.measurable_sum _ fun i _ => continuous_abs.measurable.comp (measurable_pi_apply i))
  have hc := (mp_snd μ).lintegral_comp hq
  rw [hc, lintegral_prod_symm _ hq.aemeasurable]
  set B := ∫⁻ d, ENNReal.ofReal |d| ∂μ.law with hBdef
  have hB : B ≠ ⊤ := (Integrable.lintegral_lt_top μ.integrable.abs).ne
  have inner : ∀ k : ℕ, ∫⁻ x, ENNReal.ofReal (∑ i ∈ Finset.range k, |x i|) ∂pathLaw μ ≤
      (k : ℝ≥0∞) * B := by
    intro k
    have hmi : ∀ i, Measurable (fun x : Path => ENNReal.ofReal |x i|) := fun i =>
      ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (measurable_pi_apply i))
    calc _ ≤ ∫⁻ x, ∑ i ∈ Finset.range k, ENNReal.ofReal |x i| ∂pathLaw μ :=
          le_of_eq (lintegral_congr fun x => ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _))
      _ = ∑ i ∈ Finset.range k, ∫⁻ x, ENNReal.ofReal |x i| ∂pathLaw μ :=
          lintegral_finsetSum _ (fun i _ => hmi i)
      _ = ∑ _i ∈ Finset.range k, B := Finset.sum_congr rfl fun i _ =>
          (mp_eval μ i).lintegral_comp (f := fun d : ℝ => ENNReal.ofReal |d|)
            (ENNReal.measurable_ofReal.comp continuous_abs.measurable)
      _ = (k : ℝ≥0∞) * B := by simp
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ghat_mean_ne_top hB)
    (le_trans (lintegral_mono inner) (le_of_eq (lintegral_mul_const B (Measurable.of_discrete))))

lemma integrable_x0 (μ : DemandLaw) : Integrable (fun ω : Sample => x0 ω) (sampleLaw μ) := by
  have hm : Measurable (fun ω : Sample => ∑ i ∈ Finset.range ω.2.2, |ω.2.1 i|) := by
    have : Measurable (fun q : Path × ℕ => ∑ i ∈ Finset.range q.2, |q.1 i|) := by
      refine measurable_from_prod_countable_left fun k => ?_
      simp only
      exact Finset.measurable_sum _ fun i _ => continuous_abs.measurable.comp (measurable_pi_apply i)
    exact this.comp measurable_snd
  have hI : Integrable (fun ω : Sample => ∑ i ∈ Finset.range ω.2.2, |ω.2.1 i|) (sampleLaw μ) :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
      (Eventually.of_forall fun ω => Finset.sum_nonneg fun i _ => abs_nonneg _)).1
      (x0_abs_lintegral μ)
  refine hI.mono' measurable_x0.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  unfold x0
  rw [abs_neg]
  exact Finset.abs_sum_le_sum_abs _ _

lemma integrable_P (μ : DemandLaw) (L₀ L : ℕ) (r S : ℝ) (n : ℕ) :
    Integrable (fun ω : Sample => P L₀ L r S ω n) (sampleLaw μ) := by
  induction n with
  | zero => exact integrable_x0 μ
  | succ n ih =>
    simp only [P]
    exact (((integrable_const S).sup ih).sub (integrable_D μ n)).add (integrable_const _)

lemma integrable_q (μ : DemandLaw) (L₀ L : ℕ) (r S : ℝ) (n : ℕ) :
    Integrable (fun ω : Sample => q L₀ L r S ω n) (sampleLaw μ) := by
  unfold q
  exact ((integrable_const S).sup (integrable_P μ L₀ L r S n)).sub (integrable_P μ L₀ L r S n)

/-! ## The newsvendor function `H` and the expected holding/backorder cost -/

/-- `H y = 𝔼[G(y - ∑ D'_i)]`. -/
noncomputable def H (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (y : ℝ) : ℝ := ∫ z, G κ (y - ∑ i, z i) ∂sumLaw μ L₀

lemma H_nonneg (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (y : ℝ) : 0 ≤ H μ κ L₀ y :=
  integral_nonneg fun _ => G_nonneg _ _

lemma E_G (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (r S : ℝ) (m : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (G κ (max S (P L₀ L r S ω m) - ∑ j : Fin (L₀ + 1), ω.1 (m + j)))
        ∂sampleLaw μ =
      ∫⁻ ω, ENNReal.ofReal (H μ κ L₀ (max S (P L₀ L r S ω m))) ∂sampleLaw μ := by
  set F : Sample → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (G κ (max S (P L₀ L r S ω m) - ∑ j : Fin (L₀ + 1), ω.1 (m + j))) with hFdef
  have hF : Measurable F :=
    ENNReal.measurable_ofReal.comp ((continuous_G κ).measurable.comp
      ((measurable_const.max (measurable_P L₀ L r S m)).sub
        (Finset.measurable_sum _ fun j _ => (measurable_pi_apply _).comp measurable_fst)))
  rw [lintegral_mix μ m (L₀ + 1) hF]
  refine lintegral_congr fun ω => ?_
  have hP : ∀ y : Path, P L₀ L r S (mix m (L₀ + 1) ω.1 y, ω.2) m = P L₀ L r S ω m := by
    intro y
    refine P_local L₀ L r S (mix m (L₀ + 1) ω.1 y, ω.2) ω rfl m fun n hn => ?_
    simp only [mix]; rw [if_neg (by omega)]
  have hw : ∀ y : Path, ∀ j : Fin (L₀ + 1), mix m (L₀ + 1) ω.1 y (m + j) = y (m + j) := by
    intro y j
    simp only [mix]; rw [if_pos (by omega)]
  have hrw : ∀ y, F (mix m (L₀ + 1) ω.1 y, ω.2) =
      (fun z : Fin (L₀ + 1) → ℝ => ENNReal.ofReal (G κ (max S (P L₀ L r S ω m) - ∑ i, z i)))
        (fun j : Fin (L₀ + 1) => y (m + j)) := by
    intro y; simp only [hFdef, hP y]
    congr 3
    exact Finset.sum_congr rfl fun j _ => hw y j
  simp only [hrw]
  have hcomp := (mp_window μ L₀ m).lintegral_comp
    (f := fun z : Fin (L₀ + 1) → ℝ => ENNReal.ofReal (G κ (max S (P L₀ L r S ω m) - ∑ i, z i)))
    (ENNReal.measurable_ofReal.comp ((continuous_G κ).measurable.comp
      (measurable_const.sub (by fun_prop))))
  simp only at hcomp
  rw [hcomp, H, ofReal_integral_eq_lintegral_ofReal (integrable_G_sum μ κ L₀ _)
    (Eventually.of_forall fun _ => G_nonneg _ _)]

/-! ## The Lindley recursion and the running maximum of `W^r` -/

/-- `V k = max(0, P k - S)`, so that `max S (P k) = S + V k`. -/
def V (L₀ L : ℕ) (r S : ℝ) (ω : Sample) (k : ℕ) : ℝ := max 0 (P L₀ L r S ω k - S)

lemma V_nonneg (L₀ L : ℕ) (r S : ℝ) (ω : Sample) (k : ℕ) : 0 ≤ V L₀ L r S ω k := le_max_left _ _

lemma max_eq_S_add_V (L₀ L : ℕ) (r S : ℝ) (ω : Sample) (k : ℕ) :
    max S (P L₀ L r S ω k) = S + V L₀ L r S ω k := by
  unfold V
  rcases le_total S (P L₀ L r S ω k) with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]; ring
  · rw [max_eq_left h, max_eq_left (by linarith)]; ring

lemma V_succ (L₀ L : ℕ) (r S : ℝ) (ω : Sample) (k : ℕ) :
    V L₀ L r S ω (k + 1) = max 0 (V L₀ L r S ω k - ω.1 k + rho L₀ L r k) := by
  have h := max_eq_S_add_V L₀ L r S ω k
  conv_lhs => rw [V, P, h]
  congr 1; ring

lemma rho_of_ge (L₀ L : ℕ) (r : ℝ) (k : ℕ) (hk : L - L₀ - 1 ≤ k) : rho L₀ L r k = r := by
  unfold rho; rw [if_pos (by omega)]

lemma rho_le (L₀ L : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (k : ℕ) : rho L₀ L r k ≤ r := by
  unfold rho; split_ifs <;> linarith

lemma rho_nonneg (L₀ L : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (k : ℕ) : 0 ≤ rho L₀ L r k := by
  unfold rho; split_ifs <;> linarith

/-- Backward running maximum of the increments `r - D` from period `m₀` on. -/
def Rm (m0 : ℕ) (r : ℝ) (ω : Sample) : ℕ → ℝ
  | 0 => 0
  | n + 1 => max 0 (Rm m0 r ω n + (r - ω.1 (m0 + n)))

/-- `W' n = ∑_{j<n} (r - D_{m₀+j})`. -/
def Wp (m0 : ℕ) (r : ℝ) (ω : Sample) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, (r - ω.1 (m0 + j))

lemma lindley (L₀ L : ℕ) (r S : ℝ) (ω : Sample) (n : ℕ) :
    V L₀ L r S ω (L - L₀ - 1 + n) =
      max (V L₀ L r S ω (L - L₀ - 1) + Wp (L - L₀ - 1) r ω n) (Rm (L - L₀ - 1) r ω n) := by
  induction n with
  | zero =>
    simp only [add_zero, Wp, Finset.range_zero, Finset.sum_empty, Rm]
    exact (max_eq_left (V_nonneg _ _ _ _ _ _)).symm
  | succ n ih =>
    rw [← add_assoc, V_succ, ih, rho_of_ge L₀ L r _ (by omega)]
    simp only [Wp, Rm, Finset.sum_range_succ]
    set A := V L₀ L r S ω (L - L₀ - 1) + ∑ j ∈ Finset.range n, (r - ω.1 (L - L₀ - 1 + j))
    set R := Rm (L - L₀ - 1) r ω n
    set x := r - ω.1 (L - L₀ - 1 + n)
    have e1 : max A R - ω.1 (L - L₀ - 1 + n) + r = max (A + x) (R + x) := by
      rw [max_add_add_right]; simp only [x]; ring
    rw [e1, show A + x = A + (r - ω.1 (L - L₀ - 1 + n)) from rfl,
      show R + x = R + (r - ω.1 (L - L₀ - 1 + n)) from rfl]
    rw [max_comm 0 (max _ _), max_assoc, max_comm _ 0]
    congr 1; simp only [A, x]; ring

/-- Running maximum `Zb n = max_{i ≤ n} W^r_i`. -/
def Zb (r : ℝ) (d : Path) : ℕ → ℝ
  | 0 => 0
  | n + 1 => max (Zb r d n) (W r d (n + 1))

/-- Shift of a path. -/
def sh (d : Path) : Path := fun n => d (n + 1)

lemma W_succ (r : ℝ) (d : Path) (k : ℕ) : W r d (k + 1) = (r - d 0) + W r (sh d) k := by
  unfold W sh; rw [Finset.sum_range_succ']; ring

lemma W_zero (r : ℝ) (d : Path) : W r d 0 = 0 := by simp [W]

lemma Zb_front (r : ℝ) (d : Path) (n : ℕ) :
    Zb r d (n + 1) = max 0 ((r - d 0) + Zb r (sh d) n) := by
  induction n with
  | zero => simp [Zb, W_succ, W_zero]
  | succ n ih =>
    rw [Zb, ih, W_succ, Zb, max_assoc, ← max_add_add_left]

lemma Zb_nonneg (r : ℝ) (d : Path) (n : ℕ) : 0 ≤ Zb r d n := by
  induction n with
  | zero => simp [Zb]
  | succ n ih => exact ih.trans (le_max_left _ _)

lemma Zb_mono (r : ℝ) (d : Path) : Monotone (fun n => Zb r d n) :=
  monotone_nat_of_le_succ fun n => le_max_left _ _

lemma W_le_Zb (r : ℝ) (d : Path) (n : ℕ) : W r d n ≤ Zb r d n := by
  cases n with
  | zero => simp [Zb, W_zero]
  | succ n => exact le_max_right _ _

lemma Zb_local (r : ℝ) (d d' : Path) (n : ℕ) (h : ∀ j < n, d j = d' j) : Zb r d n = Zb r d' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Zb]
    rw [ih fun j hj => h j (by omega)]
    congr 1
    unfold W
    exact Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)]

lemma measurable_W' (r : ℝ) (i : ℕ) : Measurable (fun d : Path => W r d i) := by
  unfold W; fun_prop

lemma measurable_Zb (r : ℝ) (n : ℕ) : Measurable (fun d : Path => Zb r d n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact ih.max (measurable_W' r (n + 1))

lemma measurable_Zinf' (r : ℝ) : Measurable (fun d : Path => Zinf r d) := by
  unfold Zinf
  exact Measurable.iSup fun i => ENNReal.measurable_ofReal.comp (measurable_W' r i)

lemma ofReal_Zb_le (r : ℝ) (d : Path) (n : ℕ) : ENNReal.ofReal (Zb r d n) ≤ Zinf r d := by
  induction n with
  | zero => simp [Zb]
  | succ n ih =>
    simp only [Zb]
    rw [ENNReal.ofReal_max]
    exact max_le ih (le_iSup (fun i => ENNReal.ofReal (W r d i)) (n + 1))

lemma Zinf_eq_iSup (r : ℝ) (d : Path) : Zinf r d = ⨆ n, ENNReal.ofReal (Zb r d n) :=
  le_antisymm (iSup_le fun i => (ENNReal.ofReal_le_ofReal (W_le_Zb r d i)).trans
    (le_iSup (fun n => ENNReal.ofReal (Zb r d n)) i)) (iSup_le fun n => ofReal_Zb_le r d n)

lemma tendsto_Zb (r : ℝ) (d : Path) :
    Tendsto (fun n => ENNReal.ofReal (Zb r d n)) atTop (𝓝 (Zinf r d)) := by
  rw [Zinf_eq_iSup]
  exact tendsto_atTop_iSup fun a b hab => ENNReal.ofReal_le_ofReal (Zb_mono r d hab)

lemma tendsto_Zb_real (r : ℝ) (d : Path) (h : Zinf r d ≠ ⊤) :
    Tendsto (fun n => Zb r d n) atTop (𝓝 (Zinf r d).toReal) := by
  have := (ENNReal.tendsto_toReal h).comp (tendsto_Zb r d)
  refine this.congr fun n => ?_
  simp [ENNReal.toReal_ofReal (Zb_nonneg r d n)]

lemma Zb_le_toReal (r : ℝ) (d : Path) (h : Zinf r d ≠ ⊤) (n : ℕ) : Zb r d n ≤ (Zinf r d).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal h).1 (ofReal_Zb_le r d n)

/-! ## Reversal: `Rm n` has the law of `Zb n` -/

/-- Pad a finite vector into a path. -/
def pad (n : ℕ) (z : Fin n → ℝ) : Path := fun l => if h : l < n then z ⟨l, h⟩ else 0

lemma measurable_pad (n : ℕ) : Measurable (pad n) := by
  refine measurable_pi_lambda _ fun l => ?_
  by_cases h : l < n
  · simp only [pad, h, dif_pos]; exact measurable_pi_apply _
  · simp only [pad, h, dif_neg, not_false_eq_true]; exact measurable_const

lemma Rm_eq (m0 : ℕ) (r : ℝ) (ω : Sample) (n : ℕ) :
    Rm m0 r ω n = Zb r (pad n (fun j : Fin n => ω.1 (m0 + n - 1 - j))) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Rm, Zb_front, ih]
    have h0 : pad (n + 1) (fun j : Fin (n + 1) => ω.1 (m0 + (n + 1) - 1 - j)) 0 = ω.1 (m0 + n) := by
      simp only [pad, dif_pos (Nat.succ_pos n)]
      congr 1
    have hs : sh (pad (n + 1) (fun j : Fin (n + 1) => ω.1 (m0 + (n + 1) - 1 - j))) =
        pad n (fun j : Fin n => ω.1 (m0 + n - 1 - j)) := by
      funext l
      simp only [sh, pad]
      by_cases hl : l < n
      · rw [dif_pos (by omega), dif_pos hl]
        show ω.1 (m0 + (n + 1) - 1 - (l + 1)) = ω.1 (m0 + n - 1 - l)
        rw [show m0 + (n + 1) - 1 - (l + 1) = m0 + n - 1 - l by omega]
      · rw [dif_neg (by omega), dif_neg hl]
    rw [h0, hs, add_comm (Zb _ _ _)]

lemma Wp_eq (m0 : ℕ) (r : ℝ) (ω : Sample) (n : ℕ) :
    Wp m0 r ω n = W r (pad n (fun j : Fin n => ω.1 (m0 + j))) n := by
  unfold Wp W
  refine Finset.sum_congr rfl fun j hj => ?_
  have := Finset.mem_range.1 hj
  simp only [pad, dif_pos this]

/-- Transfer: a functional of the first `n` coordinates, read through an injective index map. -/
lemma transfer (μ : DemandLaw) (n : ℕ) (σ : Fin n → ℕ) (hσ : Function.Injective σ)
    (g : Path → ℝ≥0∞) (hg : Measurable g) (hloc : ∀ d d' : Path, (∀ j < n, d j = d' j) → g d = g d') :
    ∫⁻ ω, g (pad n (fun j => ω.1 (σ j))) ∂sampleLaw μ = ∫⁻ d, g d ∂pathLaw μ := by
  have h1 := ((mp_idx μ n σ hσ).comp (mp_fst μ)).lintegral_comp (hg.comp (measurable_pad n))
  have h2 := (mp_idx μ n (fun j => (j : ℕ)) (fun a b h => Fin.ext h)).lintegral_comp
    (hg.comp (measurable_pad n))
  simp only [Function.comp] at h1 h2
  rw [h1, ← h2]
  refine lintegral_congr fun d => hloc _ _ fun j hj => ?_
  simp [pad, hj]

lemma E_Rm (μ : DemandLaw) (m0 : ℕ) (r : ℝ) (n : ℕ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ ω, f (Rm m0 r ω n) ∂sampleLaw μ = ∫⁻ d, f (Zb r d n) ∂pathLaw μ := by
  simp only [Rm_eq]
  exact transfer μ n (fun j => m0 + n - 1 - j) (fun a b h => by
      have := a.isLt; have := b.isLt; exact Fin.ext (by simp only at h; omega))
    (fun d => f (Zb r d n)) (hf.comp (measurable_Zb r n))
    (fun d d' h => by rw [Zb_local r d d' n h])

lemma E_Wp (μ : DemandLaw) (m0 : ℕ) (r : ℝ) (n : ℕ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ ω, f (Wp m0 r ω n) ∂sampleLaw μ = ∫⁻ d, f (W r d n) ∂pathLaw μ := by
  simp only [Wp_eq]
  exact transfer μ n (fun j => m0 + j) (fun a b h => Fin.ext (by simpa using h))
    (fun d => f (W r d n)) (hf.comp (measurable_W' r n))
    (fun d d' h => by
      congr 1; unfold W
      exact Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)])

/-! ## Properties of `H`; convergence of `𝔼[H(S + Zb n)]` -/

/-- Holding part of `H`. -/
noncomputable def Hp (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (y : ℝ) : ℝ :=
  κ.h * ∫ z, max (y - ∑ i, z i) 0 ∂sumLaw μ L₀

/-- Backorder part of `H`. -/
noncomputable def Hm (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (y : ℝ) : ℝ :=
  κ.b * ∫ z, max (-(y - ∑ i, z i)) 0 ∂sumLaw μ L₀

lemma H_split (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (y : ℝ) :
    H μ κ L₀ y = Hp μ κ L₀ y + Hm μ κ L₀ y := by
  unfold H Hp Hm G
  rw [integral_add (((integrable_shift μ L₀ y).pos_part).const_mul _)
    (((integrable_shift μ L₀ y).neg_part).const_mul _), integral_const_mul, integral_const_mul]

lemma Hp_nonneg (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (y : ℝ) : 0 ≤ Hp μ κ L₀ y :=
  mul_nonneg κ.h_pos.le (integral_nonneg fun _ => le_max_right _ _)

lemma Hm_nonneg (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (y : ℝ) : 0 ≤ Hm μ κ L₀ y :=
  mul_nonneg κ.b_pos.le (integral_nonneg fun _ => le_max_right _ _)

lemma Hp_mono (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) : Monotone (Hp μ κ L₀) := by
  intro y y' h
  unfold Hp
  refine mul_le_mul_of_nonneg_left (integral_mono (integrable_shift μ L₀ y).pos_part
    (integrable_shift μ L₀ y').pos_part fun z => ?_) κ.h_pos.le
  exact max_le_max (by linarith) le_rfl

lemma Hm_anti (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) : Antitone (Hm μ κ L₀) := by
  intro y y' h
  unfold Hm
  refine mul_le_mul_of_nonneg_left (integral_mono (integrable_shift μ L₀ y').neg_part
    (integrable_shift μ L₀ y).neg_part fun z => ?_) κ.b_pos.le
  exact max_le_max (by linarith) le_rfl

lemma posp_lip (a c : ℝ) : max a 0 ≤ max c 0 + |a - c| := by
  have := le_abs_self (a - c); have := abs_nonneg (a - c)
  rcases le_total a 0 with h | h <;> rcases le_total c 0 with h' | h'
  · rw [max_eq_right h, max_eq_right h']; linarith
  · rw [max_eq_right h, max_eq_left h']; linarith
  · rw [max_eq_left h, max_eq_right h']; linarith
  · rw [max_eq_left h, max_eq_left h']; linarith

lemma Hp_lip (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (y y' : ℝ) :
    Hp μ κ L₀ y ≤ Hp μ κ L₀ y' + κ.h * |y - y'| := by
  unfold Hp
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ κ.h_pos.le
  have hc : ∫ z, (max (y' - ∑ i, z i) 0 + |y - y'|) ∂sumLaw μ L₀ =
      ∫ z, max (y' - ∑ i, z i) 0 ∂sumLaw μ L₀ + |y - y'| := by
    rw [integral_add (integrable_shift μ L₀ y').pos_part (integrable_const _)]; simp
  rw [← hc]
  refine integral_mono (integrable_shift μ L₀ y).pos_part
    ((integrable_shift μ L₀ y').pos_part.add (integrable_const _)) fun z => ?_
  have := posp_lip (y - ∑ i, z i) (y' - ∑ i, z i)
  simp only
  rw [show y - ∑ i, z i - (y' - ∑ i, z i) = y - y' by ring] at this
  exact this

lemma Hm_lip (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (y y' : ℝ) :
    Hm μ κ L₀ y ≤ Hm μ κ L₀ y' + κ.b * |y - y'| := by
  unfold Hm
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ κ.b_pos.le
  have hc : ∫ z, (max (-(y' - ∑ i, z i)) 0 + |y - y'|) ∂sumLaw μ L₀ =
      ∫ z, max (-(y' - ∑ i, z i)) 0 ∂sumLaw μ L₀ + |y - y'| := by
    rw [integral_add (integrable_shift μ L₀ y').neg_part (integrable_const _)]; simp
  rw [← hc]
  refine integral_mono (integrable_shift μ L₀ y).neg_part
    ((integrable_shift μ L₀ y').neg_part.add (integrable_const _)) fun z => ?_
  have := posp_lip (-(y - ∑ i, z i)) (-(y' - ∑ i, z i))
  simp only
  rw [show -(y - ∑ i, z i) - -(y' - ∑ i, z i) = -(y - y') by ring, abs_neg] at this
  exact this

lemma continuous_Hp (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) : Continuous (Hp μ κ L₀) :=
  (LipschitzWith.of_le_add_mul' κ.h fun x y => by
    rw [Real.dist_eq]; exact Hp_lip μ κ L₀ x y).continuous

lemma continuous_Hm (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) : Continuous (Hm μ κ L₀) :=
  (LipschitzWith.of_le_add_mul' κ.b fun x y => by
    rw [Real.dist_eq]; exact Hm_lip μ κ L₀ x y).continuous

lemma continuous_H (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) : Continuous (H μ κ L₀) := by
  have : H μ κ L₀ = fun y => Hp μ κ L₀ y + Hm μ κ L₀ y := funext (H_split μ κ L₀)
  rw [this]; exact (continuous_Hp μ κ L₀).add (continuous_Hm μ κ L₀)

/-- Mean of `∑ D'_i`. -/
noncomputable def SM (μ : DemandLaw) (L₀ : ℕ) : ℝ := ∫ z, ∑ i, z i ∂sumLaw μ L₀

lemma integrable_sum (μ : DemandLaw) (L₀ : ℕ) :
    Integrable (fun z : Fin (L₀ + 1) → ℝ => ∑ i, z i) (sumLaw μ L₀) :=
  integrable_finsetSum _ fun i _ => integrable_coord μ L₀ i

lemma Hp_ge (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (y : ℝ) :
    κ.h * (y - SM μ L₀) ≤ Hp μ κ L₀ y := by
  unfold Hp SM
  refine mul_le_mul_of_nonneg_left ?_ κ.h_pos.le
  have hc : ∫ z, (y - ∑ i, z i) ∂sumLaw μ L₀ = y - ∫ z, ∑ i, z i ∂sumLaw μ L₀ := by
    rw [integral_sub (integrable_const _) (integrable_sum μ L₀)]; simp
  rw [← hc]
  exact integral_mono ((integrable_const _).sub (integrable_sum μ L₀))
    (integrable_shift μ L₀ y).pos_part fun z => le_max_left _ _

lemma H_ge (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (y : ℝ) :
    min κ.b κ.h * (y - SM μ L₀) ≤ H μ κ L₀ y := by
  unfold H SM
  have hc : ∫ z, (y - ∑ i, z i) ∂sumLaw μ L₀ = y - ∫ z, ∑ i, z i ∂sumLaw μ L₀ := by
    rw [integral_sub (integrable_const _) (integrable_sum μ L₀)]; simp
  rw [← hc, ← integral_const_mul]
  refine integral_mono (((integrable_const _).sub (integrable_sum μ L₀)).const_mul _)
    (integrable_G_sum μ κ L₀ y) fun z => ?_
  have h1 := G_ge κ (y - ∑ i, z i)
  have h2 := le_abs_self (y - ∑ i, z i)
  have h3 : 0 < min κ.b κ.h := lt_min κ.b_pos κ.h_pos
  simp only
  nlinarith

lemma H_lip (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (y y' : ℝ) :
    H μ κ L₀ y ≤ H μ κ L₀ y' + max κ.b κ.h * |y - y'| := by
  unfold H
  have hc : ∫ z, (G κ (y' - ∑ i, z i) + max κ.b κ.h * |y - y'|) ∂sumLaw μ L₀ =
      ∫ z, G κ (y' - ∑ i, z i) ∂sumLaw μ L₀ + max κ.b κ.h * |y - y'| := by
    rw [integral_add (integrable_G_sum μ κ L₀ y') (integrable_const _)]; simp
  rw [← hc]
  refine integral_mono (integrable_G_sum μ κ L₀ y)
    ((integrable_G_sum μ κ L₀ y').add (integrable_const _)) fun z => ?_
  have := G_lip κ (y - ∑ i, z i) (y' - ∑ i, z i)
  simp only
  rw [show y - ∑ i, z i - (y' - ∑ i, z i) = y - y' by ring] at this
  exact this

/-- The limit integrand `K(Z^r_∞)`. -/
noncomputable def Kfun (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (r S : ℝ) (d : Path) : ℝ≥0∞ :=
  if Zinf r d = ⊤ then ⊤ else ENNReal.ofReal (H μ κ L₀ (S + (Zinf r d).toReal))

lemma Zb_tendsto_atTop (r : ℝ) (d : Path) (h : Zinf r d = ⊤) :
    Tendsto (fun n => Zb r d n) atTop atTop := by
  have ht := tendsto_Zb r d
  rw [h] at ht
  refine tendsto_atTop.2 fun b => ?_
  have := ht.eventually (lt_mem_nhds (show ENNReal.ofReal b < ⊤ from ENNReal.ofReal_lt_top))
  filter_upwards [this] with n hn
  exact ((ENNReal.ofReal_lt_ofReal_iff'.1 hn).1).le

lemma g_tendsto (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (r S : ℝ) :
    Tendsto (fun n => ∫⁻ d, ENNReal.ofReal (H μ κ L₀ (S + Zb r d n)) ∂pathLaw μ) atTop
      (𝓝 (∫⁻ d, Kfun μ κ L₀ r S d ∂pathLaw μ)) := by
  set Kp : Path → ℝ≥0∞ := fun d =>
    if Zinf r d = ⊤ then ⊤ else ENNReal.ofReal (Hp μ κ L₀ (S + (Zinf r d).toReal)) with hKp
  set Fm : Path → ℝ≥0∞ := fun d => ⨅ n, ENNReal.ofReal (Hm μ κ L₀ (S + Zb r d n)) with hFm
  have hmp : ∀ n, Measurable (fun d : Path => ENNReal.ofReal (Hp μ κ L₀ (S + Zb r d n))) :=
    fun n => ENNReal.measurable_ofReal.comp ((continuous_Hp μ κ L₀).measurable.comp
      (measurable_const.add (measurable_Zb r n)))
  have hmm : ∀ n, Measurable (fun d : Path => ENNReal.ofReal (Hm μ κ L₀ (S + Zb r d n))) :=
    fun n => ENNReal.measurable_ofReal.comp ((continuous_Hm μ κ L₀).measurable.comp
      (measurable_const.add (measurable_Zb r n)))
  have hsplit : ∀ n, ∫⁻ d, ENNReal.ofReal (H μ κ L₀ (S + Zb r d n)) ∂pathLaw μ =
      ∫⁻ d, ENNReal.ofReal (Hp μ κ L₀ (S + Zb r d n)) ∂pathLaw μ +
        ∫⁻ d, ENNReal.ofReal (Hm μ κ L₀ (S + Zb r d n)) ∂pathLaw μ := by
    intro n
    rw [← lintegral_add_left (hmp n)]
    refine lintegral_congr fun d => ?_
    rw [H_split, ENNReal.ofReal_add (Hp_nonneg _ _ _ _) (Hm_nonneg _ _ _ _)]
  simp only [hsplit]
  -- monotone part
  have hP : Tendsto (fun n => ∫⁻ d, ENNReal.ofReal (Hp μ κ L₀ (S + Zb r d n)) ∂pathLaw μ) atTop
      (𝓝 (∫⁻ d, Kp d ∂pathLaw μ)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun n => (hmp n).aemeasurable)
      (Eventually.of_forall fun d a b hab => ENNReal.ofReal_le_ofReal
        (Hp_mono μ κ L₀ (by have := Zb_mono r d hab; simp only at this; linarith)))
      (Eventually.of_forall fun d => ?_)
    by_cases htop : Zinf r d = ⊤
    · simp only [hKp, htop, if_true]
      have h1 : Tendsto (fun n => ENNReal.ofReal (κ.h * (S + Zb r d n - SM μ L₀))) atTop (𝓝 ⊤) :=
        ENNReal.tendsto_ofReal_atTop.comp (Tendsto.const_mul_atTop κ.h_pos
          (tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_left _ _
            (Zb_tendsto_atTop r d htop))))
      exact tendsto_nhds_top_mono h1 (Eventually.of_forall fun n =>
        ENNReal.ofReal_le_ofReal (Hp_ge μ κ L₀ _))
    · simp only [hKp, htop, if_false]
      exact (ENNReal.continuous_ofReal.tendsto _).comp
        (((continuous_Hp μ κ L₀).tendsto _).comp (tendsto_const_nhds.add (tendsto_Zb_real r d htop)))
  -- antitone part
  have hM : Tendsto (fun n => ∫⁻ d, ENNReal.ofReal (Hm μ κ L₀ (S + Zb r d n)) ∂pathLaw μ) atTop
      (𝓝 (∫⁻ d, Fm d ∂pathLaw μ)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal (Hm μ κ L₀ S))
      hmm (fun n => Eventually.of_forall fun d => ENNReal.ofReal_le_ofReal
        (Hm_anti μ κ L₀ (by have := Zb_nonneg r d n; linarith))) (by simp)
      (Eventually.of_forall fun d => ?_)
    exact tendsto_atTop_iInf fun a b hab => ENNReal.ofReal_le_ofReal
      (Hm_anti μ κ L₀ (by have := Zb_mono r d hab; simp only at this; linarith))
  have hsum := hP.add hM
  rw [← lintegral_add_right _ (Measurable.iInf fun n => hmm n)] at hsum
  convert hsum using 2
  refine lintegral_congr fun d => ?_
  by_cases htop : Zinf r d = ⊤
  · simp [Kfun, hKp, htop]
  · have hlim : Tendsto (fun n => ENNReal.ofReal (Hm μ κ L₀ (S + Zb r d n))) atTop
        (𝓝 (ENNReal.ofReal (Hm μ κ L₀ (S + (Zinf r d).toReal)))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp
        (((continuous_Hm μ κ L₀).tendsto _).comp (tendsto_const_nhds.add (tendsto_Zb_real r d htop)))
    have hinf : Tendsto (fun n => ENNReal.ofReal (Hm μ κ L₀ (S + Zb r d n))) atTop (𝓝 (Fm d)) :=
      tendsto_atTop_iInf fun a b hab => ENNReal.ofReal_le_ofReal
        (Hm_anti μ κ L₀ (by have := Zb_mono r d hab; simp only at this; linarith))
    have hFd : (⨅ i, ENNReal.ofReal (Hm μ κ L₀ (S + Zb r d i))) =
        ENNReal.ofReal (Hm μ κ L₀ (S + (Zinf r d).toReal)) := tendsto_nhds_unique hinf hlim
    rw [hFd]
    simp only [Kfun, hKp, htop, if_false]
    rw [H_split, ENNReal.ofReal_add (Hp_nonneg _ _ _ _) (Hm_nonneg _ _ _ _)]

lemma measurable_Kfun (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (r S : ℝ) :
    Measurable (Kfun μ κ L₀ r S) := by
  unfold Kfun
  refine Measurable.ite ((measurable_Zinf' r) (measurableSet_singleton ⊤)) measurable_const ?_
  exact ENNReal.measurable_ofReal.comp ((continuous_H μ κ L₀).measurable.comp
    (measurable_const.add ((measurable_Zinf' r).ennreal_toReal)))

lemma rhs_eq (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (r S : ℝ) :
    ∫⁻ p : Path × (Fin (L₀ + 1) → ℝ),
        (if Zinf r p.1 = ⊤ then ⊤
          else ENNReal.ofReal (G κ ((Zinf r p.1).toReal + S - ∑ i, p.2 i)))
        ∂((pathLaw μ).prod (sumLaw μ L₀)) = ∫⁻ d, Kfun μ κ L₀ r S d ∂pathLaw μ := by
  have hm : Measurable (fun p : Path × (Fin (L₀ + 1) → ℝ) =>
      (if Zinf r p.1 = ⊤ then ⊤
        else ENNReal.ofReal (G κ ((Zinf r p.1).toReal + S - ∑ i, p.2 i)) : ℝ≥0∞)) := by
    refine Measurable.ite (((measurable_Zinf' r).comp measurable_fst) (measurableSet_singleton ⊤))
      measurable_const ?_
    exact ENNReal.measurable_ofReal.comp ((continuous_G κ).measurable.comp
      ((((measurable_Zinf' r).comp measurable_fst).ennreal_toReal.add_const _).sub
        (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp measurable_snd)))
  rw [lintegral_prod _ hm.aemeasurable]
  refine lintegral_congr fun d => ?_
  by_cases htop : Zinf r d = ⊤
  · simp [Kfun, htop]
  · simp only [htop, if_false, Kfun]
    rw [H, ofReal_integral_eq_lintegral_ofReal (integrable_G_sum μ κ L₀ _)
      (Eventually.of_forall fun _ => G_nonneg _ _)]
    refine lintegral_congr fun z => ?_
    congr 2; ring

/-! ## Negative drift: the error term vanishes (exponential moment) -/

lemma phi_nonneg (μ : DemandLaw) (ϵ θ : ℝ) : 0 ≤ phi μ ϵ θ :=
  mul_nonneg (Real.exp_pos _).le (integral_nonneg fun d => (Real.exp_pos _).le)

lemma gamma_le_phi (μ : DemandLaw) (ϵ θ : ℝ) (hθ : 0 ≤ θ) : gamma μ ϵ ≤ phi μ ϵ θ := by
  unfold gamma
  exact ciInf_le (f := fun t : Set.Ici (0 : ℝ) => phi μ ϵ t)
    ⟨0, by rintro _ ⟨t, rfl⟩; exact phi_nonneg _ _ _⟩ ⟨θ, hθ⟩

lemma exists_trunc (μ : DemandLaw) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 1 ≤ K ∧ μ.mean - δ < ∫ d, min d K ∂μ.law := by
  have ht : Tendsto (fun n : ℕ => ∫ d, min d ((n : ℝ) + 1) ∂μ.law) atTop
      (nhds (∫ d, d ∂μ.law)) := by
    refine tendsto_integral_of_dominated_convergence (fun d => |d|) (fun n => ?_)
      μ.integrable.abs (fun n => ?_) ?_
    · exact (measurable_id.min measurable_const).aestronglyMeasurable
    · filter_upwards [ae_nonneg μ] with d hd
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hd (by positivity))]
      exact (min_le_left _ _).trans (le_abs_self _)
    · refine Eventually.of_forall fun d => tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈d⌉₊] with n hn
      have : d ≤ (n : ℝ) + 1 := by
        have := (Nat.le_ceil d).trans (Nat.cast_le.mpr hn)
        linarith
      exact (min_eq_left this).symm
  have hlt : μ.mean - δ < ∫ d, d ∂μ.law := by
    show μ.mean - δ < μ.mean; linarith
  obtain ⟨n, hn⟩ := (ht.eventually (lt_mem_nhds hlt)).exists
  exact ⟨(n : ℝ) + 1, by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)], hn⟩

lemma gamma_lt_one (μ : DemandLaw) (ϵ : ℝ) (hϵ : 0 < ϵ) : gamma μ ϵ < 1 := by
  obtain ⟨K, hK1, hK⟩ := exists_trunc μ (ϵ / 2) (by linarith)
  have hKpos : 0 < K := by linarith
  set θ := min (1 / K) (ϵ / (4 * K ^ 2)) with hθdef
  have hθpos : 0 < θ := lt_min (by positivity) (by positivity)
  have hθK : θ * K ≤ 1 := by
    have : θ ≤ 1 / K := min_le_left _ _
    calc θ * K ≤ 1 / K * K := mul_le_mul_of_nonneg_right this hKpos.le
      _ = 1 := by field_simp
  have hθ2 : θ * K ^ 2 ≤ ϵ / 4 := by
    have : θ ≤ ϵ / (4 * K ^ 2) := min_le_right _ _
    calc θ * K ^ 2 ≤ ϵ / (4 * K ^ 2) * K ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
      _ = ϵ / 4 := by field_simp
  have hpt : ∀ᵐ d ∂μ.law, Real.exp (-(θ * d)) ≤ 1 - θ * min d K + (θ * K) ^ 2 := by
    filter_upwards [ae_nonneg μ] with d hd
    have hm0 : 0 ≤ min d K := le_min hd hKpos.le
    have hu0 : 0 ≤ θ * min d K := mul_nonneg hθpos.le hm0
    have huK : θ * min d K ≤ θ * K := mul_le_mul_of_nonneg_left (min_le_right _ _) hθpos.le
    have hud : θ * min d K ≤ θ * d := mul_le_mul_of_nonneg_left (min_le_left _ _) hθpos.le
    have h1 : Real.exp (-(θ * d)) ≤ Real.exp (-(θ * min d K)) := Real.exp_le_exp.mpr (by linarith)
    have h2 := Real.abs_exp_sub_one_sub_id_le (x := -(θ * min d K))
      (by rw [abs_neg, abs_of_nonneg hu0]; linarith)
    have h3 := (abs_le.mp h2).2
    have h4 : (-(θ * min d K)) ^ 2 ≤ (θ * K) ^ 2 := by
      rw [neg_sq]; exact pow_le_pow_left₀ hu0 huK 2
    linarith
  have hint1 : Integrable (fun d => Real.exp (-(θ * d))) μ.law := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).measurable.aestronglyMeasurable
    · filter_upwards [ae_nonneg μ] with d hd
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hmin : Integrable (fun d => min d K) μ.law := by
    refine Integrable.mono' (μ.integrable.abs.add (integrable_const K)) ?_ ?_
    · exact (measurable_id.min measurable_const).aestronglyMeasurable
    · filter_upwards [ae_nonneg μ] with d hd
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hd hKpos.le)]
      have := (min_le_left d K).trans (le_abs_self d)
      simp only [Pi.add_apply, id]
      linarith
  have hint2 : Integrable (fun d => 1 - θ * min d K + (θ * K) ^ 2) μ.law :=
    ((integrable_const 1).sub (hmin.const_mul θ)).add (integrable_const _)
  have hE : ∫ d, Real.exp (-(θ * d)) ∂μ.law ≤ 1 - θ * ∫ d, min d K ∂μ.law + (θ * K) ^ 2 := by
    calc ∫ d, Real.exp (-(θ * d)) ∂μ.law ≤ ∫ d, (1 - θ * min d K + (θ * K) ^ 2) ∂μ.law :=
          integral_mono_ae hint1 hint2 hpt
      _ = 1 - θ * ∫ d, min d K ∂μ.law + (θ * K) ^ 2 := by
          rw [integral_add (f := fun d => 1 - θ * min d K) (g := fun _ => (θ * K) ^ 2)
            ((integrable_const 1).sub (hmin.const_mul θ)) (integrable_const _),
            integral_sub (f := fun _ => (1 : ℝ)) (g := fun d => θ * min d K)
              (integrable_const 1) (hmin.const_mul θ), integral_const_mul]
          simp
  have hlow : 1 - θ * (μ.mean - ϵ) ≤ Real.exp (-(θ * (μ.mean - ϵ))) := by
    linarith [Real.add_one_le_exp (-(θ * (μ.mean - ϵ)))]
  have hsq : (θ * K) ^ 2 = θ * (θ * K ^ 2) := by ring
  have hθ3 : θ * (θ * K ^ 2) ≤ θ * (ϵ / 4) := mul_le_mul_of_nonneg_left hθ2 hθpos.le
  have hK' : θ * (μ.mean - ϵ / 2) < θ * ∫ d, min d K ∂μ.law := mul_lt_mul_of_pos_left hK hθpos
  have hE' : ∫ d, Real.exp (-(θ * d)) ∂μ.law < Real.exp (-(θ * (μ.mean - ϵ))) := by
    nlinarith
  have hφ : phi μ ϵ θ < 1 := by
    unfold phi
    calc Real.exp (θ * (μ.mean - ϵ)) * ∫ d, Real.exp (-(θ * d)) ∂μ.law
        < Real.exp (θ * (μ.mean - ϵ)) * Real.exp (-(θ * (μ.mean - ϵ))) :=
          mul_lt_mul_of_pos_left hE' (Real.exp_pos _)
      _ = 1 := by rw [← Real.exp_add]; simp
  exact lt_of_le_of_lt (gamma_le_phi μ ϵ θ hθpos.le) hφ

lemma integrable_exp_incr (μ : DemandLaw) (θ r : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun x : ℝ => Real.exp (θ * (r - x))) μ.law := by
  refine Integrable.of_bound (by fun_prop) (Real.exp (θ * r)) ?_
  filter_upwards [ae_nonneg μ] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (by nlinarith)

lemma exists_theta (μ : DemandLaw) (r : ℝ) (hr : r < μ.mean) :
    ∃ θ : ℝ, 0 < θ ∧ ∫ x, Real.exp (θ * (r - x)) ∂μ.law < 1 := by
  have hγ := gamma_lt_one μ (μ.mean - r) (by linarith)
  unfold gamma at hγ
  obtain ⟨⟨θ, hθ⟩, hlt⟩ := exists_lt_of_ciInf_lt hγ
  have hphi : phi μ (μ.mean - r) θ = ∫ x, Real.exp (θ * (r - x)) ∂μ.law := by
    unfold phi
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← Real.exp_add]; congr 1; ring
  simp only at hlt
  rw [hphi] at hlt
  refine ⟨θ, lt_of_le_of_ne hθ fun h0 => ?_, hlt⟩
  rw [← h0] at hlt
  simp at hlt

lemma W_exp (μ : DemandLaw) (θ r : ℝ) (n : ℕ) :
    ∫ d, Real.exp (θ * W r d n) ∂pathLaw μ = (∫ x, Real.exp (θ * (r - x)) ∂μ.law) ^ n := by
  have hmp := mp_idx μ n (fun j => (j : ℕ)) (fun a b h => Fin.ext h)
  set F : (Fin n → ℝ) → ℝ := fun z => ∏ j, Real.exp (θ * (r - z j)) with hF
  have hFm : Measurable F := by rw [hF]; fun_prop
  have hpt : ∀ d : Path, Real.exp (θ * W r d n) = F (fun j : Fin n => d j) := by
    intro d
    simp only [hF, W]
    rw [← Real.exp_sum, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun j => θ * (r - d j))]
  simp only [hpt]
  have hmap := integral_map (μ := pathLaw μ) hmp.measurable.aemeasurable
    (f := F) hFm.aestronglyMeasurable
  rw [hmp.map_eq] at hmap
  rw [← hmap, hF, integral_fintype_prod_eq_prod (f := fun _ : Fin n => fun x : ℝ =>
    Real.exp (θ * (r - x)))]
  simp

lemma err_tendsto (μ : DemandLaw) (r : ℝ) (hr0 : 0 ≤ r) (hr : r < μ.mean) (Bd M : ℝ) (hM : 0 ≤ M) :
    Tendsto (fun n => ∫⁻ d, ENNReal.ofReal (M * max 0 (Bd + W r d n)) ∂pathLaw μ) atTop (𝓝 0) := by
  obtain ⟨θ, hθ, hφ1⟩ := exists_theta μ r hr
  set φ := ∫ x, Real.exp (θ * (r - x)) ∂μ.law with hφdef
  have hφ0 : 0 ≤ φ := integral_nonneg fun x => (Real.exp_pos _).le
  set C := M / θ * Real.exp (θ * Bd) with hC
  have hC0 : 0 ≤ C := by positivity
  have hint : ∀ n, Integrable (fun d : Path => C * Real.exp (θ * W r d n)) (pathLaw μ) := by
    intro n
    refine (Integrable.of_bound (by
      exact ((Real.continuous_exp.measurable.comp ((measurable_W' r n).const_mul θ))).aestronglyMeasurable)
      (Real.exp (θ * (r * n))) ?_).const_mul C
    filter_upwards [ae_path_nonneg μ] with d hd
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hθ.le)
    unfold W
    calc ∑ j ∈ Finset.range n, (r - d j) ≤ ∑ _j ∈ Finset.range n, r :=
          Finset.sum_le_sum fun j _ => by linarith [hd j]
      _ = r * n := by simp [mul_comm]
  have hbound : ∀ n, ∫⁻ d, ENNReal.ofReal (M * max 0 (Bd + W r d n)) ∂pathLaw μ ≤
      ENNReal.ofReal (C * φ ^ n) := by
    intro n
    calc _ ≤ ∫⁻ d, ENNReal.ofReal (C * Real.exp (θ * W r d n)) ∂pathLaw μ := by
          refine lintegral_mono fun d => ENNReal.ofReal_le_ofReal ?_
          set u := Bd + W r d n
          have h1 : max 0 u ≤ Real.exp (θ * u) / θ := by
            rw [le_div_iff₀ hθ]
            rcases le_total u 0 with hu | hu
            · rw [max_eq_left hu, zero_mul]; exact (Real.exp_pos _).le
            · rw [max_eq_right hu]; linarith [Real.add_one_le_exp (θ * u)]
          have h2 : Real.exp (θ * u) = Real.exp (θ * Bd) * Real.exp (θ * W r d n) := by
            rw [← Real.exp_add]; congr 1; simp only [u]; ring
          calc M * max 0 u ≤ M * (Real.exp (θ * u) / θ) := mul_le_mul_of_nonneg_left h1 hM
            _ = C * Real.exp (θ * W r d n) := by rw [h2, hC]; field_simp
      _ = ENNReal.ofReal (C * φ ^ n) := by
          rw [← ofReal_integral_eq_lintegral_ofReal (hint n)
            (Eventually.of_forall fun d => by positivity), integral_const_mul, W_exp]
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (C * φ ^ n)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal ((tendsto_pow_atTop_nhds_zero_of_lt_one hφ0 hφ1).const_mul C)
    rwa [mul_zero, ENNReal.ofReal_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => bot_le) hbound

/-! ## Zero drift: `𝔼[Z^r_∞] = ∞` -/

lemma measurable_sh : Measurable sh := measurable_pi_lambda _ fun n => measurable_pi_apply (n + 1)

lemma mp_shift (μ : DemandLaw) : MeasurePreserving sh (pathLaw μ) (pathLaw μ) := by
  refine ⟨measurable_sh, ?_⟩
  conv_rhs => rw [pathLaw]
  apply Measure.eq_infinitePi
  intro s t ht
  classical
  rw [Measure.map_apply measurable_sh (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  have hpre : sh ⁻¹' (Set.pi ↑s t) = Set.pi ↑(s.image (· + 1)) (fun n => t (n - 1)) := by
    ext d
    simp [sh, Set.mem_pi]
  rw [hpre]
  unfold pathLaw
  rw [Measure.infinitePi_pi _ (fun n _ => ht (n - 1)),
    Finset.prod_image (fun a _ b _ h => by simpa using h)]
  simp

lemma lintegral_indep (μ : DemandLaw) (f : ℝ → ℝ≥0∞) (g : Path → ℝ≥0∞) (hf : Measurable f)
    (hg : Measurable g) :
    ∫⁻ d, f (d 0) * g (sh d) ∂pathLaw μ = (∫⁻ x, f x ∂μ.law) * ∫⁻ d, g d ∂pathLaw μ := by
  have hF : Measurable (fun d : Path => f (d 0) * g (sh d)) :=
    (hf.comp (measurable_pi_apply 0)).mul (hg.comp measurable_sh)
  rw [← (mp_mix μ 0 1).lintegral_comp hF]
  have h0 : ∀ p y : Path, mix 0 1 p y 0 = y 0 := fun p y => by simp [mix]
  have h1 : ∀ p y : Path, sh (mix 0 1 p y) = sh p := fun p y => by
    funext n; simp only [sh, mix]; rw [if_neg (by omega)]
  simp only [h0, h1]
  rw [show (fun q : Path × Path => f (q.2 0) * g (sh q.1)) =
    (fun q : Path × Path => (g ∘ sh) q.1 * (f ∘ fun y : Path => y 0) q.2) from
      funext fun q => by simp [mul_comm]]
  rw [lintegral_prod_mul (hg.comp measurable_sh).aemeasurable
    (hf.comp (measurable_pi_apply 0)).aemeasurable]
  show (∫⁻ x, g (sh x) ∂pathLaw μ) * ∫⁻ y, f (y 0) ∂pathLaw μ = _
  rw [(mp_shift μ).lintegral_comp hg, (mp_eval μ 0).lintegral_comp hf, mul_comm]

lemma Zinf_rec (r : ℝ) (d : Path) (h : Zinf r (sh d) ≠ ⊤) :
    Zinf r d ≠ ⊤ ∧ (Zinf r d).toReal = max 0 ((r - d 0) + (Zinf r (sh d)).toReal) := by
  set v := max 0 ((r - d 0) + (Zinf r (sh d)).toReal) with hv
  have hle : ∀ n, Zb r d n ≤ v := by
    intro n
    cases n with
    | zero => simp [Zb, hv]
    | succ n =>
      rw [Zb_front]
      exact max_le_max le_rfl (by linarith [Zb_le_toReal r (sh d) h n])
  have hfin : Zinf r d ≠ ⊤ := by
    rw [Zinf_eq_iSup]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (iSup_le fun n => ENNReal.ofReal_le_ofReal (hle n))
  refine ⟨hfin, ?_⟩
  have h1 : Tendsto (fun n => Zb r d (n + 1)) atTop (𝓝 v) := by
    simp only [Zb_front]
    exact ((continuous_const.max (continuous_const.add continuous_id)).tendsto _).comp
      (tendsto_Zb_real r (sh d) h)
  have h2 : Tendsto (fun n => Zb r d (n + 1)) atTop (𝓝 (Zinf r d).toReal) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_Zb_real r d hfin)
  exact tendsto_nhds_unique h2 h1

lemma max0_eq (u : ℝ) : max 0 u = u + max (-u) 0 := by
  rcases le_total 0 u with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]; ring
  · rw [max_eq_left h, max_eq_left (by linarith)]; ring

lemma Zinf_lintegral_top (μ : DemandLaw) (r : ℝ) (hr : r = μ.mean) :
    ∫⁻ d, Zinf r d ∂pathLaw μ = ⊤ := by
  by_contra hfin
  have hmZ := measurable_Zinf' r
  have hae1 : ∀ᵐ d ∂pathLaw μ, Zinf r d < ⊤ := ae_lt_top hmZ hfin
  have hae2 : ∀ᵐ d ∂pathLaw μ, Zinf r (sh d) < ⊤ :=
    ae_of_ae_map (mp_shift μ).measurable.aemeasurable (by rw [(mp_shift μ).map_eq]; exact hae1)
  set Zr : Path → ℝ := fun d => (Zinf r d).toReal with hZr
  have hZrm : Measurable Zr := hmZ.ennreal_toReal
  have hZi : Integrable Zr (pathLaw μ) := integrable_toReal_of_lintegral_ne_top hmZ.aemeasurable hfin
  have hZsi : Integrable (fun d => Zr (sh d)) (pathLaw μ) :=
    ((mp_shift μ).integrable_comp hZrm.aestronglyMeasurable).2 hZi
  have hrel : ∀ᵐ d ∂pathLaw μ, Zr d = max 0 ((r - d 0) + Zr (sh d)) := by
    filter_upwards [hae2] with d hd
    exact (Zinf_rec r d hd.ne).2
  have hD0i : Integrable (fun d : Path => d 0) (pathLaw μ) :=
    ((mp_eval μ 0).integrable_comp (g := fun x : ℝ => x) measurable_id.aestronglyMeasurable).2 μ.integrable
  have hX : Integrable (fun d : Path => r - d 0) (pathLaw μ) := (integrable_const r).sub hD0i
  have hD0 : ∫ d, d 0 ∂pathLaw μ = μ.mean := by
    have hm := integral_map (μ := pathLaw μ) (mp_eval μ 0).measurable.aemeasurable
      (f := fun x : ℝ => x) measurable_id.aestronglyMeasurable
    rw [(mp_eval μ 0).map_eq] at hm
    rw [← hm]; rfl
  have hXint : ∫ d, (r - d 0) ∂pathLaw μ = 0 := by
    rw [integral_sub (integrable_const r) hD0i, hD0]; simp [hr]
  have hshint : ∫ d, Zr (sh d) ∂pathLaw μ = ∫ d, Zr d ∂pathLaw μ := by
    have hm := integral_map (μ := pathLaw μ) (mp_shift μ).measurable.aemeasurable
      (f := Zr) hZrm.aestronglyMeasurable
    rw [(mp_shift μ).map_eq] at hm
    exact hm.symm
  set u : Path → ℝ := fun d => (r - d 0) + Zr (sh d) with hu
  have hui : Integrable u (pathLaw μ) := hX.add hZsi
  have hneg : ∫ d, max (-u d) 0 ∂pathLaw μ = 0 := by
    have e1 : ∫ d, Zr d ∂pathLaw μ = ∫ d, (u d + max (-u d) 0) ∂pathLaw μ := by
      refine integral_congr_ae ?_
      filter_upwards [hrel] with d hd
      rw [hd, max0_eq]
    rw [integral_add hui hui.neg_part, hu, integral_add hX hZsi, hXint, hshint] at e1
    linarith
  have hnn : ∀ᵐ d ∂pathLaw μ, 0 ≤ u d := by
    have := (integral_eq_zero_iff_of_nonneg (fun d => le_max_right _ _) hui.neg_part).1 hneg
    filter_upwards [this] with d hd
    simp only [Pi.zero_apply] at hd
    have := le_max_left (-u d) 0
    linarith
  have hZeq : ∀ᵐ d ∂pathLaw μ, Zr d = u d := by
    filter_upwards [hrel, hnn] with d hd hn
    rw [hd, max_eq_right hn]
  -- Laplace transform
  set A := ∫⁻ d, ENNReal.ofReal (Real.exp (-Zr d)) ∂pathLaw μ with hA
  set B := ∫⁻ x, ENNReal.ofReal (Real.exp (x - r)) ∂μ.law with hB
  have hfm : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (x - r))) := by fun_prop
  have hgm : Measurable (fun d : Path => ENNReal.ofReal (Real.exp (-Zr d))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp hZrm.neg)
  have hAB : A = B * A := by
    rw [← lintegral_indep μ _ _ hfm hgm, hA]
    refine lintegral_congr_ae ?_
    filter_upwards [hZeq] with d hd
    rw [hd, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2; simp only [hu]; ring
  have hA0 : A ≠ 0 := by
    intro h0
    rw [hA, lintegral_eq_zero_iff hgm] at h0
    obtain ⟨d, hd⟩ := h0.exists
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hd
    linarith [Real.exp_pos (-Zr d)]
  have hAt : A ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.one_ne_top) ?_
    calc A ≤ ∫⁻ _d, (1 : ℝ≥0∞) ∂pathLaw μ := lintegral_mono fun d => by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.2 (by
            simp only [hZr, neg_nonpos]; exact ENNReal.toReal_nonneg))
      _ = 1 := by simp
  have hB1 : B = 1 := ((ENNReal.mul_left_inj hA0 hAt).1 (by rw [one_mul]; exact hAB)).symm
  have hEi : Integrable (fun x : ℝ => Real.exp (x - r)) μ.law :=
    (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
      (Eventually.of_forall fun x => (Real.exp_pos _).le)).1 (by rw [← hB, hB1]; exact ENNReal.one_ne_top)
  have hE1 : ∫ x, Real.exp (x - r) ∂μ.law = 1 := by
    have := ofReal_integral_eq_lintegral_ofReal hEi (Eventually.of_forall fun x => (Real.exp_pos _).le)
    rw [← hB, hB1, ENNReal.ofReal_eq_one] at this
    exact this
  have hIx : Integrable (fun x : ℝ => x) μ.law := μ.integrable
  have hI1 : Integrable (fun x : ℝ => x - r) μ.law := hIx.sub (integrable_const r)
  have hI2 : Integrable (fun x : ℝ => x - r + 1) μ.law := hI1.add (integrable_const 1)
  set f : ℝ → ℝ := fun x => Real.exp (x - r) - (x - r + 1) with hf
  have hfi : Integrable f μ.law := hEi.sub hI2
  have hf0 : ∫ x, f x ∂μ.law = 0 := by
    show ∫ x, (Real.exp (x - r) - (x - r + 1)) ∂μ.law = 0
    rw [integral_sub hEi hI2, integral_add hI1 (integrable_const 1),
      integral_sub hIx (integrable_const r), hE1]
    simp only [integral_const, measure_univ, ENNReal.toReal_one, one_smul, smul_eq_mul, probReal_univ]
    have : ∫ x, x ∂μ.law = μ.mean := rfl
    rw [this, hr]; ring
  have hfae := (integral_eq_zero_iff_of_nonneg (fun x => by
    simp only [hf, Pi.zero_apply]; linarith [Real.add_one_le_exp (x - r)]) hfi).1 hf0
  have hpt : ∀ᵐ x ∂μ.law, x ∈ ({r} : Set ℝ) := by
    filter_upwards [hfae] with x hx
    simp only [hf, Pi.zero_apply] at hx
    by_contra hne
    have : x - r ≠ 0 := fun h => hne (by simp only [Set.mem_singleton_iff]; linarith)
    linarith [Real.add_one_lt_exp this]
  have h1 : μ.law ({r} : Set ℝ)ᶜ = 0 := by
    rw [ae_iff] at hpt
    simpa [Set.compl_def] using hpt
  rw [prob_compl_eq_zero_iff (measurableSet_singleton _)] at h1
  exact lt_irrefl _ (h1 ▸ μ.nondegenerate r)

/-! ## Convergence of the expected newsvendor cost along the TBS dynamics -/

lemma Rm_nonneg (m0 : ℕ) (r : ℝ) (ω : Sample) (n : ℕ) : 0 ≤ Rm m0 r ω n := by
  cases n with
  | zero => simp [Rm]
  | succ n => exact le_max_left _ _

lemma V_bound (L₀ L : ℕ) (r S : ℝ) (hr0 : 0 ≤ r) (ω : Sample) (hD : ∀ n, 0 ≤ ω.1 n)
    (hD' : ∀ n, 0 ≤ ω.2.1 n) (k : ℕ) : V L₀ L r S ω k ≤ max 0 (-S) + r * k := by
  induction k with
  | zero =>
    simp only [V, P, Nat.cast_zero, mul_zero, add_zero]
    have : x0 ω ≤ 0 := by
      unfold x0; simp only [neg_nonpos]; exact Finset.sum_nonneg fun i _ => hD' i
    exact max_le_max le_rfl (by linarith)
  | succ k ih =>
    rw [V_succ]
    have h1 := rho_le L₀ L r hr0 k
    have h2 := hD k
    push_cast
    refine max_le (add_nonneg (le_max_left _ _) (mul_nonneg hr0 (by positivity))) ?_
    linarith

lemma measurable_V (L₀ L : ℕ) (r S : ℝ) (k : ℕ) : Measurable (fun ω : Sample => V L₀ L r S ω k) :=
  measurable_const.max ((measurable_P L₀ L r S k).sub_const _)

lemma integrable_V (μ : DemandLaw) (L₀ L : ℕ) (r S : ℝ) (k : ℕ) :
    Integrable (fun ω : Sample => V L₀ L r S ω k) (sampleLaw μ) :=
  (integrable_const 0).sup ((integrable_P μ L₀ L r S k).sub (integrable_const S))

lemma measurable_Rm (m0 : ℕ) (r : ℝ) (n : ℕ) : Measurable (fun ω : Sample => Rm m0 r ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact measurable_const.max (ih.add (measurable_const.sub
      ((measurable_pi_apply _).comp measurable_fst)))

lemma measurable_Wp (m0 : ℕ) (r : ℝ) (n : ℕ) : Measurable (fun ω : Sample => Wp m0 r ω n) := by
  unfold Wp
  exact Finset.measurable_sum _ fun j _ => measurable_const.sub
    ((measurable_pi_apply _).comp measurable_fst)

/-- `𝔼[H(max(S, P m))]`, the expected holding/backorder cost of period `m + L₀ + 1`. -/
noncomputable def EGm (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (r S : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (H μ κ L₀ (max S (P L₀ L r S ω m))) ∂sampleLaw μ

lemma H_upper (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (S v : ℝ) (hv : 0 ≤ v) :
    H μ κ L₀ (S + v) ≤ H μ κ L₀ S + max κ.b κ.h * v := by
  have := H_lip μ κ L₀ (S + v) S
  rwa [show S + v - S = v by ring, abs_of_nonneg hv] at this

lemma H_lower (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (S v : ℝ) :
    min κ.b κ.h * v ≤ H μ κ L₀ (S + v) + min κ.b κ.h * |SM μ L₀ - S| := by
  have h1 := H_ge μ κ L₀ (S + v)
  have hc : 0 ≤ min κ.b κ.h := (lt_min κ.b_pos κ.h_pos).le
  have h2 : min κ.b κ.h * (SM μ L₀ - S) ≤ min κ.b κ.h * |SM μ L₀ - S| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hc
  nlinarith

lemma EGm_ne_top (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (r S : ℝ) (k : ℕ) :
    EGm μ κ L₀ L r S k ≠ ⊤ := by
  unfold EGm
  refine ne_top_of_le_ne_top (((integrable_const (H μ κ L₀ S)).add
    ((integrable_V μ L₀ L r S k).const_mul (max κ.b κ.h))).lintegral_lt_top.ne)
    (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_)
  rw [max_eq_S_add_V]
  exact H_upper μ κ L₀ S _ (V_nonneg _ _ _ _ _ _)

lemma EG_tendsto (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (r S : ℝ) (hr0 : 0 ≤ r)
    (hr : r ≤ μ.mean) :
    Tendsto (fun m => EGm μ κ L₀ L r S m) atTop (𝓝 (∫⁻ d, Kfun μ κ L₀ r S d ∂pathLaw μ)) := by
  set m0 := L - L₀ - 1 with hm0
  rw [← tendsto_add_atTop_iff_nat m0]
  set x : ℕ → ℝ≥0∞ := fun n => ∫⁻ ω, ENNReal.ofReal (H μ κ L₀
    (S + max (V L₀ L r S ω m0 + Wp m0 r ω n) (Rm m0 r ω n))) ∂sampleLaw μ with hxdef
  have hx : ∀ n, EGm μ κ L₀ L r S (n + m0) = x n := by
    intro n; unfold EGm
    refine lintegral_congr fun ω => ?_
    rw [max_eq_S_add_V, add_comm n m0, hm0, lindley]
  refine Tendsto.congr (fun n => (hx n).symm) ?_
  set Mx := max κ.b κ.h with hMx
  set c1 := min κ.b κ.h with hc1
  have hMx0 : 0 ≤ Mx := le_max_of_le_left κ.b_pos.le
  have hc10 : 0 < c1 := lt_min κ.b_pos κ.h_pos
  set Bd := max 0 (-S) + r * m0 with hBd
  have hmeasx : ∀ n, Measurable (fun ω : Sample => ENNReal.ofReal (H μ κ L₀
      (S + max (V L₀ L r S ω m0 + Wp m0 r ω n) (Rm m0 r ω n)))) := fun n =>
    ENNReal.measurable_ofReal.comp ((continuous_H μ κ L₀).measurable.comp (measurable_const.add
      (((measurable_V L₀ L r S m0).add (measurable_Wp m0 r n)).max (measurable_Rm m0 r n))))
  rcases lt_or_eq_of_le hr with hlt | heq
  · -- negative drift
    set y : ℕ → ℝ≥0∞ := fun n =>
      ∫⁻ ω, ENNReal.ofReal (H μ κ L₀ (S + Rm m0 r ω n)) ∂sampleLaw μ with hydef
    set e : ℕ → ℝ≥0∞ := fun n =>
      ∫⁻ ω, ENNReal.ofReal (Mx * max 0 (Bd + Wp m0 r ω n)) ∂sampleLaw μ with hedef
    have hfH : Measurable (fun v : ℝ => ENNReal.ofReal (H μ κ L₀ (S + v))) :=
      ENNReal.measurable_ofReal.comp ((continuous_H μ κ L₀).measurable.comp
        (measurable_const.add measurable_id))
    have hfe : Measurable (fun w : ℝ => ENNReal.ofReal (Mx * max 0 (Bd + w))) := by fun_prop
    have hy : Tendsto y atTop (𝓝 (∫⁻ d, Kfun μ κ L₀ r S d ∂pathLaw μ)) := by
      refine (g_tendsto μ κ L₀ r S).congr fun n => ?_
      exact (E_Rm μ m0 r n (fun v => ENNReal.ofReal (H μ κ L₀ (S + v))) hfH).symm
    have he : Tendsto e atTop (𝓝 0) := by
      refine (err_tendsto μ r hr0 hlt Bd Mx hMx0).congr fun n => ?_
      exact (E_Wp μ m0 r n (fun w => ENNReal.ofReal (Mx * max 0 (Bd + w))) hfe).symm
    have hme : ∀ n, Measurable (fun ω : Sample => ENNReal.ofReal (Mx * max 0 (Bd + Wp m0 r ω n))) :=
      fun n => hfe.comp (measurable_Wp m0 r n)
    have hdiff : ∀ ω : Sample, (∀ n, 0 ≤ ω.1 n) → (∀ n, 0 ≤ ω.2.1 n) → ∀ n,
        |(S + max (V L₀ L r S ω m0 + Wp m0 r ω n) (Rm m0 r ω n)) - (S + Rm m0 r ω n)| ≤
          max 0 (Bd + Wp m0 r ω n) := by
      intro ω hD hD' n
      have hA : V L₀ L r S ω m0 + Wp m0 r ω n ≤ Bd + Wp m0 r ω n := by
        have := V_bound L₀ L r S hr0 ω hD hD' m0; linarith
      have hR := Rm_nonneg m0 r ω n
      set A := V L₀ L r S ω m0 + Wp m0 r ω n
      set R := Rm m0 r ω n
      rw [show S + max A R - (S + R) = max A R - R by ring,
        abs_of_nonneg (by linarith [le_max_right A R])]
      rcases le_total A R with h | h
      · rw [max_eq_right h, sub_self]; exact le_max_left _ _
      · rw [max_eq_left h]; exact le_max_of_le_right (by linarith)
    have hup : ∀ n, x n ≤ y n + e n := by
      intro n
      rw [hydef, hedef, ← lintegral_add_right _ (hme n)]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_good μ] with ω hω
      rw [← ENNReal.ofReal_add (H_nonneg _ _ _ _) (mul_nonneg hMx0 (le_max_left _ _))]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := H_lip μ κ L₀ (S + max (V L₀ L r S ω m0 + Wp m0 r ω n) (Rm m0 r ω n))
        (S + Rm m0 r ω n)
      have h2 := mul_le_mul_of_nonneg_left (hdiff ω hω.1 hω.2 n) hMx0
      linarith
    have hlow : ∀ n, y n ≤ x n + e n := by
      intro n
      rw [hxdef, hedef, ← lintegral_add_right _ (hme n)]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_good μ] with ω hω
      rw [← ENNReal.ofReal_add (H_nonneg _ _ _ _) (mul_nonneg hMx0 (le_max_left _ _))]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := H_lip μ κ L₀ (S + Rm m0 r ω n)
        (S + max (V L₀ L r S ω m0 + Wp m0 r ω n) (Rm m0 r ω n))
      rw [abs_sub_comm] at h1
      have h2 := mul_le_mul_of_nonneg_left (hdiff ω hω.1 hω.2 n) hMx0
      linarith
    have hlo : Tendsto (fun n => y n - e n) atTop (𝓝 (∫⁻ d, Kfun μ κ L₀ r S d ∂pathLaw μ)) := by
      have := ENNReal.Tendsto.sub hy he (Or.inr ENNReal.zero_ne_top)
      rwa [tsub_zero] at this
    have hhi : Tendsto (fun n => y n + e n) atTop (𝓝 (∫⁻ d, Kfun μ κ L₀ r S d ∂pathLaw μ)) := by
      have := hy.add he
      rwa [add_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
      (fun n => tsub_le_iff_right.2 (hlow n)) hup
  · -- zero drift
    have hZ := Zinf_lintegral_top μ r heq
    set C := c1 * |SM μ L₀ - S| with hC
    have hC0 : 0 ≤ C := mul_nonneg hc10.le (abs_nonneg _)
    have hpt : ∀ v : ℝ, 0 ≤ v →
        ENNReal.ofReal c1 * ENNReal.ofReal v ≤ ENNReal.ofReal (H μ κ L₀ (S + v)) + ENNReal.ofReal C := by
      intro v hv
      rw [← ENNReal.ofReal_mul hc10.le, ← ENNReal.ofReal_add (H_nonneg _ _ _ _) hC0]
      exact ENNReal.ofReal_le_ofReal (H_lower μ κ L₀ S v)
    have hc1ne : ENNReal.ofReal c1 ≠ 0 := by simp [hc10]
    have hℓ : ∫⁻ d, Kfun μ κ L₀ r S d ∂pathLaw μ = ⊤ := by
      have hk : ∀ d, ENNReal.ofReal c1 * Zinf r d ≤ Kfun μ κ L₀ r S d + ENNReal.ofReal C := by
        intro d
        by_cases htop : Zinf r d = ⊤
        · simp [Kfun, htop]
        · simp only [Kfun, htop, if_false]
          calc ENNReal.ofReal c1 * Zinf r d
              = ENNReal.ofReal c1 * ENNReal.ofReal (Zinf r d).toReal := by
                rw [ENNReal.ofReal_toReal htop]
            _ ≤ _ := hpt _ ENNReal.toReal_nonneg
      have h2 : ENNReal.ofReal c1 * ∫⁻ d, Zinf r d ∂pathLaw μ ≤
          ∫⁻ d, Kfun μ κ L₀ r S d ∂pathLaw μ + ENNReal.ofReal C := by
        rw [← lintegral_const_mul _ (measurable_Zinf' r)]
        calc _ ≤ ∫⁻ d, (Kfun μ κ L₀ r S d + ENNReal.ofReal C) ∂pathLaw μ := lintegral_mono hk
          _ = _ := by rw [lintegral_add_right _ measurable_const]; simp
      rw [hZ, ENNReal.mul_top hc1ne, top_le_iff] at h2
      by_contra hne
      exact (ENNReal.add_ne_top.2 ⟨hne, ENNReal.ofReal_ne_top⟩) h2
    rw [hℓ]
    have hR : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (Rm m0 r ω n) ∂sampleLaw μ) atTop (𝓝 ⊤) := by
      rw [← hZ]
      refine Tendsto.congr (fun n => (E_Rm μ m0 r n ENNReal.ofReal ENNReal.measurable_ofReal).symm) ?_
      exact lintegral_tendsto_of_tendsto_of_monotone
        (fun n => (ENNReal.measurable_ofReal.comp (measurable_Zb r n)).aemeasurable)
        (Eventually.of_forall fun d a b hab => ENNReal.ofReal_le_ofReal (Zb_mono r d hab))
        (Eventually.of_forall fun d => tendsto_Zb r d)
    have hR2 : Tendsto (fun n => ENNReal.ofReal c1 * ∫⁻ ω, ENNReal.ofReal (Rm m0 r ω n) ∂sampleLaw μ)
        atTop (𝓝 ⊤) := by
      have := ENNReal.Tendsto.const_mul hR (Or.inl ENNReal.top_ne_zero) (a := ENNReal.ofReal c1)
      rwa [ENNReal.mul_top hc1ne] at this
    have hle : ∀ n, ENNReal.ofReal c1 * ∫⁻ ω, ENNReal.ofReal (Rm m0 r ω n) ∂sampleLaw μ ≤
        x n + ENNReal.ofReal C := by
      intro n
      have hmR : Measurable (fun ω : Sample => ENNReal.ofReal (Rm m0 r ω n)) :=
        ENNReal.measurable_ofReal.comp (measurable_Rm m0 r n)
      rw [← lintegral_const_mul _ hmR]
      calc ∫⁻ ω, ENNReal.ofReal c1 * ENNReal.ofReal (Rm m0 r ω n) ∂sampleLaw μ
          ≤ ∫⁻ ω, (ENNReal.ofReal (H μ κ L₀
              (S + max (V L₀ L r S ω m0 + Wp m0 r ω n) (Rm m0 r ω n))) + ENNReal.ofReal C)
              ∂sampleLaw μ := lintegral_mono fun ω => by
            have hRA := le_max_right (V L₀ L r S ω m0 + Wp m0 r ω n) (Rm m0 r ω n)
            calc ENNReal.ofReal c1 * ENNReal.ofReal (Rm m0 r ω n)
                ≤ ENNReal.ofReal c1 *
                    ENNReal.ofReal (max (V L₀ L r S ω m0 + Wp m0 r ω n) (Rm m0 r ω n)) :=
                  by gcongr
              _ ≤ _ := hpt _ ((Rm_nonneg m0 r ω n).trans hRA)
        _ = x n + ENNReal.ofReal C := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    have h3 : Tendsto (fun n => x n + ENNReal.ofReal C) atTop (𝓝 ⊤) :=
      tendsto_nhds_top_mono hR2 (Eventually.of_forall hle)
    have h4 := ENNReal.Tendsto.sub h3 (tendsto_const_nhds (x := ENNReal.ofReal C))
      (Or.inr ENNReal.ofReal_ne_top)
    rw [ENNReal.top_sub ENNReal.ofReal_ne_top] at h4
    exact h4.congr fun n => ENNReal.add_sub_cancel_right ENNReal.ofReal_ne_top

/-! ## Cesàro averages -/

lemma ratio_tendsto (L₀ : ℕ) : Tendsto (fun T : ℕ => ((T - L₀ : ℕ) : ℝ) / T) atTop (𝓝 1) := by
  have e : ∀ᶠ T : ℕ in atTop, 1 - (L₀ : ℝ) / T = ((T - L₀ : ℕ) : ℝ) / T := by
    filter_upwards [eventually_ge_atTop (L₀ + 1)] with T hT
    have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast (by omega : T ≠ 0)
    rw [Nat.cast_sub (by omega)]
    field_simp
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_const_div_atTop_nhds_zero_nat (L₀ : ℝ))
  rw [sub_zero] at h
  exact h.congr' e

lemma cesaro_fin (b : ℕ → ℝ≥0∞) (ℓ : ℝ≥0∞) (hℓ : ℓ ≠ ⊤) (hb : ∀ k, b k ≠ ⊤)
    (h : Tendsto b atTop (𝓝 ℓ)) (L₀ : ℕ) :
    Tendsto (fun T : ℕ => (∑ k ∈ Finset.range (T - L₀), b k) / T) atTop (𝓝 ℓ) := by
  set u : ℕ → ℝ := fun k => (b k).toReal with hu
  have hut : Tendsto u atTop (𝓝 ℓ.toReal) := (ENNReal.tendsto_toReal hℓ).comp h
  have hc := (hut.cesaro).comp (tendsto_sub_atTop_nat L₀)
  have hr := (ratio_tendsto L₀).mul hc
  rw [one_mul] at hr
  have hreal : Tendsto (fun T : ℕ => (∑ k ∈ Finset.range (T - L₀), u k) / T) atTop
      (𝓝 ℓ.toReal) := by
    refine hr.congr' ?_
    filter_upwards [eventually_ge_atTop (L₀ + 1)] with T hT
    simp only [Function.comp]
    have h1 : ((T - L₀ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : T - L₀ ≠ 0)
    have h2 : (T : ℝ) ≠ 0 := by exact_mod_cast (by omega : T ≠ 0)
    field_simp
  have := ENNReal.tendsto_ofReal hreal
  rw [ENNReal.ofReal_toReal hℓ] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop (L₀ + 1)] with T hT
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  rw [ENNReal.ofReal_div_of_pos hT0, ENNReal.ofReal_sum_of_nonneg (fun k _ => ENNReal.toReal_nonneg),
    ENNReal.ofReal_natCast]
  congr 1
  exact Finset.sum_congr rfl fun k _ => ENNReal.ofReal_toReal (hb k)

lemma cesaro_top (b : ℕ → ℝ≥0∞) (h : Tendsto b atTop (𝓝 ⊤)) (L₀ : ℕ) :
    Tendsto (fun T : ℕ => (∑ k ∈ Finset.range (T - L₀), b k) / T) atTop (𝓝 ⊤) := by
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro x
  set Mx : ℝ≥0∞ := (x : ℝ≥0∞) + 1 with hMxd
  have hMx : Mx ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top, ENNReal.one_ne_top⟩
  have hb' : Tendsto (fun k => min (b k) Mx) atTop (𝓝 Mx) := by
    have := h.min (tendsto_const_nhds (x := Mx))
    rwa [min_eq_right le_top] at this
  have hc := cesaro_fin (fun k => min (b k) Mx) Mx hMx
    (fun k => ne_top_of_le_ne_top hMx (min_le_right _ _)) hb' L₀
  have hlt : (x : ℝ≥0∞) < Mx := ENNReal.lt_add_right ENNReal.coe_ne_top one_ne_zero
  filter_upwards [hc.eventually (lt_mem_nhds hlt)] with T hT
  exact lt_of_lt_of_le hT (ENNReal.div_le_div_right (Finset.sum_le_sum fun k _ => min_le_left _ _) _)

lemma express_tendsto (Q : ℕ → ℝ) (a B : ℝ) (hQ : ∀ N, |Q N - N * a| ≤ B) (L₀ : ℕ) :
    Tendsto (fun T : ℕ => Q (T - L₀) / T) atTop (𝓝 a) := by
  have h1 := (ratio_tendsto L₀).const_mul a
  have h2 : Tendsto (fun T : ℕ => (Q (T - L₀) - ((T - L₀ : ℕ) : ℝ) * a) / T) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun T => ?_) (tendsto_const_div_atTop_nhds_zero_nat B)
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (hQ _) (Nat.cast_nonneg T)
  have := h1.add h2
  rw [mul_one, add_zero] at this
  refine this.congr fun T => ?_
  ring

/-! ## The express-order part -/

lemma E_D (μ : DemandLaw) (k : ℕ) : ∫ ω, ω.1 k ∂sampleLaw μ = μ.mean := by
  have hmp := (mp_eval μ k).comp (mp_fst μ)
  have hm := integral_map (μ := sampleLaw μ) hmp.measurable.aemeasurable
    (f := fun x : ℝ => x) measurable_id.aestronglyMeasurable
  rw [hmp.map_eq] at hm
  exact hm.symm

lemma sum_q (μ : DemandLaw) (L₀ L : ℕ) (r S : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, ∫ ω, q L₀ L r S ω k ∂sampleLaw μ =
      ∫ ω, P L₀ L r S ω N ∂sampleLaw μ - ∫ ω, x0 ω ∂sampleLaw μ + N * μ.mean -
        ∑ k ∈ Finset.range N, rho L₀ L r k := by
  have hpt : ∀ ω, ∑ k ∈ Finset.range N, q L₀ L r S ω k =
      P L₀ L r S ω N - x0 ω + ∑ k ∈ Finset.range N, ω.1 k - ∑ k ∈ Finset.range N, rho L₀ L r k := by
    intro ω
    have h := P_add L₀ L r S ω 0 N
    simp only [zero_add] at h
    have hP0 : P L₀ L r S ω 0 = x0 ω := rfl
    rw [h, hP0, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  have hDs : Integrable (fun ω : Sample => ∑ k ∈ Finset.range N, ω.1 k) (sampleLaw μ) :=
    integrable_finsetSum _ fun k _ => integrable_D μ k
  rw [← integral_finsetSum _ (fun k _ => integrable_q μ L₀ L r S k)]
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  have i1 : Integrable (fun ω : Sample => P L₀ L r S ω N - x0 ω) (sampleLaw μ) :=
    (integrable_P μ L₀ L r S N).sub (integrable_x0 μ)
  have i2 : Integrable (fun ω : Sample => P L₀ L r S ω N - x0 ω + ∑ k ∈ Finset.range N, ω.1 k)
      (sampleLaw μ) := i1.add hDs
  rw [integral_sub i2 (integrable_const _), integral_add i1 hDs,
    integral_sub (integrable_P μ L₀ L r S N) (integrable_x0 μ),
    integral_finsetSum _ (fun k _ => integrable_D μ k)]
  simp only [E_D, Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const, probReal_univ,
    one_smul, smul_eq_mul, one_mul]

lemma rho_sum (L₀ L : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (N : ℕ) :
    0 ≤ N * r - ∑ k ∈ Finset.range N, rho L₀ L r k ∧
      N * r - ∑ k ∈ Finset.range N, rho L₀ L r k ≤ (L - L₀ - 1 : ℕ) * r := by
  have hNr : (N : ℝ) * r = ∑ _k ∈ Finset.range N, r := by simp
  rw [hNr, ← Finset.sum_sub_distrib]
  constructor
  · exact Finset.sum_nonneg fun k _ => by linarith [rho_le L₀ L r hr0 k]
  · classical
    calc ∑ k ∈ Finset.range N, (r - rho L₀ L r k)
        ≤ ∑ k ∈ Finset.range N, (if k < L - L₀ - 1 then r else 0) :=
          Finset.sum_le_sum fun k _ => by
            split_ifs with h
            · linarith [rho_nonneg L₀ L r hr0 k]
            · rw [rho_of_ge L₀ L r k (by omega), sub_self]
      _ = ((Finset.range N).filter (fun k => k < L - L₀ - 1)).card * r := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (L - L₀ - 1 : ℕ) * r := by
          refine mul_le_mul_of_nonneg_right ?_ hr0
          exact_mod_cast (Finset.card_le_card (fun k hk => by
            simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢; exact hk.2)).trans
            (Finset.card_range _).le

lemma P_bound (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (r S : ℝ) (hr0 : 0 ≤ r) (U : ℝ)
    (hU : ∀ N, (EGm μ κ L₀ L r S N).toReal ≤ U) :
    ∃ B, ∀ N, |∫ ω, P L₀ L r S ω N ∂sampleLaw μ| ≤ B := by
  set c1 := min κ.b κ.h with hc1
  have hc10 : 0 < c1 := lt_min κ.b_pos κ.h_pos
  set C := c1 * |SM μ L₀ - S| with hC
  have hV : ∀ N, c1 * ∫ ω, V L₀ L r S ω N ∂sampleLaw μ ≤ U + C := by
    intro N
    have hHi : Integrable (fun ω : Sample => H μ κ L₀ (S + V L₀ L r S ω N)) (sampleLaw μ) := by
      refine ((integrable_const (H μ κ L₀ S)).add
        ((integrable_V μ L₀ L r S N).const_mul (max κ.b κ.h))).mono'
        ((continuous_H μ κ L₀).measurable.comp (measurable_const.add
          (measurable_V L₀ L r S N))).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (H_nonneg _ _ _ _)]
      exact H_upper μ κ L₀ S _ (V_nonneg _ _ _ _ _ _)
    have hEq : ∫ ω, H μ κ L₀ (S + V L₀ L r S ω N) ∂sampleLaw μ = (EGm μ κ L₀ L r S N).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => H_nonneg _ _ _ _)
        hHi.aestronglyMeasurable]
      unfold EGm
      congr 1
      refine lintegral_congr fun ω => ?_
      rw [max_eq_S_add_V]
    calc c1 * ∫ ω, V L₀ L r S ω N ∂sampleLaw μ = ∫ ω, c1 * V L₀ L r S ω N ∂sampleLaw μ :=
          (integral_const_mul _ _).symm
      _ ≤ ∫ ω, (H μ κ L₀ (S + V L₀ L r S ω N) + C) ∂sampleLaw μ :=
          integral_mono ((integrable_V μ L₀ L r S N).const_mul _) (hHi.add (integrable_const _))
            fun ω => H_lower μ κ L₀ S _
      _ = (EGm μ κ L₀ L r S N).toReal + C := by
          rw [integral_add hHi (integrable_const _), hEq]; simp
      _ ≤ U + C := by linarith [hU N]
  refine ⟨max |∫ ω, x0 ω ∂sampleLaw μ| (max (|S| + μ.mean) (|S| + (U + C) / c1)), fun N => ?_⟩
  have hup : ∫ ω, P L₀ L r S ω N ∂sampleLaw μ ≤ |S| + (U + C) / c1 := by
    have h1 : ∫ ω, P L₀ L r S ω N ∂sampleLaw μ ≤ ∫ ω, (S + V L₀ L r S ω N) ∂sampleLaw μ :=
      integral_mono (integrable_P μ L₀ L r S N) ((integrable_const S).add (integrable_V μ L₀ L r S N))
        fun ω => by rw [← max_eq_S_add_V]; exact le_max_right _ _
    rw [integral_add (integrable_const S) (integrable_V μ L₀ L r S N)] at h1
    simp only [integral_const, probReal_univ, one_smul, smul_eq_mul, one_mul] at h1
    have h2 : ∫ ω, V L₀ L r S ω N ∂sampleLaw μ ≤ (U + C) / c1 := by
      rw [le_div_iff₀ hc10, mul_comm]; exact hV N
    linarith [le_abs_self S]
  have hlow : -(max |∫ ω, x0 ω ∂sampleLaw μ| (|S| + μ.mean)) ≤ ∫ ω, P L₀ L r S ω N ∂sampleLaw μ := by
    cases N with
    | zero =>
      show _ ≤ ∫ ω, x0 ω ∂sampleLaw μ
      have := neg_abs_le (∫ ω, x0 ω ∂sampleLaw μ)
      linarith [le_max_left |∫ ω, x0 ω ∂sampleLaw μ| (|S| + μ.mean)]
    | succ k =>
      have h1 : ∫ ω, (S - ω.1 k) ∂sampleLaw μ ≤ ∫ ω, P L₀ L r S ω (k + 1) ∂sampleLaw μ :=
        integral_mono ((integrable_const S).sub (integrable_D μ k)) (integrable_P μ L₀ L r S (k + 1))
          fun ω => by
            simp only [P]
            linarith [le_max_left S (P L₀ L r S ω k), rho_nonneg L₀ L r hr0 k]
      rw [integral_sub (integrable_const S) (integrable_D μ k), E_D] at h1
      simp only [integral_const, probReal_univ, one_smul, smul_eq_mul, one_mul] at h1
      have := neg_abs_le S
      linarith [le_max_right |∫ ω, x0 ω ∂sampleLaw μ| (|S| + μ.mean)]
  rw [abs_le]
  constructor
  · have := max_le_max (le_refl |∫ ω, x0 ω ∂sampleLaw μ|) (le_max_left (|S| + μ.mean) (|S| + (U + C) / c1))
    linarith
  · have := le_max_right (|S| + μ.mean) (|S| + (U + C) / c1)
    have := le_max_right |∫ ω, x0 ω ∂sampleLaw μ| (max (|S| + μ.mean) (|S| + (U + C) / c1))
    linarith

/-! ## Main theorem -/

theorem main (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (hL : L₀ + 1 < L)
    (r S : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ μ.mean) :
    tbsCost μ κ L₀ L r S =
      ENNReal.ofReal (κ.c * (μ.mean - r)) + ∫⁻ d, Kfun μ κ L₀ r S d ∂pathLaw μ := by
  set ℓ := ∫⁻ d, Kfun μ κ L₀ r S d ∂pathLaw μ with hℓdef
  set Q : ℕ → ℝ := fun N => ∑ k ∈ Finset.range N, ∫ ω, q L₀ L r S ω k ∂sampleLaw μ with hQdef
  have hE : ∀ k, ∫⁻ ω, periodCost κ (tbsPolicy L₀ L r S) ω (k + L₀ + 1) ∂sampleLaw μ =
      ENNReal.ofReal (κ.c * ∫ ω, q L₀ L r S ω k ∂sampleLaw μ) + EGm μ κ L₀ L r S k := by
    intro k
    rw [lintegral_congr (fun ω => cost_formula κ L₀ L hL r S hr0 ω k)]
    have hmc : Measurable (fun ω : Sample => ENNReal.ofReal (κ.c * q L₀ L r S ω k)) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_q L₀ L r S k))
    rw [lintegral_add_left hmc, E_G]
    congr 1
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal
      ((integrable_q μ L₀ L r S k).const_mul _)
      (Eventually.of_forall fun ω => mul_nonneg κ.c_pos.le (q_nonneg _ _ _ _ _ _))]
  have hsum : ∀ T, ∑ t ∈ Finset.Icc (L₀ + 1) T,
      ∫⁻ ω, periodCost κ (tbsPolicy L₀ L r S) ω t ∂sampleLaw μ =
      ENNReal.ofReal (κ.c * Q (T - L₀)) + ∑ k ∈ Finset.range (T - L₀), EGm μ κ L₀ L r S k := by
    intro T
    have hIcc : Finset.Icc (L₀ + 1) T = Finset.Ico (L₀ + 1) (T + 1) := by
      ext t; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hIcc, Finset.sum_Ico_eq_sum_range, show T + 1 - (L₀ + 1) = T - L₀ by omega]
    rw [Finset.sum_congr rfl (fun k _ => by rw [show L₀ + 1 + k = k + L₀ + 1 by ring, hE k]),
      Finset.sum_add_distrib, hQdef]
    congr 1
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg κ.c_pos.le
      (integral_nonneg fun ω => q_nonneg _ _ _ _ _ _))]
  unfold tbsCost policyCost
  simp only [hsum, ENNReal.add_div]
  have hEG := EG_tendsto μ κ L₀ L r S hr0 hr
  rw [← hℓdef] at hEG
  by_cases hℓ : ℓ = ⊤
  · rw [hℓ, add_top]
    rw [hℓ] at hEG
    have h1 := cesaro_top _ hEG L₀
    exact (tendsto_nhds_top_mono h1 (Eventually.of_forall fun T => le_add_self)).limsup_eq
  · have h1 := cesaro_fin _ ℓ hℓ (EGm_ne_top μ κ L₀ L r S) hEG L₀
    have hbdd := ((ENNReal.tendsto_toReal hℓ).comp hEG).bddAbove_range
    obtain ⟨U, hU⟩ := hbdd
    obtain ⟨B, hB⟩ := P_bound μ κ L₀ L r S hr0 U (fun N => hU ⟨N, rfl⟩)
    have hQ : ∀ N, |Q N - N * (μ.mean - r)| ≤
        B + |∫ ω, x0 ω ∂sampleLaw μ| + (L - L₀ - 1 : ℕ) * r := by
      intro N
      have hs := sum_q μ L₀ L r S N
      have hρ := rho_sum L₀ L r hr0 N
      simp only [hQdef]
      rw [hs]
      have e : ∫ ω, P L₀ L r S ω N ∂sampleLaw μ - ∫ ω, x0 ω ∂sampleLaw μ + N * μ.mean -
          ∑ k ∈ Finset.range N, rho L₀ L r k - N * (μ.mean - r) =
          ∫ ω, P L₀ L r S ω N ∂sampleLaw μ - ∫ ω, x0 ω ∂sampleLaw μ +
            (N * r - ∑ k ∈ Finset.range N, rho L₀ L r k) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      refine add_le_add ((abs_sub _ _).trans (add_le_add (hB N) le_rfl)) ?_
      rw [abs_of_nonneg hρ.1]; exact hρ.2
    have h2 : Tendsto (fun T : ℕ => ENNReal.ofReal (κ.c * Q (T - L₀)) / T) atTop
        (𝓝 (ENNReal.ofReal (κ.c * (μ.mean - r)))) := by
      have hr' := express_tendsto Q (μ.mean - r) _ hQ L₀
      have := ENNReal.tendsto_ofReal (hr'.const_mul κ.c)
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with T hT
      have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
      rw [← mul_div_assoc, ENNReal.ofReal_div_of_pos hT0, ENNReal.ofReal_natCast]
    exact (h2.add h1).limsup_eq

end XGCF

open XinGoldbergTBS.Asymptotic in
theorem solution (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (hL : L₀ + 1 < L)
    (r S : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ μ.mean) :
    tbsCost μ κ L₀ L r S =
      ENNReal.ofReal (κ.c * (μ.mean - r)) +
        ∫⁻ p : Path × (Fin (L₀ + 1) → ℝ),
          (if Zinf r p.1 = ⊤ then ⊤
            else ENNReal.ofReal (G κ ((Zinf r p.1).toReal + S - ∑ i, p.2 i)))
          ∂((pathLaw μ).prod (sumLaw μ L₀)) := by
  rw [XGCF.rhs_eq]
  exact XGCF.main μ κ L₀ L hL r S hr0 hr

