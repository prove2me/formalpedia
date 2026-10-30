-- Prove2me | solution 1 for SkipFreeFluct.MBI.theorem_5_4_gf
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T10:29:57.161185+00:00
-- url     : https://prove2.me/submissions/757bd68b-093f-47d4-8beb-95a19e8c0495

import Mathlib
import Definitions.Def_SkipFreeFluct_MBI_Chain
import Definitions.Def_SkipFreeFluct_MBI_Model
import Theorems.Thm_SkipFreeFluct_MBI_lemma_5_1
open scoped ENNReal Topology
open Filter MeasureTheory

namespace MBI54A
open SkipFreeFluct.MBI Finset

lemma abs_varpi_le (P : MBIParams) (hk : ∀ k, 0 ≤ kappa P k) :
    ∀ n, |varpi P n| ≤ piSeq P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [varpi, piSeq]
    | succ k =>
      rw [varpi, piSeq]
      have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / ((k:ℝ) + 1))]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_of_nonneg (hk j)]
      exact mul_le_mul_of_nonneg_right (ih _ (by omega)) (hk j)

lemma cauchy_term (a b : ℕ → ℝ) (v : ℝ) (n : ℕ) :
    ∑ k ∈ range (n + 1), (a k * v ^ k) * (b (n - k) * v ^ (n - k)) = conv b a n * v ^ n := by
  unfold conv
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by have := Finset.mem_range.1 hk; omega
  have : v ^ n = v ^ k * v ^ (n - k) := by rw [← pow_add]; congr 1; omega
  rw [this]; ring

end MBI54A

open SkipFreeFluct.MBI Finset MBI54A in
theorem solution (P : MBIParams) (hP : P.Valid) :
    ∀ x : ℕ, ∀ s ∈ Set.Ico 0 (s0 P),
      HasSum (fun y : ℕ => calH P y x * s ^ y)
        (∫ v in (0 : ℝ)..s,
          v ^ x / psi P v * Real.exp (∫ u in v..s, phiImm P u / psi P u)) := by
  obtain ⟨hnn, hgf⟩ := lemma_5_1 P hP
  intro x s hs
  have hs0 : 0 ≤ s := hs.1
  set f : ℝ → ℝ := fun u => phiImm P u / psi P u with hf_def
  have hmem : ∀ v ∈ Set.Icc 0 s, v ∈ Set.Ico 0 (s0 P) := fun v hv => ⟨hv.1, hv.2.trans_lt hs.2⟩
  have hk : ∀ k, 0 ≤ kappa P k := fun k => (hnn k).2.2.1
  have hpi : ∀ k, 0 ≤ piSeq P k := fun k => (hnn k).2.2.2
  have hW : ∀ k, 0 ≤ W P k := fun k => (hnn k).2.1
  have hvarpi := abs_varpi_le P hk
  -- summability facts at a point v ∈ [0, s]
  have hWsum : ∀ v ∈ Set.Icc 0 s, Summable (fun k => ‖W P k * v ^ k‖) := by
    intro v hv
    refine ((hgf v (hmem v hv)).2.1.summable).congr fun k => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (hW k) (pow_nonneg hv.1 _))]
  have hpisum : ∀ v ∈ Set.Icc 0 s, Summable (fun k => ‖piSeq P k * v ^ k‖) := by
    intro v hv
    refine ((hgf v (hmem v hv)).2.2.2.1.summable).congr fun k => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (hpi k) (pow_nonneg hv.1 _))]
  have hvpsum : ∀ v ∈ Set.Icc 0 s, Summable (fun k => ‖varpi P k * v ^ k‖) := by
    intro v hv
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) (hpisum v hv)
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (hpi k)]
    exact mul_le_mul_of_nonneg_right (hvarpi k) (norm_nonneg _)
  set c : ℕ → ℝ := fun l => conv (W P) (varpi P) l with hc_def
  set d : ℕ → ℝ := fun l => conv (W P) (piSeq P) l with hd_def
  have hcd : ∀ l, |c l| ≤ d l := by
    intro l
    simp only [hc_def, hd_def, conv]
    refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_of_nonneg (hW _)]
    exact mul_le_mul_of_nonneg_left (hvarpi j) (hW _)
  -- generating function of c = W ⋆ ϖ
  set G : ℝ → ℝ := fun v => v ^ x * (Real.exp (-∫ u in (0 : ℝ)..v, f u) * (1 / psi P v))
    with hG_def
  have hcgf : ∀ v ∈ Set.Icc 0 s, HasSum (fun l => c l * v ^ l)
      (Real.exp (-∫ u in (0 : ℝ)..v, f u) * (1 / psi P v)) := by
    intro v hv
    have h := hasSum_sum_range_mul_of_summable_norm (hvpsum v hv) (hWsum v hv)
    rw [(hgf v (hmem v hv)).2.2.2.2.tsum_eq, (hgf v (hmem v hv)).2.1.tsum_eq] at h
    simpa only [cauchy_term] using h
  have hdsum : Summable (fun l => d l * s ^ l) := by
    have h := summable_norm_sum_mul_range_of_summable_norm (hpisum s ⟨hs0, le_rfl⟩)
      (hWsum s ⟨hs0, le_rfl⟩)
    simp only [cauchy_term] at h
    exact h.of_norm
  -- termwise integration
  have hint : HasSum (fun l => ∫ v in (0 : ℝ)..s, c l * v ^ (x + l)) (∫ v in (0 : ℝ)..s, G v) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun l _ => d l * s ^ (x + l)) (fun l => ?_) (fun l => ?_) ?_ ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by fun_prop))
    · refine Filter.Eventually.of_forall fun t ht => ?_
      rw [Set.uIoc_of_le hs0] at ht
      rw [norm_mul, Real.norm_eq_abs, norm_pow, Real.norm_of_nonneg ht.1.le]
      exact mul_le_mul (hcd l) (pow_le_pow_left₀ ht.1.le ht.2 _) (pow_nonneg ht.1.le _)
        ((abs_nonneg _).trans (hcd l))
    · refine Filter.Eventually.of_forall fun t _ => ?_
      refine (hdsum.mul_left (s ^ x)).congr fun l => ?_
      rw [pow_add]; ring
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall fun t ht => ?_
      rw [Set.uIoc_of_le hs0] at ht
      have h := (hcgf t ⟨ht.1.le, ht.2⟩).mul_left (t ^ x)
      have he : (fun l => c l * t ^ (x + l)) = fun i => t ^ x * (c i * t ^ i) := by
        funext l; rw [pow_add]; ring
      rw [he]; exact h
  -- the integrated terms
  set b : ℕ → ℝ := fun l => c l * (s ^ (x + l + 1) / ((x : ℝ) + l + 1)) with hb_def
  have hbint : ∀ l, (∫ v in (0 : ℝ)..s, c l * v ^ (x + l)) = b l := by
    intro l
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp only [hb_def]
    congr 1
    rw [zero_pow (by omega), sub_zero]
    push_cast; ring_nf
  simp only [hbint] at hint
  -- Cauchy product with π*
  have hbn : Summable (fun l => ‖b l‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_)
      (hdsum.mul_left (s ^ (x + 1)))
    simp only [hb_def, norm_mul, Real.norm_eq_abs]
    have h1 : |s ^ (x + l + 1) / ((x : ℝ) + l + 1)| ≤ s ^ (x + 1) * s ^ l := by
      rw [abs_of_nonneg (by positivity)]
      rw [div_le_iff₀ (by positivity)]
      have : s ^ (x + 1) * s ^ l = s ^ (x + l + 1) := by rw [← pow_add]; congr 1; omega
      rw [this]
      have h2 : (1 : ℝ) ≤ (x : ℝ) + l + 1 := by linarith [(x.cast_nonneg : (0:ℝ) ≤ x), (l.cast_nonneg : (0:ℝ) ≤ l)]
      nlinarith [pow_nonneg hs0 (x + l + 1)]
    calc |c l| * |s ^ (x + l + 1) / ((x : ℝ) + l + 1)| ≤ d l * (s ^ (x + 1) * s ^ l) :=
          mul_le_mul (hcd l) h1 (abs_nonneg _) ((abs_nonneg _).trans (hcd l))
      _ = s ^ (x + 1) * (d l * s ^ l) := by ring
  have hprod := hasSum_sum_range_mul_of_summable_norm hbn (hpisum s ⟨hs0, le_rfl⟩)
  rw [hint.tsum_eq, (hgf s hs).2.2.2.1.tsum_eq] at hprod
  have hterm : ∀ m, calH P (m + (x + 1)) x * s ^ (m + (x + 1)) =
      ∑ k ∈ range (m + 1), b k * (piSeq P (m - k) * s ^ (m - k)) := by
    intro m
    unfold calH
    have e1 : m + (x + 1) - x = m + 1 := by omega
    rw [e1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ m := by have := Finset.mem_range.1 hl; omega
    have e2 : m + 1 - 1 - l = m - l := by omega
    rw [e2]
    simp only [hb_def, hc_def]
    have e3 : s ^ (m + (x + 1)) = s ^ (x + l + 1) * s ^ (m - l) := by
      rw [← pow_add]; congr 1; omega
    rw [e3]
    have : ((l : ℝ) + x + 1) = (x : ℝ) + l + 1 := by ring
    rw [this]
    ring
  have hfin : HasSum (fun y : ℕ => calH P y x * s ^ y)
      ((∫ v in (0 : ℝ)..s, G v) * Real.exp (∫ u in (0 : ℝ)..s, f u)) := by
    rw [← hasSum_nat_add_iff' (x + 1)]
    have hz : ∑ i ∈ range (x + 1), calH P i x * s ^ i = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have : i - x = 0 := by have := Finset.mem_range.1 hi; omega
      simp [calH, this]
    rw [hz, sub_zero]
    simp only [hterm]
    exact hprod
  convert hfin using 1
  have hcont : ContinuousOn f (Set.Icc 0 s) := by
    have hser : ContinuousOn (fun u => ∑' k, kappa P k * u ^ k) (Set.Icc 0 s) := by
      refine continuousOn_tsum (u := fun k => kappa P k * s ^ k) (fun k => by fun_prop)
        (hgf s hs).2.2.1.summable (fun k u hu => ?_)
      rw [norm_mul, Real.norm_of_nonneg (hk k), norm_pow, Real.norm_of_nonneg hu.1]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu.1 hu.2 _) (hk k)
    refine hser.congr fun u hu => ?_
    exact ((hgf u (hmem u hu)).2.2.1.tsum_eq).symm
  have hII : ∀ v ∈ Set.Icc 0 s, IntervalIntegrable f volume 0 v := by
    intro v hv
    refine (hcont.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le hv.1]
    exact Set.Icc_subset_Icc le_rfl hv.2
  rw [mul_comm, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun v hv => ?_
  rw [Set.uIcc_of_le hs0] at hv
  simp only [hG_def]
  rw [← intervalIntegral.integral_interval_sub_left (hII s ⟨hs0, le_rfl⟩) (hII v hv),
    Real.exp_sub, Real.exp_neg]
  ring
