-- Prove2me | solution 1 for OnlineMaxWeightMatch.Approx.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T15:00:08.989486+00:00
-- url     : https://prove2.me/submissions/efa37a63-bc0a-4db1-af8d-e5e05dc1378d

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Algorithm1
import Theorems.Thm_OnlineMaxWeightMatch_Approx_lemma_4_1
import Theorems.Thm_OnlineMaxWeightMatch_Approx_theorem_4_2

open MeasureTheory ProbabilityTheory

open OnlineMaxWeightMatch.Approx in
theorem solution {ι : Type*} [Fintype ι] {n : ℕ} (I : RideHailInstance ι n)
    (x : ι → Fin n → ℝ) (hopt : IsLPOptimal I x) :
    51 / 100 * optOn I ≤ algorithm1Value I x := by
  classical
  obtain ⟨hx, hval⟩ := hopt
  set X := augmentX I x with hX
  set J := augment I with hJ
  -- column sums
  have hcol : ∀ t, 0 ≤ I.p t - ∑ i, x i t := fun t => sub_nonneg.mpr (hx.ball_le_p t)
  -- cumX of a dummy bin
  have hcum_d : ∀ s t : Fin n, cumX X (Sum.inr s) t = if s < t then I.p s - ∑ i, x i s else 0 := by
    intro s t
    simp only [cumX, hX, augmentX, Sum.elim_inr]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_Iio]
  have hcum_i : ∀ (i : ι) t, cumX X (Sum.inl i) t = cumX x i t := by
    intro i t; simp [cumX, hX, augmentX]
  -- feasibility and tightness of the augmented solution
  have htight : ∀ t, ∑ j, X j t = J.p t := by
    intro t
    rw [Fintype.sum_sum_type]
    simp [hX, hJ, augmentX, augment]
  have hfeas : LPFeasible J X := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro (i | s)
      · simpa [hX, augmentX] using hx.bin_le_one i
      · simp only [hX, augmentX, Sum.elim_inr]
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_univ, if_true]
        have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hx.nonneg i s)
        linarith [I.p_le_one s]
    · intro t; rw [htight t]
    · rintro (i | s) t
      · rw [hcum_i]; simpa [hX, hJ, augmentX, augment] using hx.online i t
      · rw [hcum_d]
        simp only [hX, hJ, augmentX, augment, Sum.elim_inr]
        by_cases hst : s = t
        · subst hst
          simp only [if_true, lt_irrefl, if_false, sub_zero, mul_one]
          have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hx.nonneg i s)
          linarith
        · rw [if_neg hst]
          apply mul_nonneg (I.p_nonneg t)
          split_ifs
          · have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hx.nonneg i s)
            linarith [I.p_le_one s]
          · norm_num
    · rintro (i | s) t
      · simpa [hX, augmentX] using hx.nonneg i t
      · simp only [hX, augmentX, Sum.elim_inr]
        split_ifs with h
        · subst h; exact hcol s
        · exact le_rfl
  -- the measure is finite
  set μ := algMeasure J X with hμ
  have : IsFiniteMeasure μ := by
    constructor
    rw [hμ, algMeasure, Measure.finsetSum_apply]
    refine ENNReal.sum_lt_top.mpr (fun ω _ => ?_)
    simp [ENNReal.ofReal_lt_top]
  -- linearity of expectation
  have hlin : algorithm1Value I x =
      ∑ e : (ι ⊕ Fin n) × Fin n, J.w e.1 e.2 * μ.real {ω | e ∈ algMatching X ω} := by
    have h1 : ∀ ω, ∑ e ∈ algMatching X ω, J.w e.1 e.2 =
        ∑ e : (ι ⊕ Fin n) × Fin n,
          ({ω' | e ∈ algMatching X ω'} : Set (Outcome (ι ⊕ Fin n) n)).indicator
            (fun _ => J.w e.1 e.2) ω := by
      intro ω
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun e => e ∈ algMatching X ω)]
      rw [Finset.sum_eq_zero (s := Finset.univ.filter (fun e => e ∉ algMatching X ω))]
      · rw [add_zero]
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
        apply Finset.sum_congr rfl
        intro e he
        simp [Set.indicator, he]
      · intro e he
        simp only [Finset.mem_filter] at he
        simp [Set.indicator, he.2]
    have : algorithm1Value I x = ∫ ω, ∑ e ∈ algMatching X ω, J.w e.1 e.2 ∂μ := rfl
    rw [this]
    simp_rw [h1]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro e _
      rw [integral_indicator_const _ (MeasurableSpace.measurableSet_top), smul_eq_mul, mul_comm]
    · intro e _
      exact Integrable.of_finite
  -- per-edge guarantee
  have hedge := fun j t => OnlineMaxWeightMatch.Approx.theorem_4_2 J X hfeas htight j t
  have hlow : (1 / 2 + c) * lpObjective I x ≤ algorithm1Value I x := by
    rw [hlin, Fintype.sum_prod_type, Fintype.sum_sum_type]
    have hd : ∑ s : Fin n, ∑ t : Fin n, J.w (Sum.inr s) t *
        μ.real {ω | (Sum.inr s, t) ∈ algMatching X ω} = 0 := by
      simp [hJ, augment]
    rw [hd, add_zero, lpObjective, Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro t _
    have h := hedge (Sum.inl i) t
    have hw : J.w (Sum.inl i) t = I.w i t := by simp [hJ, augment]
    have hXi : X (Sum.inl i) t = x i t := by simp [hX, augmentX]
    rw [hw]
    rw [hXi] at h
    calc (1 / 2 + c) * (I.w i t * x i t) = I.w i t * (x i t * (1 / 2 + c)) := by ring
      _ ≤ I.w i t * μ.real {ω | (Sum.inl i, t) ∈ algMatching X ω} :=
          mul_le_mul_of_nonneg_left h (I.w_nonneg i t)
  have hopt' := OnlineMaxWeightMatch.Approx.lemma_4_1 I
  have hc : (1 / 2 + c : ℝ) = 51 / 100 := by rw [c]; norm_num
  rw [hc, hval] at hlow
  calc 51 / 100 * optOn I ≤ 51 / 100 * lpValue I := by linarith
    _ ≤ _ := hlow
