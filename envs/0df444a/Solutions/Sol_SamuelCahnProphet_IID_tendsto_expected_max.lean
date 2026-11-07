-- Prove2me | solution 1 for SamuelCahnProphet.IID.tendsto_expected_max
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T14:20:15.260211+00:00
-- url     : https://prove2.me/submissions/c0d2a671-9d9f-4245-9fe4-c2c84f824c84

import Mathlib
import Definitions.Def_SamuelCahnProphet_IID_Setting

open MeasureTheory Filter Topology
open SamuelCahnProphet.IID

lemma scp2_prod_range (q A : ENNReal) (i : ℕ) : ∀ N : ℕ, i < N →
    ∏ m ∈ Finset.range N, (if m < i then q else if m = i then A else 1) = q ^ i * A := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ N ih =>
    intro h
    rw [Finset.prod_range_succ]
    rcases Nat.lt_or_ge i N with hi | hi
    · rw [ih hi]
      have h1 : ¬ N < i := by omega
      have h2 : N ≠ i := by omega
      simp [h1, h2]
    · have hiN : i = N := by omega
      subst hiN
      have : ∀ m ∈ Finset.range i, (if m < i then q else if m = i then A else 1) = q := by
        intro m hm; simp [Finset.mem_range.1 hm]
      rw [Finset.prod_congr rfl this]
      simp

lemma scp2_pi_prod {N : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : Fin N → ℝ → ENNReal) (hg : ∀ j, Measurable (g j)) :
    ∫⁻ x, ∏ j, g j (x j) ∂(Measure.pi fun _ : Fin N => μ) = ∏ j, ∫⁻ y, g j y ∂μ := by
  have hind : ProbabilityTheory.iIndepFun (fun j (x : Fin N → ℝ) => g j (x j))
      (Measure.pi fun _ : Fin N => μ) :=
    ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin N => μ) (X := fun j y => g j y)
      (fun j => (hg j).aemeasurable)
  rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun j => (hg j).comp (measurable_pi_apply j))]
  congr 1; funext j
  exact (measurePreserving_eval (fun _ : Fin N => μ) j).lintegral_comp (hg j)

/-- General formula for a one-sided threshold-type stopping rule on i.i.d. coordinates. -/
lemma scp2_stop_formula {N : ℕ} [NeZero N] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (S : Set ℝ) (hS : MeasurableSet S) (τ : (Fin N → ℝ) → Fin N)
    (hτ : ∀ x i, τ x = i ↔ (∀ j, j < i → x j ∉ S) ∧ (x i ∈ S ∨ i = ⊤)) :
    ∫⁻ x, ENNReal.ofReal (x (τ x)) ∂(Measure.pi fun _ : Fin N => μ) =
      (∑ i ∈ Finset.range (N - 1), μ Sᶜ ^ i) * ∫⁻ y, S.indicator (fun y => ENNReal.ofReal y) y ∂μ
        + μ Sᶜ ^ (N - 1) * ∫⁻ y, ENNReal.ofReal y ∂μ := by
  classical
  set g : Fin N → Fin N → ℝ → ENNReal := fun i j y =>
    if j < i then Sᶜ.indicator 1 y else if j = i then
      (if i = ⊤ then ENNReal.ofReal y else S.indicator (fun y => ENNReal.ofReal y) y) else 1
    with hgdef
  have hgm : ∀ i j, Measurable (g i j) := by
    intro i j
    simp only [hgdef]
    split_ifs
    · exact measurable_one.indicator hS.compl
    · exact ENNReal.measurable_ofReal
    · exact ENNReal.measurable_ofReal.indicator hS
    · exact measurable_const
  have hpt : ∀ x : Fin N → ℝ, ENNReal.ofReal (x (τ x)) = ∑ i, ∏ j, g i j (x j) := by
    intro x
    rw [Finset.sum_eq_single (τ x)]
    · rw [Finset.prod_eq_single (τ x)]
      · simp only [hgdef, lt_irrefl, if_false, if_true]
        split_ifs with h
        · rfl
        · have := ((hτ x (τ x)).1 rfl).2
          rcases this with h' | h'
          · simp [Set.indicator_of_mem h']
          · exact absurd h' h
      · intro j _ hj
        have hτx := ((hτ x (τ x)).1 rfl).1
        simp only [hgdef, hj, if_false]
        split_ifs with hlt
        · simp [Set.indicator_of_mem (show x j ∈ Sᶜ from hτx j hlt)]
        · rfl
      · simp
    · intro i _ hi
      have hnot : ¬ ((∀ j, j < i → x j ∉ S) ∧ (x i ∈ S ∨ i = ⊤)) := fun h =>
        hi ((hτ x i).2 h).symm
      rw [not_and_or] at hnot
      rcases hnot with h | h
      · push Not at h
        obtain ⟨j, hj, hjS⟩ := h
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        simp [hgdef, hj, Set.indicator_of_notMem (show x j ∉ Sᶜ from fun h => h hjS)]
      · push Not at h
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hgdef, h.2, Set.indicator_of_notMem h.1]
    · simp
  simp_rw [hpt]
  rw [lintegral_finsetSum]
  swap
  · intro i _
    exact Finset.measurable_prod _ (fun j _ =>
      ((hgm i j).comp (measurable_pi_apply j) : Measurable (fun x : Fin N → ℝ => g i j (x j))))
  simp_rw [scp2_pi_prod μ _ (hgm _)]
  -- compute each product
  set A := ∫⁻ y, S.indicator (fun y => ENNReal.ofReal y) y ∂μ
  set B := ∫⁻ y, ENNReal.ofReal y ∂μ
  set q := μ Sᶜ
  have hint : ∀ i j : Fin N, ∫⁻ y, g i j y ∂μ =
      if j < i then q else if j = i then (if i = ⊤ then B else A) else 1 := by
    intro i j
    simp only [hgdef]
    split_ifs
    · rw [lintegral_indicator hS.compl]; simp [q]
    · rfl
    · rfl
    · simp
  simp_rw [hint]
  have hprod : ∀ i : Fin N, (∏ j : Fin N, (if j < i then q else if j = i then
      (if i = ⊤ then B else A) else 1)) = q ^ (i : ℕ) * (if i = ⊤ then B else A) := by
    intro i
    have := Fin.prod_univ_eq_prod_range (fun m => if m < (i : ℕ) then q else if m = (i : ℕ) then
      (if i = ⊤ then B else A) else 1) N
    rw [← scp2_prod_range q _ i N i.isLt, ← this]
    apply Finset.prod_congr rfl
    intro j _
    simp only [Fin.lt_def, Fin.ext_iff]
  simp_rw [hprod]
  have hN : N = N - 1 + 1 := (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne N))).symm
  have := Fin.sum_univ_eq_sum_range (fun m => q ^ m * (if m = N - 1 then B else A)) N
  have hcongr : ∀ i : Fin N, q ^ (i : ℕ) * (if i = ⊤ then B else A) =
      q ^ (i : ℕ) * (if (i : ℕ) = N - 1 then B else A) := by
    intro i; congr 2; simp [Fin.ext_iff, Fin.val_top]
  simp_rw [hcongr]
  rw [this]
  rw [show Finset.range N = Finset.range (N - 1 + 1) by rw [← hN]]
  rw [Finset.sum_range_succ, Finset.sum_mul]
  rw [if_pos rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  have : m ≠ N - 1 := by have := Finset.mem_range.1 hm; omega
  simp [this]

lemma scp2_min'_iff {N : ℕ} [NeZero N] (p : Fin N → Prop) [DecidablePred p] (i : Fin N)
    (h : (Finset.univ.filter (fun j : Fin N => p j ∨ j = ⊤)).Nonempty) :
    (Finset.univ.filter (fun j : Fin N => p j ∨ j = ⊤)).min' h = i ↔
      (∀ j, j < i → ¬ p j) ∧ (p i ∨ i = ⊤) := by
  constructor
  · rintro rfl
    refine ⟨fun j hj hpj => ?_, ?_⟩
    · have := Finset.min'_le (Finset.univ.filter (fun j : Fin N => p j ∨ j = ⊤)) j (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, Or.inl hpj⟩)
      exact absurd hj (not_lt.2 this)
    · have := Finset.min'_mem _ h
      rw [Finset.mem_filter] at this
      exact this.2
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · exact Finset.min'_le (Finset.univ.filter (fun j : Fin N => p j ∨ j = ⊤)) i (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h2⟩)
    · apply Finset.le_min'
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      by_contra hlt
      push Not at hlt
      rcases hj with hj | hj
      · exact h1 j hlt hj
      · subst hj; exact absurd hlt (not_lt.2 le_top)

lemma scp2_tIdx_iff {N : ℕ} [NeZero N] (x : Fin N → ℝ) (c : ℝ) (i : Fin N) :
    tIdx x c = i ↔ (∀ j, j < i → x j ∉ Set.Ici c) ∧ (x i ∈ Set.Ici c ∨ i = ⊤) := by
  unfold tIdx
  have := scp2_min'_iff (fun j => c ≤ x j) i ⟨⊤, by simp⟩
  simp only [Set.mem_Ici]
  exact this

lemma scp2_sIdx_iff {N : ℕ} [NeZero N] (x : Fin N → ℝ) (c : ℝ) (i : Fin N) :
    sIdx x c = i ↔ (∀ j, j < i → x j ∉ Set.Ioi c) ∧ (x i ∈ Set.Ioi c ∨ i = ⊤) := by
  unfold sIdx
  have := scp2_min'_iff (fun j => c < x j) i ⟨⊤, by simp⟩
  simp only [Set.mem_Ioi]
  exact this

lemma scp2_EstopT_formula {N : ℕ} [NeZero N] (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ) :
    EstopT μ N c =
      (∑ i ∈ Finset.range (N - 1), μ (Set.Ici c)ᶜ ^ i) *
          ∫⁻ y, (Set.Ici c).indicator (fun y => ENNReal.ofReal y) y ∂μ
        + μ (Set.Ici c)ᶜ ^ (N - 1) * ∫⁻ y, ENNReal.ofReal y ∂μ :=
  scp2_stop_formula μ _ measurableSet_Ici (fun x => tIdx x c) (fun x i => scp2_tIdx_iff x c i)

lemma scp2_EstopS_formula {N : ℕ} [NeZero N] (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ) :
    EstopS μ N c =
      (∑ i ∈ Finset.range (N - 1), μ (Set.Ioi c)ᶜ ^ i) *
          ∫⁻ y, (Set.Ioi c).indicator (fun y => ENNReal.ofReal y) y ∂μ
        + μ (Set.Ioi c)ᶜ ^ (N - 1) * ∫⁻ y, ENNReal.ofReal y ∂μ :=
  scp2_stop_formula μ _ measurableSet_Ioi (fun x => sIdx x c) (fun x i => scp2_sIdx_iff x c i)

lemma scp2_lintegral_threePoint (n a b c : ℝ) (f : ℝ → ENNReal) :
    ∫⁻ y, f y ∂(threePoint n a b c) = ENNReal.ofReal (1 - (b + c) / n) * f 0 +
      ENNReal.ofReal (c / n) * f a + ENNReal.ofReal (b / n) * f 1 := by
  simp [threePoint, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]

lemma scp2_threePoint_apply (n a b c : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    threePoint n a b c s = ENNReal.ofReal (1 - (b + c) / n) * s.indicator 1 0 +
      ENNReal.ofReal (c / n) * s.indicator 1 a + ENNReal.ofReal (b / n) * s.indicator 1 1 := by
  simp only [threePoint, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs]

lemma scp2_threePoint_prob (n a b c : ℝ) (hn : 0 < n) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hbc : b + c ≤ n) : IsProbabilityMeasure (threePoint n a b c) := by
  constructor
  simp only [threePoint, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  have h1 : 0 ≤ 1 - (b + c) / n := by
    rw [sub_nonneg, div_le_one hn]; exact hbc
  rw [← ENNReal.ofReal_add h1 (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [show 1 - (b + c) / n + c / n + b / n = 1 by field_simp; ring]
  simp

lemma scp2_pow_tendsto' (s : ℝ) :
    Tendsto (fun k : ℕ => (1 - s / ((k + 1 : ℕ) : ℝ)) ^ (k + 1)) atTop (𝓝 (Real.exp (-s))) := by
  have h1 := (Real.tendsto_one_add_div_pow_exp (-s)).comp (tendsto_add_atTop_nat 1)
  refine h1.congr' (Eventually.of_forall fun k => ?_)
  simp only [Function.comp, neg_div, ← sub_eq_add_neg]

lemma scp2_prob_le_max {N : ℕ} [NeZero N] (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    (Measure.pi fun _ : Fin N => μ) {x | t ≤ maxV x} = 1 - μ (Set.Iio t) ^ N := by
  have hc : {x : Fin N → ℝ | t ≤ maxV x} = (Set.univ.pi fun _ => Set.Iio t)ᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_pi, Set.mem_univ, Set.mem_Iio,
      true_implies, not_forall, not_lt, maxV, Finset.le_sup'_iff, Finset.mem_univ, true_and]
  rw [hc, prob_compl_eq_one_sub (MeasurableSet.univ_pi fun _ => measurableSet_Iio), Measure.pi_pi]
  simp

theorem solution (a b c : ℝ) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b)
    (hc : 0 < c) :
    Tendsto (fun k : ℕ => (Emax (threePoint ((k + 1 : ℕ) : ℝ) a b c) (k + 1)).toReal) atTop
      (𝓝 (1 - Real.exp (-b) + a * (Real.exp (-b) - Real.exp (-b - c)))) := by
  have hlim : Tendsto (fun k : ℕ => a * (1 - (1 - (b + c) / ((k + 1 : ℕ) : ℝ)) ^ (k + 1)) +
      (1 - a) * (1 - (1 - b / ((k + 1 : ℕ) : ℝ)) ^ (k + 1))) atTop
      (𝓝 (1 - Real.exp (-b) + a * (Real.exp (-b) - Real.exp (-b - c)))) := by
    have := ((tendsto_const_nhds (x := a)).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub
      (scp2_pow_tendsto' (b + c)))).add ((tendsto_const_nhds (x := 1 - a)).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (scp2_pow_tendsto' b)))
    convert this using 2
    rw [show -b - c = -(b + c) by ring]
    ring
  refine hlim.congr' ?_
  have hev : ∀ᶠ k : ℕ in atTop, b + c < ((k + 1 : ℕ) : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_gt (b + c)
    filter_upwards [eventually_ge_atTop N] with k hk
    have : (N : ℝ) ≤ k := by exact_mod_cast hk
    push_cast; linarith
  filter_upwards [hev] with k hk
  set n : ℝ := ((k + 1 : ℕ) : ℝ) with hn
  have hnpos : 0 < n := by positivity
  set μ := threePoint n a b c with hμ
  have hprob : IsProbabilityMeasure μ := scp2_threePoint_prob n a b c hnpos hb.le hc.le hk.le
  -- support
  have hsupp : ∀ᵐ y ∂μ, y = 0 ∨ y = a ∨ y = 1 := by
    rw [ae_iff]
    have hset : {y : ℝ | ¬ (y = 0 ∨ y = a ∨ y = 1)} = ({0, a, 1} : Set ℝ)ᶜ := by
      ext y; simp
    rw [hset, hμ, scp2_threePoint_apply _ _ _ _ _ (Set.toFinite _).measurableSet.compl]
    simp
  have hsuppi : ∀ᵐ x ∂(Measure.pi fun _ : Fin (k + 1) => μ), ∀ i, x i = 0 ∨ x i = a ∨ x i = 1 :=
    ae_all_iff.2 fun i => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin (k + 1) => μ)).eventually hsupp
  have hEmax : Emax μ (k + 1) = ∫⁻ x, ({x : Fin (k + 1) → ℝ | a ≤ maxV x}.indicator
      (fun _ => ENNReal.ofReal a) x + {x : Fin (k + 1) → ℝ | 1 ≤ maxV x}.indicator
      (fun _ => ENNReal.ofReal (1 - a)) x) ∂(Measure.pi fun _ : Fin (k + 1) => μ) := by
    unfold Emax iidLaw
    apply lintegral_congr_ae
    filter_upwards [hsuppi] with x hx
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin (k + 1))) x
    have hM : maxV x = x i := hi
    simp only [Set.indicator, Set.mem_ofPred_eq, hM]
    rcases hx i with h | h | h <;> rw [h]
    · simp [ha.not_ge]
    · simp [ha1.not_ge]
    · simp [ha1.le]
      rw [← ENNReal.ofReal_add ha.le (by linarith)]; simp
  have hmeas : ∀ t : ℝ, MeasurableSet {x : Fin (k + 1) → ℝ | t ≤ maxV x} := by
    intro t
    have : Measurable (fun x : Fin (k + 1) → ℝ => maxV x) := by
      have h : (fun x : Fin (k + 1) → ℝ => maxV x) =
          Finset.univ.sup' Finset.univ_nonempty (fun i (x : Fin (k + 1) → ℝ) => x i) := by
        funext x; simp [maxV, Finset.sup'_apply]
      rw [h]; exact Finset.measurable_sup' _ (fun i _ => measurable_pi_apply i)
    exact measurableSet_le measurable_const this
  rw [hEmax, lintegral_add_left ((measurable_const.indicator (hmeas a))),
    lintegral_indicator_const (hmeas a), lintegral_indicator_const (hmeas 1),
    scp2_prob_le_max, scp2_prob_le_max]
  -- compute μ (Iio a), μ (Iio 1)
  have hr0 : 0 ≤ 1 - (b + c) / n := by rw [sub_nonneg, div_le_one hnpos]; linarith
  have hr1 : 0 ≤ 1 - b / n := by rw [sub_nonneg, div_le_one hnpos]; linarith
  have hqa : μ (Set.Iio a) = ENNReal.ofReal (1 - (b + c) / n) := by
    rw [hμ, scp2_threePoint_apply _ _ _ _ _ measurableSet_Iio]
    simp [Set.indicator, ha, ha1.not_gt]
  have hq1 : μ (Set.Iio 1) = ENNReal.ofReal (1 - b / n) := by
    rw [hμ, scp2_threePoint_apply _ _ _ _ _ measurableSet_Iio]
    simp [Set.indicator, ha1]
    rw [← ENNReal.ofReal_add hr0 (by positivity)]; congr 1; ring
  rw [hqa, hq1, ← ENNReal.ofReal_pow hr0, ← ENNReal.ofReal_pow hr1, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ (pow_nonneg hr0 _), ← ENNReal.ofReal_sub _ (pow_nonneg hr1 _),
    ← ENNReal.ofReal_mul ha.le, ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_add (mul_nonneg ha.le ?_) (mul_nonneg (by linarith) ?_), ENNReal.toReal_ofReal]
  · exact add_nonneg (mul_nonneg ha.le (sub_nonneg.2 (pow_le_one₀ hr0 (by
      rw [sub_le_self_iff]; positivity)))) (mul_nonneg (by linarith) (sub_nonneg.2 (pow_le_one₀ hr1 (by
      rw [sub_le_self_iff]; positivity))))
  · exact sub_nonneg.2 (pow_le_one₀ hr0 (by rw [sub_le_self_iff]; positivity))
  · exact sub_nonneg.2 (pow_le_one₀ hr1 (by rw [sub_le_self_iff]; positivity))
