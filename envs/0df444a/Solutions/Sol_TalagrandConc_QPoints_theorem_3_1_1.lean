-- Prove2me | solution 1 for TalagrandConc.QPoints.theorem_3_1_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:15:08.833094+00:00
-- url     : https://prove2.me/submissions/e5a7ae20-1ceb-4d8a-ab49-b682f185bb79

import Mathlib
import Definitions.Def_TalagrandConc_QPoints_Basic



namespace TalagrandConc.QPoints

open MeasureTheory
open scoped ENNReal
open Classical

lemma uncaptured_eq_sum {Ω : Type*} {N q : ℕ} (y : Fin q → Fin N → Ω) (x : Fin N → Ω) :
    uncaptured y x = ∑ i : Fin N, (if ∀ j : Fin q, x i ≠ y j i then 1 else 0) := by
  unfold uncaptured
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

lemma uncaptured_snoc {Ω : Type*} {N q : ℕ} (y' : Fin q → Fin N → Ω) (ω' : Fin q → Ω)
    (x : Fin N → Ω) (ω : Ω) :
    uncaptured (fun j => (Fin.snoc (y' j) (ω' j) : Fin (N + 1) → Ω))
        (Fin.snoc x ω : Fin (N + 1) → Ω) =
      uncaptured y' x + (if ∀ j : Fin q, ω ≠ ω' j then 1 else 0) := by
  rw [uncaptured_eq_sum, uncaptured_eq_sum, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

lemma qDist_le_of_mem {Ω : Type*} {N q : ℕ} (A : Fin q → Set (Fin N → Ω)) (x : Fin N → Ω)
    (y : Fin q → Fin N → Ω) (hy : ∀ j, y j ∈ A j) : qDist A x ≤ (uncaptured y x : ℕ∞) := by
  unfold qDist
  exact iInf₂_le y hy

lemma le_qDist {Ω : Type*} {N q : ℕ} (A : Fin q → Set (Fin N → Ω)) (x : Fin N → Ω) (c : ℕ∞)
    (h : ∀ y : Fin q → Fin N → Ω, (∀ j, y j ∈ A j) → c ≤ (uncaptured y x : ℕ∞)) :
    c ≤ qDist A x := by
  unfold qDist
  exact le_iInf₂ h

lemma qDist_anti {Ω : Type*} {N q : ℕ} (A A' : Fin q → Set (Fin N → Ω)) (x : Fin N → Ω)
    (h : ∀ i, A i ⊆ A' i) : qDist A' x ≤ qDist A x := by
  apply le_qDist
  intro y hy
  exact qDist_le_of_mem A' x y (fun j => h j (hy j))

theorem eq_3_1_6_core {Ω : Type*} {N q : ℕ} (hq : 2 ≤ q) (A : Fin q → Set (Fin (N + 1) → Ω))
    (x : Fin N → Ω) (ω : Ω) :
    qDist A (Fin.snoc x ω : Fin (N + 1) → Ω) ≤ 1 + qDist (fun i => projLast (A i)) x ∧
      ∀ j : Fin q, qDist A (Fin.snoc x ω : Fin (N + 1) → Ω) ≤
        qDist (Function.update (fun i => projLast (A i)) j (sliceAt (A j) ω)) x := by
  classical
  constructor
  · unfold qDist
    rw [ENat.add_iInf₂]
    refine le_iInf₂ fun y' hy' => ?_
    choose ω' hω' using hy'
    refine le_trans (iInf₂_le (fun j => (Fin.snoc (y' j) (ω' j) : Fin (N + 1) → Ω)) hω') ?_
    rw [uncaptured_snoc]
    push_cast
    split_ifs <;> simp [add_comm]
  · intro j
    apply le_qDist
    intro y' hy'
    have hj : y' j ∈ sliceAt (A j) ω := by simpa using hy' j
    have hother : ∀ i, i ≠ j → y' i ∈ projLast (A i) := by
      intro i hi
      have := hy' i
      rwa [Function.update_of_ne hi] at this
    let ω' : Fin q → Ω := fun i => if h : i = j then ω else Classical.choose (hother i h)
    have hmem : ∀ i, (Fin.snoc (y' i) (ω' i) : Fin (N + 1) → Ω) ∈ A i := by
      intro i
      by_cases h : i = j
      · subst h
        simp only [ω', dif_pos]
        exact hj
      · simp only [ω', dif_neg h]
        exact Classical.choose_spec (hother i h)
    refine le_trans (qDist_le_of_mem A _ _ hmem) ?_
    rw [uncaptured_snoc]
    have : ¬ ∀ i : Fin q, ω ≠ ω' i := by
      push Not
      exact ⟨j, by simp [ω']⟩
    simp [this]


/-- `(q + 1 - q u) u^q ≤ 1` for `0 ≤ u ≤ 1`. -/
lemma key_poly_ineq (q : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ((q : ℝ) + 1 - q * u) * u ^ q ≤ 1 := by
  set t := 1 - u with ht
  have hu : u = 1 - t := by rw [ht]; ring
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t ≤ 1 := by linarith
  have hb : 1 + (q : ℝ) * t ≤ (1 + t) ^ q := one_add_mul_le_pow (by linarith) q
  have h1 : (q : ℝ) + 1 - q * u = 1 + q * t := by rw [hu]; ring
  rw [h1, hu]
  calc (1 + (q : ℝ) * t) * (1 - t) ^ q ≤ (1 + t) ^ q * (1 - t) ^ q :=
        mul_le_mul_of_nonneg_right hb (pow_nonneg (by linarith) q)
    _ = (1 - t ^ 2) ^ q := by rw [← mul_pow]; ring_nf
    _ ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)

theorem lemma_3_1_2_core {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 2 ≤ q) (g : Ω → ℝ) (hg : Measurable g)
    (hlow : ∀ ω, 1 / (q : ℝ) ≤ g ω) (hup : ∀ ω, g ω ≤ 1) :
    (∫ ω, 1 / g ω ∂μ) * (∫ ω, g ω ∂μ) ^ q ≤ 1 := by
  have hq0 : (0 : ℝ) < q := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hqinv : 0 < 1 / (q : ℝ) := by positivity
  have hgpos : ∀ ω, 0 < g ω := fun ω => lt_of_lt_of_le hqinv (hlow ω)
  have hint_g : Integrable g μ := by
    refine Integrable.of_bound hg.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hlow ω, hup ω]
  have hinv_le : ∀ ω, 1 / g ω ≤ q := by
    intro ω
    rw [div_le_iff₀ (hgpos ω)]
    have := hlow ω
    rw [div_le_iff₀ hq0] at this
    linarith
  have hint_inv : Integrable (fun ω => 1 / g ω) μ := by
    refine Integrable.of_bound (hg.inv.aestronglyMeasurable.congr ?_) q
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact Filter.Eventually.of_forall fun ω => by simp
    · rw [Real.norm_eq_abs, abs_le]
      constructor
      · have := hinv_le ω; have : 0 < 1 / g ω := by have := hgpos ω; positivity
        linarith
      · exact hinv_le ω
  have hpt : ∀ ω, 1 / g ω ≤ ((q : ℝ) + 1) - q * g ω := by
    intro ω
    rw [div_le_iff₀ (hgpos ω)]
    have h1 := hlow ω
    rw [div_le_iff₀ hq0] at h1
    have h2 := hup ω
    nlinarith
  have h1 : ∫ ω, 1 / g ω ∂μ ≤ ∫ ω, (((q : ℝ) + 1) - q * g ω) ∂μ := by
    refine integral_mono hint_inv ?_ hpt
    exact (integrable_const _).sub (hint_g.const_mul _)
  have h2 : ∫ ω, (((q : ℝ) + 1) - q * g ω) ∂μ = ((q : ℝ) + 1) - q * ∫ ω, g ω ∂μ := by
    rw [integral_sub (integrable_const _) (hint_g.const_mul _), integral_const,
      integral_const_mul]
    simp
  have hu0 : 0 ≤ ∫ ω, g ω ∂μ := integral_nonneg fun ω => (hgpos ω).le
  have hu1 : ∫ ω, g ω ∂μ ≤ 1 := by
    have := integral_mono hint_g (integrable_const (1 : ℝ)) hup
    simpa using this
  have hA : 0 ≤ (∫ ω, g ω ∂μ) ^ q := pow_nonneg hu0 q
  calc (∫ ω, 1 / g ω ∂μ) * (∫ ω, g ω ∂μ) ^ q
      ≤ (((q : ℝ) + 1) - q * ∫ ω, g ω ∂μ) * (∫ ω, g ω ∂μ) ^ q := by
        rw [← h2]; exact mul_le_mul_of_nonneg_right h1 hA
    _ ≤ 1 := key_poly_ineq q _ hu0 hu1

/-- ENNReal version of Lemma 3.1.2: for measurable `h` with `q⁻¹ ≤ h ≤ 1`. -/
theorem lemma_3_1_2_ennreal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (q : ℕ) (hq : 2 ≤ q) (h : Ω → ℝ≥0∞) (hh : Measurable h)
    (hlow : ∀ ω, (q : ℝ≥0∞)⁻¹ ≤ h ω) (hup : ∀ ω, h ω ≤ 1) :
    (∫⁻ ω, (h ω)⁻¹ ∂μ) * (∫⁻ ω, h ω ∂μ) ^ q ≤ 1 := by
  have hq0 : (0 : ℝ) < q := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hne : ∀ ω, h ω ≠ ⊤ := fun ω => ne_top_of_le_ne_top ENNReal.one_ne_top (hup ω)
  set g : Ω → ℝ := fun ω => (h ω).toReal with hg_def
  have hg : Measurable g := ENNReal.measurable_toReal.comp hh
  have hglow : ∀ ω, 1 / (q : ℝ) ≤ g ω := by
    intro ω
    have := ENNReal.toReal_mono (hne ω) (hlow ω)
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast] at this
    rw [one_div]; exact this
  have hgup : ∀ ω, g ω ≤ 1 := by
    intro ω
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact hup ω)
  have hgpos : ∀ ω, 0 < g ω := fun ω => lt_of_lt_of_le (by positivity) (hglow ω)
  have hreal := lemma_3_1_2_core μ q hq g hg hglow hgup
  have hint_g : Integrable g μ := by
    refine Integrable.of_bound hg.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hglow ω, hgup ω, hgpos ω]
  have hinv_le : ∀ ω, 1 / g ω ≤ q := by
    intro ω
    rw [div_le_iff₀ (hgpos ω)]
    have := hglow ω
    rw [div_le_iff₀ hq0] at this
    linarith
  have hint_inv : Integrable (fun ω => 1 / g ω) μ := by
    refine Integrable.of_bound (hg.inv.aestronglyMeasurable.congr ?_) q
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact Filter.Eventually.of_forall fun ω => by simp
    · rw [Real.norm_eq_abs, abs_le]
      constructor
      · have := hinv_le ω; have : 0 < 1 / g ω := by have := hgpos ω; positivity
        linarith
      · exact hinv_le ω
  have e1 : ∫⁻ ω, h ω ∂μ = ENNReal.ofReal (∫ ω, g ω ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_g (Filter.Eventually.of_forall fun ω => (hgpos ω).le)]
    congr 1
    ext ω
    simp [hg_def, ENNReal.ofReal_toReal (hne ω)]
  have e2 : ∫⁻ ω, (h ω)⁻¹ ∂μ = ENNReal.ofReal (∫ ω, 1 / g ω ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_inv
      (Filter.Eventually.of_forall fun ω => by have := hgpos ω; positivity)]
    congr 1
    ext ω
    rw [one_div, ENNReal.ofReal_inv_of_pos (hgpos ω)]
    simp [hg_def, ENNReal.ofReal_toReal (hne ω)]
  rw [e1, e2, ← ENNReal.ofReal_pow (integral_nonneg fun ω => (hgpos ω).le),
    ← ENNReal.ofReal_mul (integral_nonneg fun ω => by have := hgpos ω; positivity),
    ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal hreal

theorem corollary_3_1_3_core {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (q : ℕ) (hq : 2 ≤ q) (g : Fin q → Ω → ℝ≥0∞)
    (hg : ∀ i, Measurable (g i)) (hup : ∀ i ω, g i ω ≤ 1) :
    (∫⁻ ω, ⨅ i : Fin q, min (q : ℝ≥0∞) (g i ω)⁻¹ ∂μ) * ∏ i : Fin q, ∫⁻ ω, g i ω ∂μ ≤ 1 := by
  haveI : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  set h : Ω → ℝ≥0∞ := fun ω => max (q : ℝ≥0∞)⁻¹ (⨆ i, g i ω) with hh_def
  have hh : Measurable h := measurable_const.max (Measurable.iSup hg)
  have hlow : ∀ ω, (q : ℝ≥0∞)⁻¹ ≤ h ω := fun ω => le_max_left _ _
  have hq1 : (q : ℝ≥0∞)⁻¹ ≤ 1 := by
    rw [ENNReal.inv_le_one]
    exact_mod_cast (by omega : 1 ≤ q)
  have hup' : ∀ ω, h ω ≤ 1 := fun ω => max_le hq1 (iSup_le fun i => hup i ω)
  have hle : ∀ ω, (⨅ i : Fin q, min (q : ℝ≥0∞) (g i ω)⁻¹) ≤ (h ω)⁻¹ := by
    intro ω
    by_cases hc : (⨆ i, g i ω) ≤ (q : ℝ≥0∞)⁻¹
    · have : h ω = (q : ℝ≥0∞)⁻¹ := max_eq_left hc
      rw [this, inv_inv]
      exact le_trans (iInf_le _ (Classical.arbitrary _)) (min_le_left _ _)
    · push Not at hc
      have : h ω = ⨆ i, g i ω := max_eq_right hc.le
      rw [this]
      obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => g i ω)
      rw [← hi]
      exact le_trans (iInf_le _ i) (min_le_right _ _)
  have hgh : ∀ i ω, g i ω ≤ h ω := fun i ω => le_trans (le_iSup (fun i => g i ω) i) (le_max_right _ _)
  calc (∫⁻ ω, ⨅ i : Fin q, min (q : ℝ≥0∞) (g i ω)⁻¹ ∂μ) * ∏ i : Fin q, ∫⁻ ω, g i ω ∂μ
      ≤ (∫⁻ ω, (h ω)⁻¹ ∂μ) * ∏ i : Fin q, ∫⁻ ω, h ω ∂μ := by
        gcongr with i
        · exact hle _
        · exact hgh i _
    _ = (∫⁻ ω, (h ω)⁻¹ ∂μ) * (∫⁻ ω, h ω ∂μ) ^ q := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ 1 := lemma_3_1_2_ennreal μ q hq h hh hlow hup'

/-- Inverse form used in the induction. -/
theorem corollary_3_1_3_inv {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (q : ℕ) (hq : 2 ≤ q) (g : Fin q → Ω → ℝ≥0∞)
    (hg : ∀ i, Measurable (g i)) (hup : ∀ i ω, g i ω ≤ 1) :
    (∫⁻ ω, ⨅ i : Fin q, min (q : ℝ≥0∞) (g i ω)⁻¹ ∂μ) ≤ (∏ i : Fin q, ∫⁻ ω, g i ω ∂μ)⁻¹ := by
  rw [ENNReal.le_inv_iff_mul_le]
  exact corollary_3_1_3_core μ q hq g hg hup


/-! ### `epow` lemmas -/

lemma epow_coe (a : ℝ≥0∞) (m : ℕ) : epow a (m : ℕ∞) = a ^ m := by
  simp [epow]

lemma epow_top' (a : ℝ≥0∞) : epow a ⊤ = ⊤ := by
  simp [epow]

lemma epow_mono {a : ℝ≥0∞} (ha : 1 ≤ a) {m n : ℕ∞} (h : m ≤ n) : epow a m ≤ epow a n := by
  induction n using ENat.recTopCoe with
  | top => rw [epow_top']; exact le_top
  | coe n =>
    induction m using ENat.recTopCoe with
    | top => exact absurd h (by simp)
    | coe m =>
      rw [epow_coe, epow_coe]
      exact pow_le_pow_right₀ ha (by exact_mod_cast h)

lemma epow_one_add (a : ℝ≥0∞) (ha : a ≠ 0) (n : ℕ∞) : epow a (1 + n) = a * epow a n := by
  induction n using ENat.recTopCoe with
  | top => simp [epow, ENNReal.mul_top ha]
  | coe n =>
    have : (1 : ℕ∞) + n = ((1 + n : ℕ) : ℕ∞) := by push_cast; rfl
    rw [this, epow_coe, epow_coe, pow_add, pow_one]

/-! ### Choice of a good measurable sub-projection -/

lemma exists_good_proj {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (A : Set (Fin (N + 1) → Ω)) (hsl : ∀ ω, MeasurableSet (sliceAt A ω)) :
    ∃ B : Set (Fin N → Ω), MeasurableSet B ∧ B ⊆ projLast A ∧
      ∀ ω, (Measure.pi fun _ : Fin N => μ) (sliceAt A ω) ≤ (Measure.pi fun _ : Fin N => μ) B := by
  haveI : Nonempty Ω := Measure.nonempty_of_neZero μ
  set P := Measure.pi fun _ : Fin N => μ with hP
  set S := Set.range (fun ω => P (sliceAt A ω)) with hS
  obtain ⟨u, -, hlim, hmem⟩ :=
    exists_seq_tendsto_sSup (S := S) (Set.range_nonempty _) (OrderTop.bddAbove S)
  choose ω' hω' using hmem
  refine ⟨⋃ n, sliceAt A (ω' n), MeasurableSet.iUnion fun n => hsl _, ?_, ?_⟩
  · intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
    exact ⟨ω' n, hn⟩
  · intro ω
    calc P (sliceAt A ω) ≤ sSup S := le_csSup (OrderTop.bddAbove S) ⟨ω, rfl⟩
      _ ≤ P (⋃ n, sliceAt A (ω' n)) := by
        refine le_of_tendsto' hlim fun n => ?_
        rw [← hω' n]
        exact measure_mono (Set.subset_iUnion (fun n => sliceAt A (ω' n)) n)

/-! ### The induction -/

theorem main_induction {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 2 ≤ q) :
    ∀ (N : ℕ) (A : Fin q → Set (Fin N → Ω)), (∀ i, MeasurableSet (A i)) →
      ∫⁻ x, epow (q : ℝ≥0∞) (qDist A x) ∂(Measure.pi fun _ : Fin N => μ) ≤
        (∏ i : Fin q, (Measure.pi fun _ : Fin N => μ) (A i))⁻¹ := by
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hq1 : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hqtop : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top q
  intro N
  induction N with
  | zero =>
    intro A hA
    by_cases hne : ∀ i, (A i).Nonempty
    · choose y hy using hne
      have h0 : ∀ x, qDist A x = 0 := by
        intro x
        apply le_antisymm _ zero_le
        refine le_trans (qDist_le_of_mem A x y hy) ?_
        simp [uncaptured]
      simp only [h0]
      have h1 : epow (q : ℝ≥0∞) 0 = 1 := by
        rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, epow_coe, pow_zero]
      rw [h1, lintegral_const, measure_univ, mul_one, ENNReal.le_inv_iff_mul_le, one_mul]
      exact Finset.prod_le_one (fun i _ => zero_le) (fun i _ => prob_le_one)
    · push Not at hne
      obtain ⟨i, hi⟩ := hne
      have : ∏ j, (Measure.pi fun _ : Fin 0 => μ) (A j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
      rw [this, ENNReal.inv_zero]
      exact le_top
  | succ N ih =>
    intro A hA
    set P : Measure (Fin N → Ω) := Measure.pi fun _ : Fin N => μ with hP
    set P' : Measure (Fin (N + 1) → Ω) := Measure.pi fun _ : Fin (N + 1) => μ with hP'
    -- the measurable equivalence splitting off the last coordinate
    let e : (Fin (N + 1) → Ω) ≃ᵐ Ω × (Fin N → Ω) :=
      MeasurableEquiv.piFinSuccAbove (fun _ => Ω) (Fin.last N)
    have hmp : MeasurePreserving e P' (μ.prod P) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => μ) (Fin.last N)
    have he : ∀ (ω : Ω) (x : Fin N → Ω), e.symm (ω, x) = (Fin.snoc x ω : Fin (N + 1) → Ω) := by
      intro ω x
      simp [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
    have hslice : ∀ i ω, sliceAt (A i) ω = Prod.mk ω ⁻¹' (e.symm ⁻¹' A i) := by
      intro i ω
      ext x
      simp [sliceAt, he]
    have hslice_meas : ∀ i ω, MeasurableSet (sliceAt (A i) ω) := by
      intro i ω
      rw [hslice]
      exact measurable_prodMk_left (e.symm.measurable (hA i))
    have hmeas_slice : ∀ i, Measurable (fun ω => P (sliceAt (A i) ω)) := by
      intro i
      simp_rw [hslice]
      exact measurable_measure_prodMk_left (e.symm.measurable (hA i))
    have hfub : ∀ i, ∫⁻ ω, P (sliceAt (A i) ω) ∂μ = P' (A i) := by
      intro i
      rw [← (hmp.symm e).measure_preimage (hA i).nullMeasurableSet,
        Measure.prod_apply (e.symm.measurable (hA i))]
      simp_rw [hslice]
    -- transfer of the integral
    have htrans : ∫⁻ z, epow (q : ℝ≥0∞) (qDist A z) ∂P' ≤
        ∫⁻ ω, ∫⁻ x, epow (q : ℝ≥0∞) (qDist A (Fin.snoc x ω : Fin (N + 1) → Ω)) ∂P ∂μ := by
      calc ∫⁻ z, epow (q : ℝ≥0∞) (qDist A z) ∂P'
          = ∫⁻ p, epow (q : ℝ≥0∞) (qDist A (e.symm p)) ∂(μ.prod P) :=
            ((hmp.symm e).lintegral_comp_emb e.symm.measurableEmbedding _).symm
        _ ≤ ∫⁻ ω, ∫⁻ x, epow (q : ℝ≥0∞) (qDist A (e.symm (ω, x))) ∂P ∂μ := lintegral_prod_le _
        _ = _ := by simp_rw [he]
    -- trivial case: some `A i` is null
    by_cases hz : ∃ i, P' (A i) = 0
    · obtain ⟨i, hi⟩ := hz
      have : ∏ j, P' (A j) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
      rw [this, ENNReal.inv_zero]
      exact le_top
    push Not at hz
    -- good sub-projections
    choose B hBm hBsub hBle using fun i => exists_good_proj μ (A i) (hslice_meas i)
    have hPAle : ∀ i, P' (A i) ≤ P (B i) := by
      intro i
      rw [← hfub i]
      calc ∫⁻ ω, P (sliceAt (A i) ω) ∂μ ≤ ∫⁻ ω, P (B i) ∂μ := lintegral_mono fun ω => hBle i ω
        _ = P (B i) := by rw [lintegral_const, measure_univ, mul_one]
    have hB0 : ∀ i, P (B i) ≠ 0 := fun i h => hz i (le_antisymm (h ▸ hPAle i) zero_le)
    have hBtop : ∀ i, P (B i) ≠ ⊤ := fun i => measure_ne_top _ _
    set PB := ∏ i, P (B i) with hPB
    have hPB0 : PB ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hB0 i
    have hPBtop : PB ≠ ⊤ := ENNReal.prod_ne_top fun i _ => hBtop i
    -- the modified families
    let C : Fin q → Ω → Fin q → Set (Fin N → Ω) := fun j ω => Function.update B j (sliceAt (A j) ω)
    have hCm : ∀ j ω i, MeasurableSet (C j ω i) := by
      intro j ω i
      by_cases h : i = j
      · subst h; simp [C, hslice_meas]
      · simp only [C, Function.update_of_ne h]; exact hBm i
    -- pointwise bounds
    have hb1 : ∀ x ω, epow (q : ℝ≥0∞) (qDist A (Fin.snoc x ω : Fin (N + 1) → Ω)) ≤
        q * epow (q : ℝ≥0∞) (qDist B x) := by
      intro x ω
      have h1 := (eq_3_1_6_core hq A x ω).1
      have h2 := qDist_anti B (fun i => projLast (A i)) x hBsub
      calc epow (q : ℝ≥0∞) (qDist A (Fin.snoc x ω : Fin (N + 1) → Ω))
          ≤ epow (q : ℝ≥0∞) (1 + qDist B x) :=
            epow_mono hq1 (le_trans h1 (add_le_add le_rfl h2))
        _ = q * epow (q : ℝ≥0∞) (qDist B x) := epow_one_add _ hq0 _
    have hb2 : ∀ x ω j, epow (q : ℝ≥0∞) (qDist A (Fin.snoc x ω : Fin (N + 1) → Ω)) ≤
        epow (q : ℝ≥0∞) (qDist (C j ω) x) := by
      intro x ω j
      have h1 := (eq_3_1_6_core hq A x ω).2 j
      have h2 : qDist (Function.update (fun i => projLast (A i)) j (sliceAt (A j) ω)) x ≤
          qDist (C j ω) x := by
        apply qDist_anti
        intro i
        by_cases h : i = j
        · subst h; simp [C]
        · simp only [C, Function.update_of_ne h]; exact hBsub i
      exact epow_mono hq1 (le_trans h1 h2)
    -- the functions g_j
    let g : Fin q → Ω → ℝ≥0∞ := fun j ω => P (sliceAt (A j) ω) * (P (B j))⁻¹
    have hg_meas : ∀ j, Measurable (g j) := fun j => (hmeas_slice j).mul_const _
    have hg_le : ∀ j ω, g j ω ≤ 1 := by
      intro j ω
      calc g j ω = P (sliceAt (A j) ω) * (P (B j))⁻¹ := rfl
        _ ≤ P (B j) * (P (B j))⁻¹ := mul_le_mul' (hBle j ω) le_rfl
        _ = 1 := ENNReal.mul_inv_cancel (hB0 j) (hBtop j)
    have hg_int : ∀ j, ∫⁻ ω, g j ω ∂μ = P' (A j) * (P (B j))⁻¹ := by
      intro j
      simp only [g]
      rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (hB0 j)), hfub]
    -- the key bound for fixed ω
    have J : ∀ ω, ∫⁻ x, epow (q : ℝ≥0∞) (qDist A (Fin.snoc x ω : Fin (N + 1) → Ω)) ∂P ≤
        PB⁻¹ * ⨅ j, min (q : ℝ≥0∞) (g j ω)⁻¹ := by
      intro ω
      set X := ∫⁻ x, epow (q : ℝ≥0∞) (qDist A (Fin.snoc x ω : Fin (N + 1) → Ω)) ∂P with hX
      have I1 : X ≤ q * PB⁻¹ := by
        calc X ≤ ∫⁻ x, q * epow (q : ℝ≥0∞) (qDist B x) ∂P := lintegral_mono fun x => hb1 x ω
          _ = q * ∫⁻ x, epow (q : ℝ≥0∞) (qDist B x) ∂P := lintegral_const_mul' _ _ hqtop
          _ ≤ q * PB⁻¹ := by gcongr; exact ih B hBm
      have I2 : ∀ j, X ≤ (∏ i, P (C j ω i))⁻¹ := by
        intro j
        calc X ≤ ∫⁻ x, epow (q : ℝ≥0∞) (qDist (C j ω) x) ∂P := lintegral_mono fun x => hb2 x ω j
          _ ≤ _ := ih (C j ω) (hCm j ω)
      rw [mul_comm, ← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl hPB0) (Or.inl hPBtop)]
      refine le_iInf fun j => le_min ?_ ?_
      · calc X * PB ≤ q * PB⁻¹ * PB := by gcongr
          _ = q := by rw [mul_assoc, ENNReal.inv_mul_cancel hPB0 hPBtop, mul_one]
      · set R := ∏ i ∈ Finset.univ.erase j, P (B i) with hR
        have hR0 : R ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hB0 i
        have hRtop : R ≠ ⊤ := ENNReal.prod_ne_top fun i _ => hBtop i
        have hPBeq : PB = P (B j) * R :=
          (Finset.mul_prod_erase Finset.univ (fun i => P (B i)) (Finset.mem_univ j)).symm
        have hCeq : ∏ i, P (C j ω i) = P (sliceAt (A j) ω) * R := by
          calc ∏ i, P (C j ω i) = P (C j ω j) * ∏ i ∈ Finset.univ.erase j, P (C j ω i) :=
                (Finset.mul_prod_erase Finset.univ (fun i => P (C j ω i)) (Finset.mem_univ j)).symm
            _ = P (sliceAt (A j) ω) * R := by
                congr 1
                · simp [C]
                · exact Finset.prod_congr rfl fun i hi => by
                    simp [C, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
        have hS_top : P (sliceAt (A j) ω) ≠ ⊤ := measure_ne_top _ _
        have hginv : (g j ω)⁻¹ = (P (sliceAt (A j) ω))⁻¹ * P (B j) := by
          simp only [g]
          rw [ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.2 (hB0 j))) (Or.inl hS_top), inv_inv]
        rw [hginv, hPBeq]
        have I2' := I2 j
        rw [hCeq, ENNReal.mul_inv (Or.inr hRtop) (Or.inl hS_top)] at I2'
        calc X * (P (B j) * R) ≤ (P (sliceAt (A j) ω))⁻¹ * R⁻¹ * (P (B j) * R) := by gcongr
          _ = (P (sliceAt (A j) ω))⁻¹ * P (B j) * (R⁻¹ * R) := by ring
          _ = (P (sliceAt (A j) ω))⁻¹ * P (B j) := by
              rw [ENNReal.inv_mul_cancel hR0 hRtop, mul_one]
    -- integrate over ω
    have hQ0 : ∏ j, P' (A j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hz j
    have hQtop : ∏ j, P' (A j) ≠ ⊤ := ENNReal.prod_ne_top fun j _ => measure_ne_top _ _
    calc ∫⁻ z, epow (q : ℝ≥0∞) (qDist A z) ∂P'
        ≤ ∫⁻ ω, ∫⁻ x, epow (q : ℝ≥0∞) (qDist A (Fin.snoc x ω : Fin (N + 1) → Ω)) ∂P ∂μ := htrans
      _ ≤ ∫⁻ ω, PB⁻¹ * ⨅ j, min (q : ℝ≥0∞) (g j ω)⁻¹ ∂μ := lintegral_mono J
      _ = PB⁻¹ * ∫⁻ ω, ⨅ j, min (q : ℝ≥0∞) (g j ω)⁻¹ ∂μ :=
          lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hPB0)
      _ ≤ PB⁻¹ * (∏ j, ∫⁻ ω, g j ω ∂μ)⁻¹ := by
          gcongr; exact corollary_3_1_3_inv μ q hq g hg_meas hg_le
      _ = PB⁻¹ * ((∏ j, P' (A j)) * PB⁻¹)⁻¹ := by
          simp_rw [hg_int]
          rw [Finset.prod_mul_distrib, hPB,
            ENNReal.prod_inv_distrib (fun i _ j _ _ => Or.inl (hB0 i))]
      _ = (∏ j, P' (A j))⁻¹ := by
          rw [ENNReal.mul_inv (Or.inl hQ0) (Or.inl hQtop), inv_inv]
          calc PB⁻¹ * ((∏ j, P' (A j))⁻¹ * PB) = (∏ j, P' (A j))⁻¹ * (PB⁻¹ * PB) := by ring
            _ = _ := by rw [ENNReal.inv_mul_cancel hPB0 hPBtop, mul_one]

theorem theorem_3_1_1_core {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (N q : ℕ) (hq : 2 ≤ q) :
    (∀ A : Fin q → Set (Fin N → Ω), (∀ i, MeasurableSet (A i)) →
        Measurable (qDist A) →
        ∫⁻ x, epow (q : ℝ≥0∞) (qDist A x) ∂(Measure.pi fun _ : Fin N => μ) ≤
          (∏ i : Fin q, (Measure.pi fun _ : Fin N => μ) (A i))⁻¹) ∧
    (∀ (A : Set (Fin N → Ω)) (k : ℕ), MeasurableSet A →
        Measurable (qDist (fun _ : Fin q => A)) →
        (Measure.pi fun _ : Fin N => μ) {x | (k : ℕ∞) ≤ qDist (fun _ : Fin q => A) x} ≤
          ((q : ℝ≥0∞) ^ k * (Measure.pi fun _ : Fin N => μ) A ^ q)⁻¹) := by
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hq1 : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hqtop : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top q
  refine ⟨fun A hA _ => main_induction μ q hq N A hA, ?_⟩
  intro A k hA hf
  set P := Measure.pi fun _ : Fin N => μ with hP
  have h1 := main_induction μ q hq N (fun _ => A) (fun _ => hA)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  have hmeas : AEMeasurable (fun x => epow (q : ℝ≥0∞) (qDist (fun _ : Fin q => A) x)) P :=
    (Measurable.of_discrete.comp hf).aemeasurable
  have hmarkov := mul_meas_ge_le_lintegral₀ hmeas ((q : ℝ≥0∞) ^ k)
  have hsub : {x | (k : ℕ∞) ≤ qDist (fun _ : Fin q => A) x} ⊆
      {x | (q : ℝ≥0∞) ^ k ≤ epow (q : ℝ≥0∞) (qDist (fun _ : Fin q => A) x)} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [← epow_coe]
    exact epow_mono hq1 hx
  have hqk0 : (q : ℝ≥0∞) ^ k ≠ 0 := pow_ne_zero _ hq0
  have hqktop : (q : ℝ≥0∞) ^ k ≠ ⊤ := ENNReal.pow_ne_top hqtop
  rw [ENNReal.mul_inv (Or.inl hqk0) (Or.inl hqktop), ← ENNReal.mul_le_iff_le_inv hqk0 hqktop]
  calc (q : ℝ≥0∞) ^ k * P {x | (k : ℕ∞) ≤ qDist (fun _ : Fin q => A) x}
      ≤ (q : ℝ≥0∞) ^ k * P {x | (q : ℝ≥0∞) ^ k ≤ epow (q : ℝ≥0∞) (qDist (fun _ : Fin q => A) x)} := by
        gcongr
    _ ≤ ∫⁻ x, epow (q : ℝ≥0∞) (qDist (fun _ : Fin q => A) x) ∂P := hmarkov
    _ ≤ (P A ^ q)⁻¹ := h1

end TalagrandConc.QPoints

open TalagrandConc.QPoints
open MeasureTheory
open scoped ENNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (N q : ℕ) (hq : 2 ≤ q) :
    (∀ A : Fin q → Set (Fin N → Ω), (∀ i, MeasurableSet (A i)) →
        Measurable (qDist A) →
        ∫⁻ x, epow (q : ℝ≥0∞) (qDist A x) ∂(Measure.pi fun _ : Fin N => μ) ≤
          (∏ i : Fin q, (Measure.pi fun _ : Fin N => μ) (A i))⁻¹) ∧
    (∀ (A : Set (Fin N → Ω)) (k : ℕ), MeasurableSet A →
        Measurable (qDist (fun _ : Fin q => A)) →
        (Measure.pi fun _ : Fin N => μ) {x | (k : ℕ∞) ≤ qDist (fun _ : Fin q => A) x} ≤
          ((q : ℝ≥0∞) ^ k * (Measure.pi fun _ : Fin N => μ) A ^ q)⁻¹) := by
  exact theorem_3_1_1_core μ N q hq
