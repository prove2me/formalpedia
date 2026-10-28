-- Prove2me | solution 1 for RobustSPA.AllDist.pointwise_regret_le_inv_e
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T08:36:43.562368+00:00
-- url     : https://prove2.me/submissions/5cde9ebe-3d3a-441b-8608-234987f369bb

import Mathlib
import Definitions.Def_RobustSPA_AllDist_Setting
open MeasureTheory
open scoped Classical


namespace RSPA3
open RobustSPA.AllDist

variable {n : ℕ}

lemma SPA_x (ρ : Measure ℝ) (i : Fin n) (v : Fin n → ℝ) :
    (SPA (n := n) ρ).x i v = if isWinner v i then (ρ (Set.Iic (v i))).toReal else 0 := rfl

lemma SPA_p (ρ : Measure ℝ) (i : Fin n) (v : Fin n → ℝ) :
    (SPA (n := n) ρ).p i v = if isWinner v i then
      ∫ q, (Set.Iic (v i)).indicator (fun q => max (second v) q) q ∂ρ else 0 := rfl

lemma isWinner_unique {v : Fin n → ℝ} {i j : Fin n} (hi : isWinner v i) (hj : isWinner v j) :
    i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := hj.2 i h; have := hi.1 j; linarith
  · exact h
  · have := hi.2 j h; have := hj.1 i; linarith

/-- the highest competing valuation -/
noncomputable def cmax (v : Fin n → ℝ) (i : Fin n) : ℝ := ⨆ j : {j : Fin n // j ≠ i}, v j

lemma le_cmax (v : Fin n → ℝ) (i j : Fin n) (hj : j ≠ i) : v j ≤ cmax v i :=
  le_ciSup (f := fun j : {j : Fin n // j ≠ i} => v j) (Finite.bddAbove_range _) ⟨j, hj⟩

lemma le_second (v : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b) : min (v a) (v b) ≤ second v :=
  le_ciSup (f := fun q : {q : Fin n × Fin n // q.1 ≠ q.2} => min (v q.1.1) (v q.1.2))
    (Finite.bddAbove_range _) ⟨(a, b), hab⟩

lemma second_eq_cmax {v : Fin n → ℝ} {i : Fin n} (hw : isWinner v i) : second v = cmax v i := by
  by_cases hne : Nonempty {j : Fin n // j ≠ i}
  · obtain ⟨⟨j0, hj0⟩⟩ := hne
    haveI : Nonempty {q : Fin n × Fin n // q.1 ≠ q.2} := ⟨⟨(i, j0), fun h => hj0 h.symm⟩⟩
    haveI : Nonempty {j : Fin n // j ≠ i} := ⟨⟨j0, hj0⟩⟩
    apply le_antisymm
    · apply ciSup_le
      rintro ⟨⟨a, b⟩, hab⟩
      by_cases ha : a = i
      · subst ha
        exact (min_le_right _ _).trans (le_cmax v a b (Ne.symm hab))
      · exact (min_le_left _ _).trans (le_cmax v i a ha)
    · apply ciSup_le
      rintro ⟨j, hj⟩
      have h1 : min (v i) (v j) = v j := min_eq_right (hw.1 j)
      calc v j = min (v i) (v j) := h1.symm
        _ ≤ second v := le_second v i j (fun h => hj h.symm)
  · haveI h1 : IsEmpty {j : Fin n // j ≠ i} := not_nonempty_iff.mp hne
    haveI h2 : IsEmpty {q : Fin n × Fin n // q.1 ≠ q.2} := by
      constructor
      rintro ⟨⟨a, b⟩, hab⟩
      by_cases ha : a = i
      · subst ha; exact h1.false ⟨b, Ne.symm hab⟩
      · exact h1.false ⟨a, ha⟩
    unfold second cmax
    rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty]

lemma cmax_update (v : Fin n → ℝ) (i : Fin n) (w : ℝ) :
    cmax (Function.update v i w) i = cmax v i := by
  unfold cmax
  congr 1
  funext j
  exact Function.update_of_ne j.2 _ _

lemma cmax_le_of_winner {v : Fin n → ℝ} {i : Fin n} (hw : isWinner v i) (h0 : 0 ≤ v i) :
    cmax v i ≤ v i := by
  by_cases hne : Nonempty {j : Fin n // j ≠ i}
  · exact ciSup_le (fun j => hw.1 j)
  · haveI : IsEmpty {j : Fin n // j ≠ i} := not_nonempty_iff.mp hne
    unfold cmax; rw [Real.iSup_of_isEmpty]; exact h0

lemma le_cmax_of_not_winner {v : Fin n → ℝ} {i : Fin n} (hw : ¬ isWinner v i) :
    v i ≤ cmax v i := by
  unfold isWinner at hw
  by_cases h : ∀ j, v j ≤ v i
  · have : ¬ ∀ j, j < i → v j < v i := fun h' => hw ⟨h, h'⟩
    push_neg at this
    obtain ⟨j, hji, hj⟩ := this
    exact hj.trans (le_cmax v i j (ne_of_lt hji))
  · push_neg at h
    obtain ⟨j, hj⟩ := h
    have hne : j ≠ i := by rintro rfl; exact lt_irrefl _ hj
    exact hj.le.trans (le_cmax v i j hne)

lemma second_nonneg {v : Fin n → ℝ} (hv : v ∈ cube n) : 0 ≤ second v := by
  by_cases hne : Nonempty {q : Fin n × Fin n // q.1 ≠ q.2}
  · obtain ⟨⟨⟨a, b⟩, hab⟩⟩ := hne
    refine le_trans ?_ (le_second v a b hab)
    exact le_min (hv a (Set.mem_univ _)).1 (hv b (Set.mem_univ _)).1
  · haveI : IsEmpty {q : Fin n × Fin n // q.1 ≠ q.2} := not_nonempty_iff.mp hne
    unfold second; rw [Real.iSup_of_isEmpty]

lemma second_le_one {v : Fin n → ℝ} (hv : v ∈ cube n) : second v ≤ 1 := by
  unfold second
  apply Real.iSup_le _ zero_le_one
  rintro ⟨⟨a, b⟩, _⟩
  exact (min_le_left _ _).trans (hv a (Set.mem_univ _)).2

/-- integrability of the bounded integrands -/
lemma integrable_ind_max (ρ : Measure ℝ) [IsFiniteMeasure ρ] (a c : ℝ) :
    Integrable (fun q => (Set.Iic a).indicator (fun q => max c q) q) ρ := by
  refine Integrable.of_bound ((measurable_const.max measurable_id).indicator
    measurableSet_Iic).aestronglyMeasurable (|c| + |a|) (Filter.Eventually.of_forall fun q => ?_)
  by_cases hq : q ∈ Set.Iic a
  · rw [Set.indicator_of_mem hq, Real.norm_eq_abs, abs_le]
    have : q ≤ a := hq
    constructor
    · have := neg_abs_le c; have := abs_nonneg a; have := le_max_left c q; linarith
    · have := le_abs_self c; have := le_abs_self a; have := abs_nonneg c; have := abs_nonneg a
      rcases le_total c q with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
  · rw [Set.indicator_of_notMem hq]; simp; positivity

lemma util_eq (ρ : Measure ℝ) [IsFiniteMeasure ρ] (a c val : ℝ) :
    val * (ρ (Set.Iic a)).toReal - ∫ q, (Set.Iic a).indicator (fun q => max c q) q ∂ρ
      = ∫ q, (Set.Iic a).indicator (fun q => val - max c q) q ∂ρ := by
  have h1 : (fun q => (Set.Iic a).indicator (fun q => val - max c q) q)
      = fun q => (Set.Iic a).indicator (fun _ => val) q
          - (Set.Iic a).indicator (fun q => max c q) q := by
    funext q
    by_cases hq : q ∈ Set.Iic a
    · simp [Set.indicator_of_mem hq]
    · simp [Set.indicator_of_notMem hq]
  rw [h1, integral_sub ((integrable_const val).indicator measurableSet_Iic)
    (integrable_ind_max ρ a c), integral_indicator_const _ measurableSet_Iic, smul_eq_mul,
    measureReal_def, mul_comm]

lemma ind_le_ind {a c val q : ℝ} (hc : c ≤ val) :
    (Set.Iic a).indicator (fun q => val - max c q) q
      ≤ (Set.Iic val).indicator (fun q => val - max c q) q := by
  by_cases hqa : q ≤ a <;> by_cases hqv : q ≤ val
  · rw [Set.indicator_of_mem (show q ∈ Set.Iic a from hqa),
      Set.indicator_of_mem (show q ∈ Set.Iic val from hqv)]
  · rw [Set.indicator_of_mem (show q ∈ Set.Iic a from hqa),
      Set.indicator_of_notMem (show q ∉ Set.Iic val from hqv)]
    push_neg at hqv
    have := le_max_right c q; linarith
  · rw [Set.indicator_of_notMem (show q ∉ Set.Iic a from hqa),
      Set.indicator_of_mem (show q ∈ Set.Iic val from hqv)]
    have : max c q ≤ val := max_le hc hqv
    linarith
  · rw [Set.indicator_of_notMem (show q ∉ Set.Iic a from hqa),
      Set.indicator_of_notMem (show q ∉ Set.Iic val from hqv)]

lemma ind_nonpos {a c val q : ℝ} (hc : val ≤ c) :
    (Set.Iic a).indicator (fun q => val - max c q) q ≤ 0 := by
  by_cases hqa : q ≤ a
  · rw [Set.indicator_of_mem (show q ∈ Set.Iic a from hqa)]
    have := le_max_left c q; linarith
  · rw [Set.indicator_of_notMem (show q ∉ Set.Iic a from hqa)]

lemma ind_nonneg {c val q : ℝ} (hc : c ≤ val) :
    0 ≤ (Set.Iic val).indicator (fun q => val - max c q) q := by
  by_cases hqv : q ≤ val
  · rw [Set.indicator_of_mem (show q ∈ Set.Iic val from hqv)]
    have : max c q ≤ val := max_le hc hqv
    linarith
  · rw [Set.indicator_of_notMem (show q ∉ Set.Iic val from hqv)]

lemma integrable_ind_sub (ρ : Measure ℝ) [IsFiniteMeasure ρ] (a c val : ℝ) :
    Integrable (fun q => (Set.Iic a).indicator (fun q => val - max c q) q) ρ := by
  have h1 : (fun q => (Set.Iic a).indicator (fun q => val - max c q) q)
      = fun q => (Set.Iic a).indicator (fun _ => val) q
          - (Set.Iic a).indicator (fun q => max c q) q := by
    funext q
    by_cases hq : q ∈ Set.Iic a
    · simp [Set.indicator_of_mem hq]
    · simp [Set.indicator_of_notMem hq]
  rw [h1]
  exact ((integrable_const val).indicator measurableSet_Iic).sub (integrable_ind_max ρ a c)

/-- truthful utility of buyer `i` is nonnegative, and equals this integral when `i` wins -/
lemma truthful_util (ρ : Measure ℝ) [IsFiniteMeasure ρ] (v : Fin n → ℝ) (hv : v ∈ cube n)
    (i : Fin n) :
    0 ≤ v i * (SPA (n := n) ρ).x i v - (SPA (n := n) ρ).p i v := by
  rw [SPA_x, SPA_p]
  by_cases hw : isWinner v i
  · rw [if_pos hw, if_pos hw, util_eq, second_eq_cmax hw]
    exact integral_nonneg (fun q => ind_nonneg (cmax_le_of_winner hw (hv i (Set.mem_univ _)).1))
  · rw [if_neg hw, if_neg hw]; simp

lemma meas_winner (i : Fin n) : MeasurableSet {v : Fin n → ℝ | isWinner v i} := by
  unfold isWinner
  refine measurableSet_setOfPred.2 (Measurable.and (Measurable.forall fun j => ?_)
    (Measurable.forall fun j => Measurable.imp measurable_const ?_))
  · exact measurableSet_setOfPred.1 (measurableSet_le (measurable_pi_apply j) (measurable_pi_apply i))
  · exact measurableSet_setOfPred.1 (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i))

lemma meas_second : Measurable (fun v : Fin n → ℝ => second v) := by
  unfold second
  exact Measurable.iSup (fun q => (measurable_pi_apply _).min (measurable_pi_apply _))

theorem SPA_isDSIC' (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    (SPA (n := n) ρ).IsDSIC := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v _ i
    rw [SPA_x]
    split_ifs
    · refine ⟨ENNReal.toReal_nonneg, ?_⟩
      have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := ρ) (s := Set.Iic (v i)))
      simpa using this
    · exact ⟨le_refl _, zero_le_one⟩
  · intro v hv i
    exact truthful_util ρ v hv i
  · intro v hv i w hw
    have htr := truthful_util ρ v hv i
    rw [SPA_x, SPA_p]
    by_cases hw' : isWinner (Function.update v i w) i
    · rw [if_pos hw', if_pos hw', second_eq_cmax hw', cmax_update, Function.update_self, util_eq]
      by_cases hvw : isWinner v i
      · rw [SPA_x, SPA_p, if_pos hvw, if_pos hvw, util_eq, second_eq_cmax hvw]
        exact integral_mono (integrable_ind_sub ρ _ _ _) (integrable_ind_sub ρ _ _ _)
          (fun q => ind_le_ind (cmax_le_of_winner hvw (hv i (Set.mem_univ _)).1))
      · rw [SPA_x, SPA_p, if_neg hvw, if_neg hvw]
        simp only [mul_zero, sub_zero]
        exact integral_nonpos (fun q => ind_nonpos (le_cmax_of_not_winner hvw))
    · rw [if_neg hw', if_neg hw']
      simpa using htr
  · intro v _
    by_cases h : ∃ i, isWinner v i
    · obtain ⟨i0, h0⟩ := h
      rw [Finset.sum_eq_single i0 (fun j _ hj => by
        rw [SPA_x, if_neg (fun hw => hj (isWinner_unique hw h0))])
        (fun h => absurd (Finset.mem_univ i0) h)]
      rw [SPA_x, if_pos h0]
      have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := ρ) (s := Set.Iic (v i0)))
      simpa using this
    · push_neg at h
      rw [Finset.sum_eq_zero (fun j _ => by rw [SPA_x, if_neg (h j)])]
      exact zero_le_one
  · intro i
    have hmono : Monotone (fun a : ℝ => (ρ (Set.Iic a)).toReal) := fun a b hab =>
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.2 hab))
    exact Measurable.ite (meas_winner i) (hmono.measurable.comp (measurable_pi_apply i))
      measurable_const
  · intro i
    refine Measurable.ite (meas_winner i) ?_ measurable_const
    have hf : StronglyMeasurable (Function.uncurry fun (v : Fin n → ℝ) (q : ℝ) =>
        (Set.Iic (v i)).indicator (fun q => max (second v) q) q) := by
      apply Measurable.stronglyMeasurable
      change Measurable (fun z : (Fin n → ℝ) × ℝ =>
        (Set.Iic (z.1 i)).indicator (fun q => max (second z.1) q) z.2)
      simp only [Set.indicator_apply, Set.mem_Iic]
      exact Measurable.ite (measurableSet_le measurable_snd
        ((measurable_pi_apply i).comp measurable_fst))
        ((meas_second.comp measurable_fst).max measurable_snd) measurable_const
    exact (hf.integral_prod_right (ν := ρ)).measurable
  · refine ⟨1, fun v hv i => ?_⟩
    rw [SPA_p]
    split_ifs
    · have := norm_integral_le_of_norm_le_const (μ := ρ)
        (f := fun q => (Set.Iic (v i)).indicator (fun q => max (second v) q) q) (C := 1)
        (Filter.Eventually.of_forall fun q => ?_)
      · simpa using this
      · have h0 := second_nonneg hv
        have h1 := second_le_one hv
        have hvi := (hv i (Set.mem_univ _)).2
        by_cases hq : q ≤ v i
        · rw [Set.indicator_of_mem (show q ∈ Set.Iic (v i) from hq), Real.norm_eq_abs, abs_le]
          constructor
          · have := le_max_left (second v) q; linarith
          · exact max_le h1 (hq.trans hvi)
        · rw [Set.indicator_of_notMem (show q ∉ Set.Iic (v i) from hq)]; simp
    · simp

end RSPA3


namespace RSPA3
open RobustSPA.AllDist

lemma meas_single {n : ℕ} (k : Fin n) :
    Measurable (fun t : ℝ => (Pi.single k t : Fin n → ℝ)) := by
  refine measurable_pi_lambda _ (fun j => ?_)
  by_cases h : j = k
  · subst h; simp only [Pi.single_eq_same]; exact measurable_id'
  · simp [h]

lemma single_mem_cube_iff {n : ℕ} (k : Fin n) (t : ℝ) :
    (Pi.single k t : Fin n → ℝ) ∈ cube n ↔ t ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · intro h
    have := h k (Set.mem_univ _)
    simpa using this
  · intro ht j _
    by_cases hj : j = k
    · subst hj; simpa using ht
    · simp [Pi.single_apply, hj]

lemma measurableSet_cube (n : ℕ) : MeasurableSet (cube n) := by
  unfold cube
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

lemma Fstar_apply {n : ℕ} (G : Measure ℝ) (s : Set (Fin n → ℝ)) (hs : MeasurableSet s) :
    Fstar n G s = (n : ENNReal)⁻¹ * ∑ k : Fin n, G ((fun t : ℝ => (Pi.single k t : Fin n → ℝ)) ⁻¹' s) := by
  unfold Fstar
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Measure.map_apply (meas_single k) hs]

theorem Fstar_mem_Fexc (n : ℕ) (hn : 0 < n) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : G (Set.Icc 0 1)ᶜ = 0) : Fstar n G ∈ Fexc n := by
  refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · rw [Fstar_apply G _ MeasurableSet.univ]
    simp only [Set.preimage_univ, measure_univ, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    have : (n : ENNReal) ≠ 0 := by exact_mod_cast hn.ne'
    exact ENNReal.inv_mul_cancel this (ENNReal.natCast_ne_top n)
  · rw [Fstar_apply G _ (measurableSet_cube n).compl]
    have : ∀ k : Fin n, G ((fun t : ℝ => (Pi.single k t : Fin n → ℝ)) ⁻¹' (cube n)ᶜ) = 0 := by
      intro k
      have hpre : ((fun t : ℝ => (Pi.single k t : Fin n → ℝ)) ⁻¹' (cube n)ᶜ) = (Set.Icc 0 1)ᶜ := by
        ext t; simp [single_mem_cube_iff]
      rw [hpre, hG]
    rw [Finset.sum_eq_zero (fun k _ => this k), mul_zero]
  · intro σ
    ext s hs
    have hmσ : Measurable (fun v : Fin n → ℝ => v ∘ σ) := by fun_prop
    rw [Measure.map_apply hmσ hs, Fstar_apply G _ (hmσ hs), Fstar_apply G _ hs]
    congr 1
    have key : ∀ k : Fin n, ((fun t : ℝ => (Pi.single k t : Fin n → ℝ)) ⁻¹' ((fun v : Fin n → ℝ => v ∘ σ) ⁻¹' s))
        = (fun t : ℝ => (Pi.single (σ.symm k) t : Fin n → ℝ)) ⁻¹' s := by
      intro k
      ext t
      simp only [Set.mem_preimage]
      have : ((Pi.single k t : Fin n → ℝ) ∘ σ) = Pi.single (σ.symm k) t := by
        funext j
        simp only [Function.comp, Pi.single_apply]
        congr 1
        exact propext ⟨fun h => by rw [← h]; simp, fun h => by rw [h]; simp⟩
      rw [this]
    simp_rw [key]
    exact Equiv.sum_comp σ.symm (fun k => G ((fun t : ℝ => (Pi.single k t : Fin n → ℝ)) ⁻¹' s))

end RSPA3


namespace RSPA3
open RobustSPA.AllDist

variable {n : ℕ}

/-- the uniform law on `[0,1]` -/
noncomputable abbrev unif : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)

lemma unif_prob : IsProbabilityMeasure unif := by
  constructor
  simp [unif]

lemma meas_E : Measurable (fun u : ℝ => Real.exp (u - 1)) := by fun_prop

lemma preimage_E (a : ℝ) (ha : 0 < a) :
    (fun u : ℝ => Real.exp (u - 1)) ⁻¹' Set.Iic a = Set.Iic (Real.log a + 1) := by
  ext u
  simp only [Set.mem_preimage, Set.mem_Iic]
  rw [← Real.le_log_iff_exp_le ha]
  constructor <;> intro h <;> linarith

lemma rho_eq (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hρ : ∀ t, cdfOf ρ t = PhiE t) :
    ρ = unif.map (fun u : ℝ => Real.exp (u - 1)) := by
  apply Measure.ext_of_Iic
  intro a
  have h1 : ρ (Set.Iic a) = ENNReal.ofReal (PhiE a) := by
    rw [← hρ a, cdfOf, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [h1, Measure.map_apply meas_E measurableSet_Iic, Measure.restrict_apply
    (meas_E measurableSet_Iic)]
  have he : 0 < Real.exp (-1) := Real.exp_pos _
  unfold PhiE
  by_cases ha0 : a ≤ 0
  · have : (fun u : ℝ => Real.exp (u - 1)) ⁻¹' Set.Iic a = ∅ := by
      ext u; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_le_of_lt ha0 (Real.exp_pos _)
    rw [this, if_pos (by linarith)]; simp
  push_neg at ha0
  rw [preimage_E a ha0]
  by_cases h2 : a ≤ Real.exp (-1)
  · rw [if_pos h2]
    have hL : Real.log a + 1 ≤ 0 := by
      have := (Real.log_le_iff_le_exp ha0).2 h2; linarith
    simp only [ENNReal.ofReal_zero]
    symm
    apply measure_mono_null (t := Set.Icc 0 (Real.log a + 1))
    · intro u ⟨hu1, hu2⟩; exact ⟨hu2.1, hu1⟩
    · rw [Real.volume_Icc]; simp; linarith
  · rw [if_neg h2]
    push_neg at h2
    have hL : 0 < Real.log a + 1 := by
      have := (Real.log_le_iff_le_exp ha0).not.2 (not_le.2 h2); linarith
    by_cases h3 : a ≤ 1
    · rw [if_pos h3]
      have hL1 : Real.log a + 1 ≤ 1 := by have := Real.log_nonpos ha0.le h3; linarith
      have : Set.Iic (Real.log a + 1) ∩ Set.Icc 0 1 = Set.Icc 0 (Real.log a + 1) := by
        ext u; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        constructor
        · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
      rw [this, Real.volume_Icc, sub_zero]
    · rw [if_neg h3]
      push_neg at h3
      have hL1 : 1 < Real.log a + 1 := by have := Real.log_pos h3; linarith
      have : Set.Iic (Real.log a + 1) ∩ Set.Icc 0 1 = Set.Icc 0 1 := by
        ext u; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        constructor
        · rintro ⟨_, h⟩; exact h
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1, h2⟩
      rw [this, Real.volume_Icc]; simp

/-- the winner payment integral -/
noncomputable def J (ρ : Measure ℝ) (a b : ℝ) : ℝ :=
  ∫ q, (Set.Iic a).indicator (fun q => max b q) q ∂ρ

lemma J_map (a b : ℝ) :
    J (unif.map (fun u : ℝ => Real.exp (u - 1))) a b
      = ∫ u in Set.Icc (0:ℝ) 1, (Set.Iic a).indicator (fun q => max b q) (Real.exp (u - 1)) := by
  unfold J
  rw [integral_map meas_E.aemeasurable]
  exact ((measurable_const.max measurable_id).indicator measurableSet_Iic).aestronglyMeasurable

lemma J_small (a b : ℝ) (ha : a < Real.exp (-1)) :
    J (unif.map (fun u : ℝ => Real.exp (u - 1))) a b = 0 := by
  rw [J_map]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro u hu
  apply Set.indicator_of_notMem
  simp only [Set.mem_Iic, not_le]
  calc a < Real.exp (-1) := ha
    _ ≤ Real.exp (u - 1) := Real.exp_le_exp.2 (by linarith [hu.1])

lemma J_big (a b : ℝ) (ha : Real.exp (-1) ≤ a) (ha1 : a ≤ 1) :
    J (unif.map (fun u : ℝ => Real.exp (u - 1))) a b
      = ∫ u in (0:ℝ)..(Real.log a + 1), max b (Real.exp (u - 1)) := by
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos _) ha
  have hL0 : 0 ≤ Real.log a + 1 := by
    have := (Real.le_log_iff_exp_le ha0).2 ha; linarith
  have hL1 : Real.log a + 1 ≤ 1 := by have := Real.log_nonpos ha0.le ha1; linarith
  rw [J_map]
  have : (fun u => (Set.Iic a).indicator (fun q => max b q) (Real.exp (u - 1)))
      = (Set.Iic (Real.log a + 1)).indicator (fun u => max b (Real.exp (u - 1))) := by
    funext u
    by_cases hu : u ≤ Real.log a + 1
    · rw [Set.indicator_of_mem (show u ∈ Set.Iic (Real.log a + 1) from hu),
        Set.indicator_of_mem]
      show Real.exp (u - 1) ≤ a
      rw [← Real.le_log_iff_exp_le ha0]; linarith
    · rw [Set.indicator_of_notMem (show u ∉ Set.Iic (Real.log a + 1) from hu),
        Set.indicator_of_notMem]
      simp only [Set.mem_Iic, not_le]
      rw [← Real.log_lt_iff_lt_exp ha0]; push_neg at hu; linarith
  rw [this, setIntegral_indicator measurableSet_Iic]
  have hs : Set.Icc (0:ℝ) 1 ∩ Set.Iic (Real.log a + 1) = Set.Icc 0 (Real.log a + 1) := by
    ext u; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, h2⟩
  rw [hs, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL0]

lemma integral_exp_sub (x y : ℝ) :
    ∫ u in x..y, Real.exp (u - 1) = Real.exp (y - 1) - Real.exp (x - 1) := by
  rw [intervalIntegral.integral_comp_sub_right (fun u => Real.exp u), integral_exp]

lemma J_case2 (a b : ℝ) (ha : Real.exp (-1) ≤ a) (ha1 : a ≤ 1) (hb : b ≤ Real.exp (-1)) :
    J (unif.map (fun u : ℝ => Real.exp (u - 1))) a b = a - Real.exp (-1) := by
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos _) ha
  have hL0 : 0 ≤ Real.log a + 1 := by
    have := (Real.le_log_iff_exp_le ha0).2 ha; linarith
  rw [J_big a b ha ha1]
  rw [intervalIntegral.integral_congr (g := fun u => Real.exp (u - 1))]
  · rw [integral_exp_sub]
    have : Real.log a + 1 - 1 = Real.log a := by ring
    rw [this, Real.exp_log ha0]; norm_num
  · intro u hu
    rw [Set.uIcc_of_le hL0] at hu
    apply max_eq_right
    exact hb.trans (Real.exp_le_exp.2 (by linarith [hu.1]))

lemma J_case3 (a b : ℝ) (ha1 : a ≤ 1) (hb : Real.exp (-1) < b) (hba : b ≤ a) :
    J (unif.map (fun u : ℝ => Real.exp (u - 1))) a b = b * Real.log b + a := by
  have ha : Real.exp (-1) ≤ a := hb.le.trans hba
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos _) ha
  have hb0 : 0 < b := lt_trans (Real.exp_pos _) hb
  have hM0 : 0 ≤ Real.log b + 1 := by
    have := (Real.le_log_iff_exp_le hb0).2 hb.le; linarith
  have hML : Real.log b + 1 ≤ Real.log a + 1 := by
    have := Real.log_le_log hb0 hba; linarith
  rw [J_big a b ha ha1]
  have hc : Continuous (fun u => max b (Real.exp (u - 1))) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := Real.log b + 1)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_congr (g := fun _ => b) (a := 0) (b := Real.log b + 1),
    intervalIntegral.integral_congr (g := fun u => Real.exp (u - 1)) (a := Real.log b + 1)
      (b := Real.log a + 1)]
  · rw [integral_exp_sub, intervalIntegral.integral_const]
    have h1 : Real.log a + 1 - 1 = Real.log a := by ring
    have h2 : Real.log b + 1 - 1 = Real.log b := by ring
    rw [h1, h2, Real.exp_log ha0, Real.exp_log hb0, smul_eq_mul]; ring
  · intro u hu
    rw [Set.uIcc_of_le hML] at hu
    apply max_eq_right
    have : Real.exp (Real.log b + 1 - 1) ≤ Real.exp (u - 1) := Real.exp_le_exp.2 (by linarith [hu.1])
    rwa [show Real.log b + 1 - 1 = Real.log b by ring, Real.exp_log hb0] at this
  · intro u hu
    rw [Set.uIcc_of_le hM0] at hu
    apply max_eq_left
    have : Real.exp (u - 1) ≤ Real.exp (Real.log b + 1 - 1) := Real.exp_le_exp.2 (by linarith [hu.2])
    rwa [show Real.log b + 1 - 1 = Real.log b by ring, Real.exp_log hb0] at this

lemma neg_mul_log_lt (b : ℝ) (hb : Real.exp (-1) < b) : -(b * Real.log b) < Real.exp (-1) := by
  have hb0 : 0 < b := lt_trans (Real.exp_pos _) hb
  have hx : 0 < Real.exp (-1) / b := div_pos (Real.exp_pos _) hb0
  have hx1 : Real.exp (-1) / b ≠ 1 := by
    intro h; rw [div_eq_one_iff_eq hb0.ne'] at h; linarith
  have := Real.log_lt_sub_one_of_pos hx hx1
  rw [Real.log_div (Real.exp_pos _).ne' hb0.ne', Real.log_exp] at this
  have h2 : b * (-1 - Real.log b) < b * (Real.exp (-1) / b - 1) := mul_lt_mul_of_pos_left this hb0
  have h4 : b * (Real.exp (-1) / b - 1) = Real.exp (-1) - b := by
    rw [mul_sub, mul_div_cancel₀ _ hb0.ne', mul_one]
  rw [h4] at h2
  linarith

lemma exists_winner (hn : 0 < n) (v : Fin n → ℝ) : ∃ i, isWinner v i := by
  obtain ⟨i1, _, hi1⟩ := Finset.exists_max_image Finset.univ v ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  let S := Finset.univ.filter (fun i => ∀ j, v j ≤ v i)
  have hS : S.Nonempty := ⟨i1, by simp [S]; exact fun j => hi1 j (Finset.mem_univ _)⟩
  refine ⟨S.min' hS, ?_, ?_⟩
  · have := S.min'_mem hS
    simp only [S, Finset.mem_filter] at this
    exact this.2
  · intro j hj
    by_contra hcon
    push_neg at hcon
    have hmem := S.min'_mem hS
    simp only [S, Finset.mem_filter] at hmem
    have hjS : j ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      intro k; exact (hmem.2 k).trans hcon
    exact absurd (S.min'_le j hjS) (not_le.2 hj)

lemma top_eq_of_winner {v : Fin n → ℝ} {i : Fin n} (hw : isWinner v i) : top v = v i := by
  haveI : Nonempty (Fin n) := ⟨i⟩
  exact le_antisymm (ciSup_le hw.1) (le_ciSup (Finite.bddAbove_range v) i)

lemma sum_p_SPA (ρ : Measure ℝ) {v : Fin n → ℝ} {i : Fin n} (hw : isWinner v i) :
    ∑ j, (SPA (n := n) ρ).p j v = J ρ (v i) (cmax v i) := by
  rw [Finset.sum_eq_single i (fun j _ hj => by
        rw [SPA_p, if_neg (fun hw' => hj (isWinner_unique hw' hw))])
        (fun h => absurd (Finset.mem_univ i) h)]
  rw [SPA_p, if_pos hw, second_eq_cmax hw]; rfl

theorem pw_main (hn : 0 < n) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ : ∀ t, cdfOf ρ t = PhiE t) (v : Fin n → ℝ) (hv : v ∈ cube n) :
    top v - ∑ i, (SPA ρ).p i v ≤ Real.exp (-1) ∧
    (second v ≤ Real.exp (-1) → Real.exp (-1) ≤ top v →
      top v - ∑ i, (SPA ρ).p i v = Real.exp (-1)) ∧
    (Real.exp (-1) < second v →
      top v - ∑ i, (SPA ρ).p i v = -(second v * Real.log (second v)) ∧
      -(second v * Real.log (second v)) < Real.exp (-1)) ∧
    (top v < Real.exp (-1) → top v - ∑ i, (SPA ρ).p i v = top v) := by
  obtain ⟨i, hw⟩ := exists_winner hn v
  rw [sum_p_SPA ρ hw, top_eq_of_winner hw, ← second_eq_cmax hw, rho_eq ρ hρ]
  have hvi := hv i (Set.mem_univ _)
  have hb0 := second_nonneg hv
  have hba : second v ≤ v i := by rw [second_eq_cmax hw]; exact cmax_le_of_winner hw hvi.1
  have he : 0 < Real.exp (-1) := Real.exp_pos _
  have c2 : second v ≤ Real.exp (-1) → Real.exp (-1) ≤ v i →
      v i - J (unif.map (fun u : ℝ => Real.exp (u - 1))) (v i) (second v) = Real.exp (-1) := by
    intro h1 h2; rw [J_case2 _ _ h2 hvi.2 h1]; ring
  have c3 : Real.exp (-1) < second v →
      v i - J (unif.map (fun u : ℝ => Real.exp (u - 1))) (v i) (second v)
        = -(second v * Real.log (second v)) ∧
      -(second v * Real.log (second v)) < Real.exp (-1) := by
    intro h1; rw [J_case3 _ _ hvi.2 h1 hba]; exact ⟨by ring, neg_mul_log_lt _ h1⟩
  have c4 : v i < Real.exp (-1) →
      v i - J (unif.map (fun u : ℝ => Real.exp (u - 1))) (v i) (second v) = v i := by
    intro h1; rw [J_small _ _ h1]; ring
  refine ⟨?_, c2, c3, c4⟩
  by_cases h1 : v i < Real.exp (-1)
  · rw [c4 h1]; exact h1.le
  · push_neg at h1
    by_cases h2 : second v ≤ Real.exp (-1)
    · rw [c2 h2 h1]
    · push_neg at h2; exact ((c3 h2).1 ▸ (c3 h2).2).le

end RSPA3


theorem solution (n : ℕ) (hn : 0 < n) (ρ : ProbabilityMeasure ℝ)
    (hρ : ∀ t, RobustSPA.AllDist.cdfOf ρ t = RobustSPA.AllDist.PhiE t) (v : Fin n → ℝ)
    (hv : v ∈ RobustSPA.AllDist.cube n) :
    RobustSPA.AllDist.top v - ∑ i, (RobustSPA.AllDist.SPA (ρ : Measure ℝ)).p i v ≤ Real.exp (-1) ∧
    (RobustSPA.AllDist.second v ≤ Real.exp (-1) → Real.exp (-1) ≤ RobustSPA.AllDist.top v →
      RobustSPA.AllDist.top v - ∑ i, (RobustSPA.AllDist.SPA (ρ : Measure ℝ)).p i v = Real.exp (-1)) ∧
    (Real.exp (-1) < RobustSPA.AllDist.second v →
      RobustSPA.AllDist.top v - ∑ i, (RobustSPA.AllDist.SPA (ρ : Measure ℝ)).p i v
        = -(RobustSPA.AllDist.second v * Real.log (RobustSPA.AllDist.second v)) ∧
      -(RobustSPA.AllDist.second v * Real.log (RobustSPA.AllDist.second v)) < Real.exp (-1)) ∧
    (RobustSPA.AllDist.top v < Real.exp (-1) →
      RobustSPA.AllDist.top v - ∑ i, (RobustSPA.AllDist.SPA (ρ : Measure ℝ)).p i v
        = RobustSPA.AllDist.top v) :=
  RSPA3.pw_main hn (ρ : Measure ℝ) hρ v hv
