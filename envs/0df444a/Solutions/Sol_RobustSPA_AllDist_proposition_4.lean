-- Prove2me | solution 1 for RobustSPA.AllDist.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T08:50:26.401775+00:00
-- url     : https://prove2.me/submissions/57b0a446-4d9e-4947-974e-c20bdd070f4e

import Mathlib
import Definitions.Def_RobustSPA_AllDist_Setting
import Theorems.Thm_RobustSPA_AllDist_SPA_isDSIC
import Theorems.Thm_RobustSPA_AllDist_pointwise_regret_le_inv_e
import Theorems.Thm_RobustSPA_AllDist_revenue_under_Fstar
import Theorems.Thm_RobustSPA_AllDist_Fstar_exchangeable
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


namespace RSPA3

/-- If `F` has increments squeezed by a monotone `f`, then `∫ f = F b - F a`. -/
theorem integral_eq_of_squeeze {f F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Set.Icc a b))
    (h : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      (t - s) * f s ≤ F t - F s ∧ F t - F s ≤ (t - s) * f t) :
    ∫ x in a..b, f x = F b - F a := by
  set E := |(∫ x in a..b, f x) - (F b - F a)| with hE
  have hfab : f a ≤ f b := hf ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab
  set C := (b - a) * (f b - f a) with hC
  have key : ∀ N : ℕ, 0 < N → E ≤ C / N := by
    intro N hN
    have hNpos : (0:ℝ) < N := by exact_mod_cast hN
    set δ := (b - a) / N with hδ
    have hδ0 : 0 ≤ δ := div_nonneg (by linarith) hNpos.le
    let x : ℕ → ℝ := fun j => a + j * δ
    have hxN : x N = b := by
      simp only [x, hδ]; field_simp; ring
    have hx0 : x 0 = a := by simp [x]
    have hxmem : ∀ j, j ≤ N → x j ∈ Set.Icc a b := by
      intro j hj
      refine ⟨by simp only [x]; nlinarith [hδ0], ?_⟩
      have : (j:ℝ) * δ ≤ N * δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ0
      have h2 : (N:ℝ) * δ = b - a := by simp only [hδ]; field_simp
      simp only [x]; linarith
    have hxsucc : ∀ j, x (j + 1) = x j + δ := by intro j; simp only [x]; push_cast; ring
    have hint : ∀ j < N, IntervalIntegrable f volume (x j) (x (j + 1)) := by
      intro j hj
      apply MonotoneOn.intervalIntegrable
      rw [Set.uIcc_of_le (by rw [hxsucc]; linarith)]
      exact hf.mono (Set.Icc_subset_Icc (hxmem j hj.le).1 (hxmem (j+1) hj).2)
    have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
    rw [hx0, hxN] at hsum
    have htel : ∑ j ∈ Finset.range N, (F (x (j + 1)) - F (x j)) = F b - F a := by
      rw [Finset.sum_range_sub (fun j => F (x j)), hxN, hx0]
    have htelf : ∑ j ∈ Finset.range N, (f (x (j + 1)) - f (x j)) = f b - f a := by
      rw [Finset.sum_range_sub (fun j => f (x j)), hxN, hx0]
    have hpiece : ∀ j ∈ Finset.range N,
        |(∫ y in x j..x (j + 1), f y) - (F (x (j + 1)) - F (x j))|
          ≤ δ * (f (x (j + 1)) - f (x j)) := by
      intro j hj
      have hj' : j < N := Finset.mem_range.1 hj
      have hle : x j ≤ x (j + 1) := by rw [hxsucc]; linarith
      have hmj := hxmem j hj'.le
      have hmj1 := hxmem (j + 1) hj'
      have hlo : ∫ y in x j..x (j + 1), f (x j) ≤ ∫ y in x j..x (j + 1), f y :=
        intervalIntegral.integral_mono_on hle intervalIntegrable_const (hint j hj')
          (fun y hy => hf hmj ⟨hmj.1.trans hy.1, hy.2.trans hmj1.2⟩ hy.1)
      have hhi : ∫ y in x j..x (j + 1), f y ≤ ∫ y in x j..x (j + 1), f (x (j + 1)) :=
        intervalIntegral.integral_mono_on hle (hint j hj') intervalIntegrable_const
          (fun y hy => hf ⟨hmj.1.trans hy.1, hy.2.trans hmj1.2⟩ hmj1 hy.2)
      rw [intervalIntegral.integral_const, smul_eq_mul] at hlo hhi
      have hd : x (j + 1) - x j = δ := by rw [hxsucc]; ring
      rw [hd] at hlo hhi
      obtain ⟨h1, h2⟩ := h (x j) (x (j + 1)) hmj.1 hle hmj1.2
      rw [hd] at h1 h2
      rw [abs_le]; constructor <;> nlinarith
    have : (∫ x in a..b, f x) - (F b - F a)
        = ∑ j ∈ Finset.range N, ((∫ y in x j..x (j + 1), f y) - (F (x (j + 1)) - F (x j))) := by
      rw [Finset.sum_sub_distrib, hsum, htel]
    rw [hE, this]
    calc |∑ j ∈ Finset.range N, ((∫ y in x j..x (j + 1), f y) - (F (x (j + 1)) - F (x j)))|
        ≤ ∑ j ∈ Finset.range N, |(∫ y in x j..x (j + 1), f y) - (F (x (j + 1)) - F (x j))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range N, δ * (f (x (j + 1)) - f (x j)) := Finset.sum_le_sum hpiece
      _ = C / N := by rw [← Finset.mul_sum, htelf, hδ, hC]; ring
  have hC0 : 0 ≤ C := mul_nonneg (by linarith) (by linarith)
  have hE0 : E = 0 := by
    by_contra hne
    have hEpos : 0 < E := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    obtain ⟨N, hN⟩ := exists_nat_gt (C / E)
    have hNpos : (0:ℝ) < N := lt_of_le_of_lt (div_nonneg hC0 hEpos.le) hN
    have h1 := key N (by exact_mod_cast hNpos)
    rw [le_div_iff₀ hNpos] at h1
    rw [div_lt_iff₀ hEpos] at hN
    linarith
  have := abs_eq_zero.1 hE0
  linarith

/-- antitone version -/
theorem integral_eq_of_squeeze_anti {f F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AntitoneOn f (Set.Icc a b))
    (h : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      (t - s) * f t ≤ F t - F s ∧ F t - F s ≤ (t - s) * f s) :
    ∫ x in a..b, f x = F b - F a := by
  have := integral_eq_of_squeeze (f := fun x => -f x) (F := fun x => -F x) hab
    (fun x hx y hy hxy => neg_le_neg (hf hx hy hxy))
    (fun s t h1 h2 h3 => by
      obtain ⟨k1, k2⟩ := h s t h1 h2 h3
      constructor <;> nlinarith)
  rw [intervalIntegral.integral_neg] at this
  linarith

end RSPA3


namespace RSPA3
open RobustSPA.AllDist

variable {n : ℕ}

/-- `T(u) = 1 / max(1, e u)`: the isorevenue law is the law of `T(U)`, `U ∼ Unif[0,1]`. -/
noncomputable def Tm (u : ℝ) : ℝ := (max 1 (Real.exp 1 * u))⁻¹

lemma meas_Tm : Measurable Tm := by unfold Tm; fun_prop

lemma exp_neg_one_eq : Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]

lemma Tm_pos (u : ℝ) : 0 < Tm u := by
  unfold Tm; exact inv_pos.2 (lt_of_lt_of_le one_pos (le_max_left _ _))

lemma Tm_le_one (u : ℝ) : Tm u ≤ 1 := by
  unfold Tm; exact inv_le_one_of_one_le₀ (le_max_left _ _)

lemma Tm_ge (u : ℝ) (hu : u ≤ 1) : Real.exp (-1) ≤ Tm u := by
  unfold Tm; rw [exp_neg_one_eq]
  apply inv_anti₀ (lt_of_lt_of_le one_pos (le_max_left _ _))
  exact max_le (Real.one_le_exp zero_le_one) (by have := Real.exp_pos 1; nlinarith)

lemma Tm_mem (u : ℝ) (hu : u ≤ 1) : Tm u ∈ Set.Icc (0:ℝ) 1 :=
  ⟨(Tm_pos u).le, Tm_le_one u⟩

lemma Tm_small (u : ℝ) (hu : u ≤ Real.exp (-1)) : Tm u = 1 := by
  unfold Tm
  have : Real.exp 1 * u ≤ 1 := by
    rw [exp_neg_one_eq] at hu
    have := mul_le_mul_of_nonneg_left hu (Real.exp_pos 1).le
    rwa [mul_inv_cancel₀ (Real.exp_pos 1).ne'] at this
  rw [max_eq_left this, inv_one]

lemma Tm_big (u : ℝ) (hu : Real.exp (-1) ≤ u) : Tm u = Real.exp (-1) / u := by
  unfold Tm
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos _) hu
  have : 1 ≤ Real.exp 1 * u := by
    rw [exp_neg_one_eq] at hu
    have := mul_le_mul_of_nonneg_left hu (Real.exp_pos 1).le
    rwa [mul_inv_cancel₀ (Real.exp_pos 1).ne'] at this
  rw [max_eq_right this, exp_neg_one_eq, mul_inv, div_eq_mul_inv]

lemma Tm_anti : AntitoneOn Tm (Set.Icc 0 1) := by
  intro x _ y _ hxy
  unfold Tm
  apply inv_anti₀ (lt_of_lt_of_le one_pos (le_max_left _ _))
  exact max_le_max (le_refl _) (mul_le_mul_of_nonneg_left hxy (Real.exp_pos 1).le)

lemma G_eq (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : ∀ t, cdfOf G t = isoCDF (Real.exp (-1)) t) : G = unif.map Tm := by
  apply Measure.ext_of_Iic
  intro a
  have h1 : G (Set.Iic a) = ENNReal.ofReal (isoCDF (Real.exp (-1)) a) := by
    rw [← hG a, cdfOf, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [h1, Measure.map_apply meas_Tm measurableSet_Iic, Measure.restrict_apply
    (meas_Tm measurableSet_Iic)]
  have he : 0 < Real.exp (-1) := Real.exp_pos _
  have he1 : Real.exp (-1) < 1 := by have := Real.exp_lt_exp.2 (show (-1:ℝ) < 0 by norm_num); simpa using this
  have hE : 0 < Real.exp 1 := Real.exp_pos _
  unfold isoCDF
  by_cases ha1 : 1 ≤ a
  · rw [if_neg (by linarith), if_neg (by linarith)]
    have : Tm ⁻¹' Set.Iic a ∩ Set.Icc 0 1 = Set.Icc 0 1 := by
      ext u; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
      exact ⟨fun h => h.2, fun h => ⟨(Tm_le_one u).trans ha1, h⟩⟩
    rw [this, Real.volume_Icc]; simp
  push_neg at ha1
  by_cases hae : a < Real.exp (-1)
  · rw [if_pos hae, ENNReal.ofReal_zero]
    have : Tm ⁻¹' Set.Iic a ∩ Set.Icc 0 1 = ∅ := by
      ext u; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro h hu
      have := Tm_ge u hu.2; linarith
    rw [this, measure_empty]
  · push_neg at hae
    rw [if_neg (not_lt.2 hae), if_pos ha1]
    have ha0 : 0 < a := lt_of_lt_of_le he hae
    -- threshold `1/(e a)`
    set θ := Real.exp (-1) / a with hθ
    have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one ha0]; exact hae
    have hθ0 : 0 ≤ θ := div_nonneg he.le ha0.le
    have : Tm ⁻¹' Set.Iic a ∩ Set.Icc 0 1 = Set.Icc θ 1 := by
      ext u; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h, hu0, hu1⟩
        refine ⟨?_, hu1⟩
        by_contra hlt
        push_neg at hlt
        by_cases hue : u ≤ Real.exp (-1)
        · rw [Tm_small u hue] at h; linarith
        · push_neg at hue
          rw [Tm_big u hue.le, div_le_iff₀ (lt_trans he hue)] at h
          rw [hθ, lt_div_iff₀ ha0] at hlt
          linarith
      · rintro ⟨h1, h2⟩
        have hue : Real.exp (-1) ≤ u := by
          have : Real.exp (-1) ≤ θ := by
            rw [hθ, le_div_iff₀ ha0]; nlinarith
          linarith
        refine ⟨?_, hθ0.trans h1, h2⟩
        rw [Tm_big u hue, div_le_iff₀ (lt_of_lt_of_le he hue)]
        rw [hθ, div_le_iff₀ ha0] at h1
        linarith
    rw [this, Real.volume_Icc]

lemma G_supp (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : ∀ t, cdfOf G t = isoCDF (Real.exp (-1)) t) : G (Set.Icc 0 1)ᶜ = 0 := by
  rw [G_eq G hG, Measure.map_apply meas_Tm measurableSet_Icc.compl,
    Measure.restrict_apply (meas_Tm measurableSet_Icc.compl)]
  apply measure_mono_null _ measure_empty
  intro u ⟨h1, h2⟩
  exact absurd (Tm_mem u h2.2) h1

lemma integral_G (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : ∀ t, cdfOf G t = isoCDF (Real.exp (-1)) t) (h : ℝ → ℝ) (hh : Measurable h) :
    ∫ t, h t ∂G = ∫ u in Set.Icc (0:ℝ) 1, h (Tm u) := by
  rw [G_eq G hG, integral_map meas_Tm.aemeasurable hh.aestronglyMeasurable]

/-- Single-buyer revenue identity under the isorevenue law. -/
theorem single_buyer (X P : ℝ → ℝ)
    (hIC : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Icc (0:ℝ) 1, t * X s - P s ≤ t * X t - P t) :
    ∫ u in Set.Icc (0:ℝ) 1, P (Tm u)
      = Real.exp (-1) * X 1 - (∫ t in (0:ℝ)..(Real.exp (-1)), X t) + P 0 := by
  set c := Real.exp (-1) with hc
  have hc0 : 0 < c := Real.exp_pos _
  have hc1 : c < 1 := by
    rw [hc]; have := Real.exp_lt_exp.2 (show (-1:ℝ) < 0 by norm_num); simpa using this
  have hXmono : MonotoneOn X (Set.Icc 0 1) := by
    intro s hs t ht hst
    have h1 := hIC t ht s hs
    have h2 := hIC s hs t ht
    by_contra hcon
    push_neg at hcon
    rcases eq_or_lt_of_le hst with h | h
    · subst h; exact lt_irrefl _ hcon
    · nlinarith [mul_pos (sub_pos.2 h) (sub_pos.2 hcon)]
  have hPmono : MonotoneOn P (Set.Icc 0 1) := by
    intro s hs t ht hst
    have h2 := hIC s hs t ht
    have := hXmono hs ht hst
    nlinarith [mul_nonneg hs.1 (sub_nonneg.2 this)]
  have hPT : AntitoneOn (fun u => P (Tm u)) (Set.Icc 0 1) := by
    intro x hx y hy hxy
    exact hPmono (Tm_mem y hy.2) (Tm_mem x hx.2) (Tm_anti hx hy hxy)
  -- split the integral
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have hint1 : IntervalIntegrable (fun u => P (Tm u)) volume 0 c :=
    AntitoneOn.intervalIntegrable (hPT.mono (by
      rw [Set.uIcc_of_le hc0.le]; exact Set.Icc_subset_Icc (le_refl _) hc1.le))
  have hint2 : IntervalIntegrable (fun u => P (Tm u)) volume c 1 :=
    AntitoneOn.intervalIntegrable (hPT.mono (by
      rw [Set.uIcc_of_le hc1.le]; exact Set.Icc_subset_Icc hc0.le (le_refl _)))
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have hA : ∫ u in (0:ℝ)..c, P (Tm u) = c * P 1 := by
    rw [intervalIntegral.integral_congr (g := fun _ => P 1)]
    · rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    · intro u hu
      rw [Set.uIcc_of_le hc0.le] at hu
      simp only [Tm_small u hu.2]
  -- the antitone part
  set U : ℝ → ℝ := fun t => t * X t - P t with hU
  have hB : ∫ u in c..1, P (Tm u) = (fun u => -(u * U (c / u))) 1 - (fun u => -(u * U (c / u))) c := by
    rw [intervalIntegral.integral_congr (g := fun u => P (c / u))]
    · refine integral_eq_of_squeeze_anti (f := fun x => P (c / x))
        (F := fun u => -(u * U (c / u))) hc1.le ?_ ?_
      · intro x hx y hy hxy
        have hx0 : 0 < x := lt_of_lt_of_le hc0 hx.1
        have hy0 : 0 < y := lt_of_lt_of_le hc0 hy.1
        apply hPmono
        · exact ⟨div_nonneg hc0.le hy0.le, by rw [div_le_one hy0]; exact hy.1⟩
        · exact ⟨div_nonneg hc0.le hx0.le, by rw [div_le_one hx0]; exact hx.1⟩
        · exact div_le_div_of_nonneg_left hc0.le hx0 hxy
      · intro s t hs hst ht
        have hs0 : 0 < s := lt_of_lt_of_le hc0 hs
        have ht0 : 0 < t := lt_of_lt_of_le hs0 hst
        have m1 : c / s ∈ Set.Icc (0:ℝ) 1 :=
          ⟨div_nonneg hc0.le hs0.le, by rw [div_le_one hs0]; exact hs⟩
        have m2 : c / t ∈ Set.Icc (0:ℝ) 1 :=
          ⟨div_nonneg hc0.le ht0.le, by rw [div_le_one ht0]; exact hs.trans hst⟩
        have k1 := mul_le_mul_of_nonneg_left (hIC (c / s) m1 (c / t) m2) hs0.le
        have k2 := mul_le_mul_of_nonneg_left (hIC (c / t) m2 (c / s) m1) ht0.le
        have e1 : s * (c / s) = c := mul_div_cancel₀ c hs0.ne'
        have e2 : t * (c / t) = c := mul_div_cancel₀ c ht0.ne'
        have f1 : s * (c / s * X (c / t)) = c * X (c / t) := by rw [← mul_assoc, e1]
        have f2 : s * (c / s * X (c / s)) = c * X (c / s) := by rw [← mul_assoc, e1]
        have f3 : t * (c / t * X (c / s)) = c * X (c / s) := by rw [← mul_assoc, e2]
        have f4 : t * (c / t * X (c / t)) = c * X (c / t) := by rw [← mul_assoc, e2]
        simp only [hU]
        constructor
        · nlinarith
        · nlinarith
    · intro u hu
      rw [Set.uIcc_of_le hc1.le] at hu
      simp only [Tm_big u hu.1, hc]
  -- the `[0, c]` envelope
  have hC : ∫ t in (0:ℝ)..c, X t = U c - U 0 := by
    apply integral_eq_of_squeeze hc0.le
    · exact hXmono.mono (Set.Icc_subset_Icc (le_refl _) hc1.le)
    · intro s t hs hst ht
      have m1 : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs, by linarith⟩
      have m2 : t ∈ Set.Icc (0:ℝ) 1 := ⟨hs.trans hst, by linarith⟩
      have k1 := hIC t m2 s m1
      have k2 := hIC s m1 t m2
      simp only [hU]
      constructor <;> nlinarith
  rw [hA, hB]
  have hC' := hC
  simp only [hU] at hC' ⊢
  rw [div_self hc0.ne', div_one]
  rw [hC']
  ring

end RSPA3


namespace RSPA3
open RobustSPA.AllDist

variable {n : ℕ}

lemma ae_Icc_of_null (G : Measure ℝ) (hG0 : G (Set.Icc 0 1)ᶜ = 0) :
    ∀ᵐ t ∂G, t ∈ Set.Icc (0:ℝ) 1 :=
  ae_iff.2 (by rw [show {a : ℝ | ¬ a ∈ Set.Icc 0 1} = (Set.Icc 0 1)ᶜ from rfl]; exact hG0)

theorem integral_Fstar (hn : 0 < n) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG0 : G (Set.Icc 0 1)ᶜ = 0) (g : (Fin n → ℝ) → ℝ) (hg : Measurable g) (C : ℝ)
    (hC : ∀ v ∈ cube n, |g v| ≤ C) :
    ∫ v, g v ∂(Fstar n G) = (1 / (n:ℝ)) * ∑ k : Fin n, ∫ t, g (Pi.single k t) ∂G := by
  unfold Fstar
  rw [integral_smul_measure, integral_finsetSum_measure]
  · rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, one_div]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [integral_map (meas_single k).aemeasurable hg.aestronglyMeasurable]
  · intro k _
    rw [integrable_map_measure hg.aestronglyMeasurable (meas_single k).aemeasurable]
    refine Integrable.of_bound (hg.comp (meas_single k)).aestronglyMeasurable C ?_
    filter_upwards [ae_Icc_of_null G hG0] with t ht
    rw [Function.comp_apply, Real.norm_eq_abs]
    exact hC _ ((single_mem_cube_iff k t).2 ht)

lemma intOn_Icc (h : ℝ → ℝ) (hm : Measurable h) (C : ℝ)
    (hC : ∀ u ∈ Set.Icc (0:ℝ) 1, |h u| ≤ C) : IntegrableOn h (Set.Icc (0:ℝ) 1) := by
  haveI := unif_prob
  refine Integrable.of_bound hm.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Filter.Eventually.of_forall (fun u hu => by rw [Real.norm_eq_abs]; exact hC u hu)

lemma update_single (k : Fin n) (t s : ℝ) :
    Function.update (Pi.single k t : Fin n → ℝ) k s = Pi.single k s := by
  funext j
  by_cases h : j = k
  · subst h; simp
  · simp [Function.update_of_ne h, h]

theorem revenue_main (hn : 0 < n) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : ∀ t, cdfOf G t = isoCDF (Real.exp (-1)) t) (m : Mechanism n) (hm : m.IsDSIC) :
    ∫ v, ∑ i, m.p i v ∂(Fstar n G)
        ≤ (1 / (n : ℝ)) * ∑ k : Fin n, (Real.exp (-1) * m.x k (Pi.single k 1)
            - ∫ t in (0 : ℝ)..(Real.exp (-1)), m.x k (Pi.single k t)) ∧
    ((∀ i, ∀ v ∈ cube n, v i = 0 → m.p i v = 0) →
      ∫ v, ∑ i, m.p i v ∂(Fstar n G)
        = (1 / (n : ℝ)) * ∑ k : Fin n, (Real.exp (-1) * m.x k (Pi.single k 1)
            - ∫ t in (0 : ℝ)..(Real.exp (-1)), m.x k (Pi.single k t))) := by
  obtain ⟨B, hB⟩ := hm.p_bdd
  have hg : Measurable (fun v : Fin n → ℝ => ∑ i, m.p i v) :=
    Finset.measurable_sum _ (fun i _ => hm.meas_p i)
  have hgC : ∀ v ∈ cube n, |∑ i, m.p i v| ≤ n * B := by
    intro v hv
    calc |∑ i, m.p i v| ≤ ∑ i, |m.p i v| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum (fun i _ => hB v hv i)
      _ = n * B := by simp
  have hG0 := G_supp G hG
  rw [integral_Fstar hn G hG0 _ hg _ hgC]
  -- per-buyer data
  have hcube : ∀ k : Fin n, ∀ t ∈ Set.Icc (0:ℝ) 1, (Pi.single k t : Fin n → ℝ) ∈ cube n :=
    fun k t ht => (single_mem_cube_iff k t).2 ht
  have hIC : ∀ k : Fin n, ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Icc (0:ℝ) 1,
      t * m.x k (Pi.single k s) - m.p k (Pi.single k s)
        ≤ t * m.x k (Pi.single k t) - m.p k (Pi.single k t) := by
    intro k t ht s hs
    have := hm.ic (Pi.single k t) (hcube k t ht) k s hs
    rwa [update_single, Pi.single_eq_same] at this
  have hSB := fun k : Fin n => single_buyer (fun t => m.x k (Pi.single k t))
    (fun t => m.p k (Pi.single k t)) (hIC k)
  have hmeasP : ∀ k : Fin n, Measurable (fun u => m.p k (Pi.single k (Tm u))) :=
    fun k => (hm.meas_p k).comp ((meas_single k).comp meas_Tm)
  have hmeasG : ∀ k : Fin n, Measurable (fun u => ∑ i, m.p i (Pi.single k (Tm u))) :=
    fun k => hg.comp ((meas_single k).comp meas_Tm)
  have hrw : ∀ k : Fin n, ∫ t, ∑ i, m.p i (Pi.single k t) ∂G
      = ∫ u in Set.Icc (0:ℝ) 1, ∑ i, m.p i (Pi.single k (Tm u)) := fun k =>
    integral_G G hG _ (hg.comp (meas_single k))
  have hintP : ∀ k : Fin n, IntegrableOn (fun u => m.p k (Pi.single k (Tm u))) (Set.Icc (0:ℝ) 1) :=
    fun k => intOn_Icc _ (hmeasP k) B (fun u hu => hB _ (hcube k _ (Tm_mem u hu.2)) k)
  have hintG : ∀ k : Fin n,
      IntegrableOn (fun u => ∑ i, m.p i (Pi.single k (Tm u))) (Set.Icc (0:ℝ) 1) :=
    fun k => intOn_Icc _ (hmeasG k) (n * B) (fun u hu => hgC _ (hcube k _ (Tm_mem u hu.2)))
  have hsplit : ∀ k : Fin n, ∀ t : ℝ, ∑ i, m.p i (Pi.single k t)
      = m.p k (Pi.single k t) + ∑ i ∈ Finset.univ.erase k, m.p i (Pi.single k t) :=
    fun k t => (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
  have hzero : ∀ k : Fin n, ∀ t : ℝ, ∀ i ∈ Finset.univ.erase k,
      (Pi.single k t : Fin n → ℝ) i = 0 := by
    intro k t i hi
    simp [Pi.single_apply, Finset.ne_of_mem_erase hi]
  constructor
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro k _
    rw [hrw k]
    calc ∫ u in Set.Icc (0:ℝ) 1, ∑ i, m.p i (Pi.single k (Tm u))
        ≤ ∫ u in Set.Icc (0:ℝ) 1, m.p k (Pi.single k (Tm u)) := by
          apply setIntegral_mono_on (hintG k) (hintP k) measurableSet_Icc
          intro u hu
          rw [hsplit]
          have : ∑ i ∈ Finset.univ.erase k, m.p i (Pi.single k (Tm u)) ≤ 0 := by
            apply Finset.sum_nonpos
            intro i hi
            have := hm.ir _ (hcube k _ (Tm_mem u hu.2)) i
            rw [hzero k _ i hi] at this
            linarith
          linarith
      _ = _ := hSB k
      _ ≤ _ := by
          have := hm.ir _ (hcube k 0 ⟨le_refl _, zero_le_one⟩) k
          rw [Pi.single_eq_same] at this
          linarith
  · intro hyp
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hrw k]
    have hP0 : m.p k (Pi.single k 0) = 0 :=
      hyp k _ (hcube k 0 ⟨le_refl _, zero_le_one⟩) (Pi.single_eq_same k 0)
    calc ∫ u in Set.Icc (0:ℝ) 1, ∑ i, m.p i (Pi.single k (Tm u))
        = ∫ u in Set.Icc (0:ℝ) 1, m.p k (Pi.single k (Tm u)) := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro u hu
          simp only
          rw [hsplit]
          have : ∑ i ∈ Finset.univ.erase k, m.p i (Pi.single k (Tm u)) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            exact hyp i _ (hcube k _ (Tm_mem u hu.2)) (hzero k _ i hi)
          rw [this, add_zero]
      _ = _ := hSB k
      _ = _ := by rw [hP0, add_zero]

end RSPA3


namespace RSPA3G
open RobustSPA.AllDist RSPA3

variable {n : ℕ}

lemma meas_top : Measurable (fun v : Fin n → ℝ => top v) := by
  unfold top; exact Measurable.iSup (fun i => measurable_pi_apply i)

lemma top_mem (hn : 0 < n) {v : Fin n → ℝ} (hv : v ∈ cube n) : top v ∈ Set.Icc (0:ℝ) 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  constructor
  · exact le_trans (hv ⟨0, hn⟩ (Set.mem_univ _)).1 (le_ciSup (Finite.bddAbove_range v) _)
  · exact ciSup_le (fun i => (hv i (Set.mem_univ _)).2)

lemma top_single (hn : 0 < n) (k : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    top (Pi.single k t : Fin n → ℝ) = t := by
  haveI : Nonempty (Fin n) := ⟨k⟩
  unfold top
  apply le_antisymm
  · apply ciSup_le; intro i
    by_cases h : i = k
    · subst h; simp
    · simp [Pi.single_apply, h, ht]
  · have := le_ciSup (Finite.bddAbove_range (Pi.single k t : Fin n → ℝ)) k
    simpa using this

lemma second_single_le (k : Fin n) (t : ℝ) :
    second (Pi.single k t : Fin n → ℝ) ≤ 0 := by
  unfold second
  apply Real.iSup_le _ (le_refl _)
  rintro ⟨⟨a, b⟩, hab⟩
  by_cases ha : a = k
  · subst ha
    have : (Pi.single a t : Fin n → ℝ) b = 0 := by simp [Pi.single_apply, Ne.symm hab]
    simp only; rw [this]; exact min_le_right _ _
  · have : (Pi.single k t : Fin n → ℝ) a = 0 := by simp [Pi.single_apply, ha]
    simp only; rw [this]; exact min_le_left _ _

/-- regret bound for any DSIC mechanism under any law in `Fall` -/
lemma regret_abs_le (hn : 0 < n) (m : Mechanism n) (hm : m.IsDSIC) :
    ∃ C : ℝ, ∀ μ ∈ Fall n, |regret m μ| ≤ C := by
  obtain ⟨B, hB⟩ := hm.p_bdd
  refine ⟨1 + n * B, fun μ hμ => ?_⟩
  haveI := hμ.1
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun v => top v - ∑ i, m.p i v) (C := 1 + n * B) ?_
  · simpa [regret] using h
  · have hae : ∀ᵐ v ∂μ, v ∈ cube n :=
      ae_iff.2 (by rw [show {a | ¬ a ∈ cube n} = (cube n)ᶜ from rfl]; exact hμ.2)
    filter_upwards [hae] with v hv
    rw [Real.norm_eq_abs]
    have h1 := top_mem hn hv
    have h2 : |∑ i, m.p i v| ≤ n * B := by
      calc |∑ i, m.p i v| ≤ ∑ i, |m.p i v| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum (fun i _ => hB v hv i)
        _ = n * B := by simp
    calc |top v - ∑ i, m.p i v| ≤ |top v| + |∑ i, m.p i v| := abs_sub _ _
      _ ≤ 1 + n * B := by
        rw [abs_of_nonneg h1.1]; linarith [h1.2]

/-- `E_G[t] = 2/e` -/
lemma mean_G (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : ∀ t, cdfOf G t = isoCDF (Real.exp (-1)) t) :
    ∫ t, t ∂G = 2 * Real.exp (-1) := by
  rw [integral_G G hG (fun t => t) measurable_id]
  set c := Real.exp (-1) with hc
  have hc0 : 0 < c := Real.exp_pos _
  have hc1 : c < 1 := by
    rw [hc]; have := Real.exp_lt_exp.2 (show (-1:ℝ) < 0 by norm_num); simpa using this
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have hanti : AntitoneOn Tm (Set.uIcc 0 1) := by rw [Set.uIcc_of_le zero_le_one]; exact Tm_anti
  have hint1 : IntervalIntegrable Tm volume 0 c :=
    AntitoneOn.intervalIntegrable (Tm_anti.mono (by
      rw [Set.uIcc_of_le hc0.le]; exact Set.Icc_subset_Icc (le_refl _) hc1.le))
  have hint2 : IntervalIntegrable Tm volume c 1 :=
    AntitoneOn.intervalIntegrable (Tm_anti.mono (by
      rw [Set.uIcc_of_le hc1.le]; exact Set.Icc_subset_Icc hc0.le (le_refl _)))
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  rw [intervalIntegral.integral_congr (g := fun _ => (1:ℝ)) (a := 0) (b := c),
    intervalIntegral.integral_congr (g := fun u => c * u⁻¹) (a := c) (b := 1)]
  · rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hc0 one_pos, one_div, hc, Real.log_inv, Real.log_exp, smul_eq_mul]
    ring
  · intro u hu
    rw [Set.uIcc_of_le hc1.le] at hu
    simp only [Tm_big u hu.1, hc, div_eq_mul_inv]
  · intro u hu
    rw [Set.uIcc_of_le hc0.le] at hu
    simp only [Tm_small u hu.2]

lemma G_supp' (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : ∀ t, cdfOf G t = isoCDF (Real.exp (-1)) t) :
    ∀ᵐ t ∂G, t ∈ Set.Icc (Real.exp (-1)) 1 := by
  rw [G_eq G hG]
  refine (ae_map_iff meas_Tm.aemeasurable (p := fun t => t ∈ Set.Icc (Real.exp (-1)) 1)
    measurableSet_Icc).2 ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Filter.Eventually.of_forall (fun u hu => ⟨Tm_ge u hu.2, Tm_le_one u⟩)

theorem goal (n : ℕ) (hn : 0 < n) (ρ : ProbabilityMeasure ℝ)
    (hρ : ∀ t, cdfOf ρ t = PhiE t) (G : ProbabilityMeasure ℝ)
    (hG : ∀ t, cdfOf G t = isoCDF (Real.exp (-1)) t) :
    (∀ μ ∈ Fall n, regret (SPA (ρ : Measure ℝ)) μ
        ≤ regret (SPA (ρ : Measure ℝ)) (Fstar n (G : Measure ℝ))) ∧
    (∀ m : Mechanism n, m.IsDSIC →
        regret (SPA (ρ : Measure ℝ)) (Fstar n (G : Measure ℝ)) ≤ regret m (Fstar n (G : Measure ℝ))) ∧
    Fstar n (G : Measure ℝ) ∈ Fexc n ∧
    regret (SPA (ρ : Measure ℝ)) (Fstar n (G : Measure ℝ)) = Real.exp (-1) ∧
    minimaxRegret n (Fexc n) = Real.exp (-1) ∧
    minimaxRegret n (Fall n) = Real.exp (-1) := by
  set c := Real.exp (-1) with hc
  have hc0 : 0 < c := Real.exp_pos _
  have hG0 : (G : Measure ℝ) (Set.Icc 0 1)ᶜ = 0 := G_supp (G : Measure ℝ) hG
  have hDSIC : (SPA (n := n) (ρ : Measure ℝ)).IsDSIC := SPA_isDSIC n ρ
  have hFexc : Fstar n (G : Measure ℝ) ∈ Fexc n := Fstar_exchangeable n hn G hG0
  have hFall : Fstar n (G : Measure ℝ) ∈ Fall n := hFexc.1
  -- (4) regret of SPA at F*
  have hR4 : regret (SPA (ρ : Measure ℝ)) (Fstar n (G : Measure ℝ)) = c := by
    obtain ⟨B, hB⟩ := hDSIC.p_bdd
    have hg : Measurable (fun v : Fin n → ℝ => top v - ∑ i, (SPA (ρ : Measure ℝ)).p i v) :=
      meas_top.sub (Finset.measurable_sum _ (fun i _ => hDSIC.meas_p i))
    have hgC : ∀ v ∈ cube n, |top v - ∑ i, (SPA (n := n) (ρ : Measure ℝ)).p i v| ≤ 1 + n * B := by
      intro v hv
      have h1 := top_mem hn hv
      have h2 : |∑ i, (SPA (n := n) (ρ : Measure ℝ)).p i v| ≤ n * B := by
        calc |∑ i, (SPA (n := n) (ρ : Measure ℝ)).p i v|
            ≤ ∑ i, |(SPA (n := n) (ρ : Measure ℝ)).p i v| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum (fun i _ => hB v hv i)
          _ = n * B := by simp
      calc _ ≤ |top v| + |∑ i, (SPA (n := n) (ρ : Measure ℝ)).p i v| := abs_sub _ _
        _ ≤ 1 + n * B := by rw [abs_of_nonneg h1.1]; linarith [h1.2]
    unfold regret
    rw [integral_Fstar hn (G : Measure ℝ) hG0 _ hg _ hgC]
    have hk : ∀ k : Fin n, ∫ t, (top (Pi.single k t : Fin n → ℝ)
        - ∑ i, (SPA (ρ : Measure ℝ)).p i (Pi.single k t)) ∂(G : Measure ℝ) = c := by
      intro k
      have : ∫ t, (top (Pi.single k t : Fin n → ℝ)
          - ∑ i, (SPA (ρ : Measure ℝ)).p i (Pi.single k t)) ∂(G : Measure ℝ)
          = ∫ _t, c ∂(G : Measure ℝ) := by
        apply integral_congr_ae
        filter_upwards [G_supp' (G : Measure ℝ) hG] with t ht
        have hcube : (Pi.single k t : Fin n → ℝ) ∈ cube n :=
          (single_mem_cube_iff k t).2 ⟨hc0.le.trans ht.1, ht.2⟩
        have hpw := pointwise_regret_le_inv_e n hn ρ hρ _ hcube
        exact hpw.2.1 ((second_single_le k t).trans hc0.le)
          (by rw [top_single hn k t (hc0.le.trans ht.1)]; exact ht.1)
      rw [this, integral_const, smul_eq_mul, probReal_univ, one_mul]
    simp_rw [hk]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- (1) SPA regret ≤ c for every law in Fall
  have hR1 : ∀ μ ∈ Fall n, regret (SPA (ρ : Measure ℝ)) μ ≤ c := by
    intro μ hμ
    haveI := hμ.1
    unfold regret
    by_cases hint : Integrable (fun v => top v - ∑ i, (SPA (ρ : Measure ℝ)).p i v) μ
    · have hae : ∀ᵐ v ∂μ, v ∈ cube n :=
        ae_iff.2 (by rw [show {a | ¬ a ∈ cube n} = (cube n)ᶜ from rfl]; exact hμ.2)
      calc ∫ v, (top v - ∑ i, (SPA (ρ : Measure ℝ)).p i v) ∂μ ≤ ∫ _v, c ∂μ := by
            apply integral_mono_ae hint (integrable_const c)
            filter_upwards [hae] with v hv
            exact (pointwise_regret_le_inv_e n hn ρ hρ v hv).1
        _ = c := by rw [integral_const, smul_eq_mul, probReal_univ, one_mul]
    · rw [integral_undef hint]; exact hc0.le
  -- (2) lower bound for every DSIC mechanism at F*
  have hR2 : ∀ m : Mechanism n, m.IsDSIC → c ≤ regret m (Fstar n (G : Measure ℝ)) := by
    intro m hm
    obtain ⟨B, hB⟩ := hm.p_bdd
    have hgP : Measurable (fun v : Fin n → ℝ => ∑ i, m.p i v) :=
      Finset.measurable_sum _ (fun i _ => hm.meas_p i)
    have hgPC : ∀ v ∈ cube n, |∑ i, m.p i v| ≤ n * B := by
      intro v hv
      calc |∑ i, m.p i v| ≤ ∑ i, |m.p i v| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum (fun i _ => hB v hv i)
        _ = n * B := by simp
    have htC : ∀ v ∈ cube n, |top v| ≤ 1 := by
      intro v hv; have := top_mem hn hv; rw [abs_le]; constructor <;> linarith [this.1, this.2]
    haveI : IsProbabilityMeasure (Fstar n (G : Measure ℝ)) := hFall.1
    have haeF : ∀ᵐ v ∂(Fstar n (G : Measure ℝ)), v ∈ cube n :=
      ae_iff.2 (by rw [show {a | ¬ a ∈ cube n} = (cube n)ᶜ from rfl]; exact hFall.2)
    have hintT : Integrable (fun v : Fin n → ℝ => top v) (Fstar n (G : Measure ℝ)) :=
      Integrable.of_bound meas_top.aestronglyMeasurable 1
        (by filter_upwards [haeF] with v hv; rw [Real.norm_eq_abs]; exact htC v hv)
    have hintP : Integrable (fun v : Fin n → ℝ => ∑ i, m.p i v) (Fstar n (G : Measure ℝ)) :=
      Integrable.of_bound hgP.aestronglyMeasurable (n * B)
        (by filter_upwards [haeF] with v hv; rw [Real.norm_eq_abs]; exact hgPC v hv)
    unfold regret
    rw [integral_sub hintT hintP]
    -- expected top
    have hTop : ∫ v, top v ∂(Fstar n (G : Measure ℝ)) = 2 * c := by
      rw [integral_Fstar hn (G : Measure ℝ) hG0 _ meas_top 1 htC]
      have hk : ∀ k : Fin n, ∫ t, top (Pi.single k t : Fin n → ℝ) ∂(G : Measure ℝ) = 2 * c := by
        intro k
        rw [← mean_G (G : Measure ℝ) hG]
        apply integral_congr_ae
        filter_upwards [G_supp' (G : Measure ℝ) hG] with t ht
        exact top_single hn k t (hc0.le.trans ht.1)
      simp_rw [hk]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    -- expected revenue
    have hRev := (revenue_under_Fstar n hn G hG m hm).1
    have hRHS : (1 / (n : ℝ)) * ∑ k : Fin n, (Real.exp (-1) * m.x k (Pi.single k 1)
            - ∫ t in (0 : ℝ)..(Real.exp (-1)), m.x k (Pi.single k t)) ≤ c := by
      have hle : ∀ k : Fin n, Real.exp (-1) * m.x k (Pi.single k 1)
          - ∫ t in (0 : ℝ)..(Real.exp (-1)), m.x k (Pi.single k t) ≤ c := by
        intro k
        have hx1 := (hm.x_mem _ ((single_mem_cube_iff k 1).2 ⟨zero_le_one, le_refl _⟩) k).2
        have hint0 : 0 ≤ ∫ t in (0 : ℝ)..(Real.exp (-1)), m.x k (Pi.single k t) := by
          apply intervalIntegral.integral_nonneg hc0.le
          intro t ht
          have hc1 : c ≤ 1 := by
            rw [hc]; have := Real.exp_le_exp.2 (show (-1:ℝ) ≤ 0 by norm_num); simpa using this
          exact (hm.x_mem _ ((single_mem_cube_iff k t).2 ⟨ht.1, ht.2.trans hc1⟩) k).1
        have : Real.exp (-1) * m.x k (Pi.single k 1) ≤ c := by
          rw [← hc]; nlinarith
        linarith
      calc (1 / (n : ℝ)) * ∑ k : Fin n, (Real.exp (-1) * m.x k (Pi.single k 1)
            - ∫ t in (0 : ℝ)..(Real.exp (-1)), m.x k (Pi.single k t))
          ≤ (1 / (n : ℝ)) * ∑ _k : Fin n, c :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hle k)) (by positivity)
        _ = c := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            have : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
            field_simp
    rw [hTop]
    linarith
  -- bounded suprema
  have hsupB : ∀ (m : {m : Mechanism n // m.IsDSIC}) (𝓕 : Set (Measure (Fin n → ℝ))),
      𝓕 ⊆ Fall n → BddAbove (Set.range fun μ : 𝓕 => regret m.1 μ) := by
    intro m 𝓕 h𝓕
    obtain ⟨C, hC⟩ := regret_abs_le hn m.1 m.2
    exact ⟨C, by rintro _ ⟨μ, rfl⟩; exact (le_abs_self _).trans (hC μ (h𝓕 μ.2))⟩
  have hmm : ∀ 𝓕 : Set (Measure (Fin n → ℝ)), 𝓕 ⊆ Fall n →
      Fstar n (G : Measure ℝ) ∈ 𝓕 → minimaxRegret n 𝓕 = c := by
    intro 𝓕 h𝓕 hF
    haveI : Nonempty 𝓕 := ⟨⟨_, hF⟩⟩
    have hlow : ∀ m : {m : Mechanism n // m.IsDSIC}, c ≤ ⨆ μ : 𝓕, regret m.1 μ := by
      intro m
      exact (hR2 m.1 m.2).trans (le_ciSup (hsupB m 𝓕 h𝓕) ⟨_, hF⟩)
    haveI : Nonempty {m : Mechanism n // m.IsDSIC} := ⟨⟨_, hDSIC⟩⟩
    apply le_antisymm
    · refine (ciInf_le ⟨c, by rintro _ ⟨m, rfl⟩; exact hlow m⟩ ⟨_, hDSIC⟩).trans ?_
      exact ciSup_le (fun μ => hR1 μ.1 (h𝓕 μ.2))
    · exact le_ciInf hlow
  refine ⟨fun μ hμ => hR4 ▸ hR1 μ hμ, fun m hm => hR4 ▸ hR2 m hm, hFexc, hR4, ?_, ?_⟩
  · exact hmm (Fexc n) (fun μ hμ => hμ.1) hFexc
  · exact hmm (Fall n) (fun μ hμ => hμ) hFall

end RSPA3G


open RobustSPA.AllDist in
theorem solution (n : ℕ) (hn : 0 < n) (ρ : ProbabilityMeasure ℝ)
    (hρ : ∀ t, cdfOf ρ t = PhiE t) (G : ProbabilityMeasure ℝ)
    (hG : ∀ t, cdfOf G t = isoCDF (Real.exp (-1)) t) :
    (∀ μ ∈ Fall n, regret (SPA (ρ : Measure ℝ)) μ
        ≤ regret (SPA (ρ : Measure ℝ)) (Fstar n (G : Measure ℝ))) ∧
    (∀ m : Mechanism n, m.IsDSIC →
        regret (SPA (ρ : Measure ℝ)) (Fstar n (G : Measure ℝ)) ≤ regret m (Fstar n (G : Measure ℝ))) ∧
    Fstar n (G : Measure ℝ) ∈ Fexc n ∧
    regret (SPA (ρ : Measure ℝ)) (Fstar n (G : Measure ℝ)) = Real.exp (-1) ∧
    minimaxRegret n (Fexc n) = Real.exp (-1) ∧
    minimaxRegret n (Fall n) = Real.exp (-1) :=
  RSPA3G.goal n hn ρ hρ G hG
