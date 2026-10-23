-- Prove2me | solution 1 for StoneRegression.Quantile.proposition_15
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:05:56.246284+00:00
-- url     : https://prove2.me/submissions/0225e39a-e7d1-4c1e-887b-6d28192b7940

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting
import Definitions.Def_StoneRegression_Quantile_Quantiles



namespace StoneRegression.Quantile

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

lemma q14_ici (ν : Measure ℝ) [IsProbabilityMeasure ν] (a p : ℝ) (hp : 0 ≤ p)
    (h : ∀ t < a, ν (Iic t) ≤ ENNReal.ofReal p) : ENNReal.ofReal (1 - p) ≤ ν (Ici a) := by
  have hU : (⋃ n : ℕ, Iic (a - 1 / ((n:ℝ) + 1))) = Iio a := by
    ext y; simp only [mem_iUnion, mem_Iic, mem_Iio]
    constructor
    · rintro ⟨n, hn⟩; have : (0:ℝ) < 1 / ((n:ℝ)+1) := by positivity
      linarith
    · intro hy
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
      exact ⟨n, by linarith⟩
  have hmono : Monotone (fun n : ℕ => Iic (a - 1 / ((n:ℝ) + 1))) := by
    intro m n hmn; apply Iic_subset_Iic.2
    have : 1 / ((n:ℝ)+1) ≤ 1 / ((m:ℝ)+1) := by
      apply one_div_le_one_div_of_le (by positivity); exact_mod_cast Nat.add_le_add_right hmn 1
    linarith
  have h1 : ν (Iio a) ≤ ENNReal.ofReal p := by
    rw [← hU, hmono.measure_iUnion]
    exact iSup_le fun n => h _ (by have : (0:ℝ) < 1 / ((n:ℝ)+1) := by positivity
                                   linarith)
  have h2 : ν (Ici a) = 1 - ν (Iio a) := by
    rw [← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio]
  rw [h2, ENNReal.ofReal_sub _ hp, ENNReal.ofReal_one]
  exact tsub_le_tsub_left h1 _

lemma q14_iic (ν : Measure ℝ) [IsProbabilityMeasure ν] (a p : ℝ)
    (h : ∀ t, a < t → ENNReal.ofReal p ≤ ν (Iic t)) : ENNReal.ofReal p ≤ ν (Iic a) := by
  have hU : (⋂ n : ℕ, Iic (a + 1 / ((n:ℝ) + 1))) = Iic a := by
    ext y; simp only [mem_iInter, mem_Iic]
    constructor
    · intro hy
      by_contra hc; push_neg at hc
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hc)
      have := hy n; linarith
    · intro hy n; have : (0:ℝ) < 1 / ((n:ℝ)+1) := by positivity
      linarith
  have hanti : Antitone (fun n : ℕ => Iic (a + 1 / ((n:ℝ) + 1))) := by
    intro m n hmn; apply Iic_subset_Iic.2
    have : 1 / ((n:ℝ)+1) ≤ 1 / ((m:ℝ)+1) := by
      apply one_div_le_one_div_of_le (by positivity); exact_mod_cast Nat.add_le_add_right hmn 1
    linarith
  rw [← hU, hanti.measure_iInter (fun _ => measurableSet_Iic.nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩]
  exact le_iInf fun n => h _ (by have : (0:ℝ) < 1 / ((n:ℝ)+1) := by positivity
                                 linarith)

/-- lower quantile of a probability measure: mass of `{|y| ≥ |L|}` is at least `min p (1-p)`. -/
lemma q14_lower (ν : Measure ℝ) [IsProbabilityMeasure ν] (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    sInf {y : ℝ | p ≤ (ν (Iic y)).toReal} = 0 ∨
    ENNReal.ofReal (min p (1 - p)) ≤
      ν {y | |sInf {y : ℝ | p ≤ (ν (Iic y)).toReal}| ≤ |y|} := by
  set S := {y : ℝ | p ≤ (ν (Iic y)).toReal} with hS
  by_cases hL : sInf S = 0
  · exact Or.inl hL
  right
  have hne : S.Nonempty := by
    by_contra h; rw [Set.not_nonempty_iff_eq_empty] at h; rw [h, Real.sInf_empty] at hL; exact hL rfl
  have hbdd : BddBelow S := by
    by_contra h; exact hL (Real.sInf_of_not_bddBelow h)
  rcases lt_or_gt_of_ne hL with hneg | hpos
  · -- L < 0
    have key : ENNReal.ofReal p ≤ ν (Iic (sInf S)) := by
      apply q14_iic
      intro t ht
      obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt hne ht
      have hs' : p ≤ (ν (Iic s)).toReal := hs
      calc ENNReal.ofReal p ≤ ν (Iic s) := ENNReal.ofReal_le_of_le_toReal hs'
        _ ≤ ν (Iic t) := measure_mono (Iic_subset_Iic.2 hst.le)
    refine le_trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)) (key.trans (measure_mono ?_))
    intro y hy; simp only [mem_Iic] at hy; simp only [mem_setOf_eq]
    rw [abs_of_neg hneg, abs_of_neg (lt_of_le_of_lt hy hneg)]; linarith
  · have key : ENNReal.ofReal (1 - p) ≤ ν (Ici (sInf S)) := by
      apply q14_ici _ _ _ hp0.le
      intro t ht
      have : t ∉ S := fun hts => absurd (csInf_le hbdd hts) (not_le.2 ht)
      simp only [hS, mem_setOf_eq, not_le] at this
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hp0.le).2 this.le
    refine le_trans (ENNReal.ofReal_le_ofReal (min_le_right _ _)) (key.trans (measure_mono ?_))
    intro y hy; simp only [mem_Ici] at hy; simp only [mem_setOf_eq]
    rw [abs_of_pos hpos, abs_of_pos (lt_of_lt_of_le hpos hy)]; exact hy

lemma q14_upper (ν : Measure ℝ) [IsProbabilityMeasure ν] (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    sSup {y : ℝ | (ν (Iic y)).toReal ≤ p} = 0 ∨
    ENNReal.ofReal (min p (1 - p)) ≤
      ν {y | |sSup {y : ℝ | (ν (Iic y)).toReal ≤ p}| ≤ |y|} := by
  set S := {y : ℝ | (ν (Iic y)).toReal ≤ p} with hS
  by_cases hL : sSup S = 0
  · exact Or.inl hL
  right
  have hne : S.Nonempty := by
    by_contra h; rw [Set.not_nonempty_iff_eq_empty] at h; rw [h, Real.sSup_empty] at hL; exact hL rfl
  have hbdd : BddAbove S := by
    by_contra h; exact hL (Real.sSup_of_not_bddAbove h)
  rcases lt_or_gt_of_ne hL with hneg | hpos
  · have key : ENNReal.ofReal p ≤ ν (Iic (sSup S)) := by
      apply q14_iic
      intro t ht
      have : t ∉ S := fun hts => absurd (le_csSup hbdd hts) (not_le.2 ht)
      simp only [hS, mem_setOf_eq, not_le] at this
      exact ENNReal.ofReal_le_of_le_toReal this.le
    refine le_trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)) (key.trans (measure_mono ?_))
    intro y hy; simp only [mem_Iic] at hy; simp only [mem_setOf_eq]
    rw [abs_of_neg hneg, abs_of_neg (lt_of_le_of_lt hy hneg)]; linarith
  · have key : ENNReal.ofReal (1 - p) ≤ ν (Ici (sSup S)) := by
      apply q14_ici _ _ _ hp0.le
      intro t ht
      obtain ⟨s, hs, hst⟩ := exists_lt_of_lt_csSup hne ht
      have hs' : (ν (Iic s)).toReal ≤ p := hs
      calc ν (Iic t) ≤ ν (Iic s) := measure_mono (Iic_subset_Iic.2 hst.le)
        _ ≤ ENNReal.ofReal p := (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hp0.le).2 hs'
    refine le_trans (ENNReal.ofReal_le_ofReal (min_le_right _ _)) (key.trans (measure_mono ?_))
    intro y hy; simp only [mem_Ici] at hy; simp only [mem_setOf_eq]
    rw [abs_of_pos hpos, abs_of_pos (lt_of_lt_of_le hpos hy)]; exact hy

/-- Chebyshev step: if `c ≤ ν {|a| ≤ |y|}` and `g ≥ G` on that set, then `G * c ≤ ∫ g`. -/
lemma q14_cheb (ν : Measure ℝ) (a : ℝ) (c G : ℝ≥0∞) (g : ℝ → ℝ≥0∞)
    (hc : c ≤ ν {y | |a| ≤ |y|}) (hg : ∀ y, |a| ≤ |y| → G ≤ g y) :
    G * c ≤ ∫⁻ y, g y ∂ν := by
  have hms : MeasurableSet {y : ℝ | |a| ≤ |y|} := measurableSet_le measurable_const measurable_abs
  calc G * c ≤ G * ν {y | |a| ≤ |y|} := by gcongr
    _ = ∫⁻ y, ({y : ℝ | |a| ≤ |y|}.indicator (fun _ => G)) y ∂ν := by
        rw [lintegral_indicator_const hms]
    _ ≤ ∫⁻ y, g y ∂ν := by
        apply lintegral_mono; intro y
        by_cases hy : y ∈ {y : ℝ | |a| ≤ |y|}
        · rw [indicator_of_mem hy]; exact hg y hy
        · rw [indicator_of_notMem hy]; exact zero_le'


lemma upd_mp {X : Type*} [MeasurableSpace X] (μ : ℕ → Measure X) [∀ k, IsProbabilityMeasure (μ k)]
    (j : ℕ) :
    MeasurePreserving (fun q : (ℕ → X) × X => Function.update q.1 j q.2)
      ((Measure.infinitePi μ).prod (μ j)) (Measure.infinitePi μ) where
  measurable := by fun_prop
  map_eq := by
    apply Measure.eq_infinitePi
    intro s t ht
    classical
    rw [Measure.map_apply (by fun_prop) (.pi s.countable_toSet (fun i _ => ht i))]
    by_cases hj : j ∈ s
    · have hpre : (fun q : (ℕ → X) × X => Function.update q.1 j q.2) ⁻¹' (Set.pi (↑s) t) =
          (Set.pi ↑(s.erase j) t) ×ˢ t j := by
        ext ⟨x, a⟩
        simp only [mem_preimage, Set.mem_pi, Finset.mem_coe, mem_prod, Finset.mem_erase]
        constructor
        · intro h
          refine ⟨fun i ⟨hij, his⟩ => ?_, ?_⟩
          · have := h i his; rwa [Function.update_of_ne hij] at this
          · have := h j hj; rwa [Function.update_self] at this
        · rintro ⟨h1, h2⟩ i his
          by_cases hij : i = j
          · subst hij; rwa [Function.update_self]
          · rw [Function.update_of_ne hij]; exact h1 i ⟨hij, his⟩
      rw [hpre, Measure.prod_prod, Measure.infinitePi_pi _ (fun i _ => ht i),
        ← Finset.prod_erase_mul _ _ hj]
    · have hpre : (fun q : (ℕ → X) × X => Function.update q.1 j q.2) ⁻¹' (Set.pi (↑s) t) =
          (Set.pi ↑s t) ×ˢ univ := by
        ext ⟨x, a⟩
        simp only [mem_preimage, Set.mem_pi, Finset.mem_coe, mem_prod, mem_univ, and_true]
        constructor
        · intro h i his
          have := h i his
          rwa [Function.update_of_ne (fun e : i = j => hj (e ▸ his))] at this
        · intro h i his
          rw [Function.update_of_ne (fun e : i = j => hj (e ▸ his))]; exact h i his
      rw [hpre, Measure.prod_prod, Measure.infinitePi_pi _ (fun i _ => ht i), measure_univ, mul_one]

lemma disint {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel X ℝ) [IsMarkovKernel κ] (j : ℕ) (w : (ℕ → X) → ℝ≥0∞) (hw : Measurable w)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ ω, w (fun k => (ω k).1) * g ((ω j).2) ∂(Measure.infinitePi (fun _ : ℕ => μ ⊗ₘ κ)) =
      ∫⁻ xs, w xs * (∫⁻ y, g y ∂κ (xs j)) ∂(Measure.infinitePi (fun _ : ℕ => μ)) := by
  have hf : Measurable (fun x => ∫⁻ y, g y ∂κ x) := hg.lintegral_kernel
  set H : (ℕ → X) → ℝ≥0∞ := fun xs => ∫⁻ x, w (Function.update xs j x) * ∫⁻ y, g y ∂κ x ∂μ
    with hHdef
  have hHm : Measurable H := by
    exact Measurable.lintegral_prod_right'
      (f := fun q : (ℕ → X) × X => w (Function.update q.1 j q.2) * ∫⁻ y, g y ∂κ q.2)
      ((hw.comp (by fun_prop)).mul (hf.comp measurable_snd))
  have hG : Measurable (fun ω : ℕ → X × ℝ => w (fun k => (ω k).1) * g ((ω j).2)) := by
    apply Measurable.mul
    · exact hw.comp (by fun_prop)
    · exact hg.comp (by fun_prop)
  have hL : ∫⁻ ω, w (fun k => (ω k).1) * g ((ω j).2) ∂(Measure.infinitePi (fun _ : ℕ => μ ⊗ₘ κ)) =
      ∫⁻ ω, H (fun k => (ω k).1) ∂(Measure.infinitePi (fun _ : ℕ => μ ⊗ₘ κ)) := by
    rw [← (upd_mp (fun _ : ℕ => μ ⊗ₘ κ) j).lintegral_comp hG, lintegral_prod]
    swap; · exact (hG.comp (upd_mp (fun _ : ℕ => μ ⊗ₘ κ) j).measurable).aemeasurable
    apply lintegral_congr; intro ω
    simp only [Function.comp, hHdef]
    have e1 : ∀ a : X × ℝ, (fun k => (Function.update ω j a k).1) =
        Function.update (fun k => (ω k).1) j a.1 := by
      intro a; funext k
      by_cases hk : k = j
      · subst hk; simp
      · simp [Function.update_of_ne hk]
    simp only [e1, Function.update_self]
    rw [Measure.lintegral_compProd]
    · apply lintegral_congr; intro x
      dsimp only; exact lintegral_const_mul _ hg
    · exact (hw.comp (by fun_prop)).mul (hg.comp measurable_snd)
  have hR : ∫⁻ xs, w xs * (∫⁻ y, g y ∂κ (xs j)) ∂(Measure.infinitePi (fun _ : ℕ => μ)) =
      ∫⁻ xs, H xs ∂(Measure.infinitePi (fun _ : ℕ => μ)) := by
    have hm : Measurable (fun xs : ℕ → X => w xs * (∫⁻ y, g y ∂κ (xs j))) :=
      hw.mul (hf.comp (measurable_pi_apply j))
    rw [← (upd_mp (fun _ : ℕ => μ) j).lintegral_comp hm, lintegral_prod]
    swap; · exact (hm.comp (upd_mp (fun _ : ℕ => μ) j).measurable).aemeasurable
    apply lintegral_congr; intro xs
    simp only [Function.comp, hHdef, Function.update_self]
  rw [hL, hR]
  have hmap : (Measure.infinitePi (fun _ : ℕ => μ ⊗ₘ κ)).map (fun ω k => (ω k).1) =
      Measure.infinitePi (fun _ : ℕ => μ) := by
    rw [Measure.infinitePi_map_pi _ (fun _ => measurable_fst)]
    congr 1; funext k
    exact Measure.fst_compProd μ κ
  rw [← hmap, lintegral_map hHm (by fun_prop)]

/-- empirical weighted measure -/
noncomputable def empM {d : ℕ} (W : StoneRegression.Criterion.WeightSeq d) (n : ℕ)
    (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ) : Measure ℝ :=
  ∑ i : Fin n, ENNReal.ofReal (W n (ω 0).1 (fun j => (ω (j.val + 1)).1) i) •
    Measure.dirac ((ω (i.val + 1)).2)

lemma empM_apply {d : ℕ} (W : StoneRegression.Criterion.WeightSeq d) (n : ℕ)
    (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    empM W n ω s = ∑ i : Fin n, ENNReal.ofReal (W n (ω 0).1 (fun j => (ω (j.val + 1)).1) i) *
      s.indicator 1 ((ω (i.val + 1)).2) := by
  simp only [empM, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs]

lemma empM_prob {d : ℕ} (W : StoneRegression.Criterion.WeightSeq d) (n : ℕ)
    (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ)
    (hPn : (∀ i, 0 ≤ W n (ω 0).1 (fun j => (ω (j.val + 1)).1) i) ∧
      ∑ i, W n (ω 0).1 (fun j => (ω (j.val + 1)).1) i = 1) :
    IsProbabilityMeasure (empM W n ω) := by
  constructor
  rw [empM_apply _ _ _ _ MeasurableSet.univ]
  simp only [indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hPn.1 i), hPn.2, ENNReal.ofReal_one]

lemma empM_cdf {d : ℕ} (W : StoneRegression.Criterion.WeightSeq d) (n : ℕ)
    (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ)
    (hP0 : ∀ i, 0 ≤ W n (ω 0).1 (fun j => (ω (j.val + 1)).1) i) (y : ℝ) :
    (empM W n ω (Iic y)).toReal = estCdf W n ω y := by
  rw [empM_apply _ _ _ _ measurableSet_Iic, ENNReal.toReal_sum]
  · unfold estCdf
    apply Finset.sum_congr rfl; intro i _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hP0 i)]
    congr 1
    by_cases h : (ω (i.val + 1)).2 ≤ y
    · rw [if_pos h, indicator_of_mem (by simpa using h)]; simp
    · rw [if_neg h, indicator_of_notMem (by simpa using h)]; simp
  · intro i _
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    by_cases h : (ω (i.val + 1)).2 ∈ Iic y
    · rw [indicator_of_mem h]; simp
    · rw [indicator_of_notMem h]; simp

lemma empM_lintegral {d : ℕ} (W : StoneRegression.Criterion.WeightSeq d) (n : ℕ)
    (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ y, g y ∂(empM W n ω) = ∑ i : Fin n,
      ENNReal.ofReal (W n (ω 0).1 (fun j => (ω (j.val + 1)).1) i) * g ((ω (i.val + 1)).2) := by
  simp only [empM, lintegral_finset_sum_measure, lintegral_smul_measure, lintegral_dirac,
    smul_eq_mul]

/-- truncated power -/
noncomputable def Gt (M r : ℝ) (z : ℝ) : ℝ≥0∞ := ‖z‖ₑ ^ r * (if M ≤ |z| then 1 else 0)

lemma Gt_meas (M r : ℝ) : Measurable (Gt M r) := by
  unfold Gt
  apply Measurable.mul
  · exact measurable_id.enorm.pow_const r
  · exact Measurable.ite (measurableSet_le measurable_const measurable_abs) measurable_const
      measurable_const

lemma q15_point (ν : Measure ℝ) (Q : ℝ) (c : ℝ≥0∞) (M r : ℝ) (hM : 0 < M) (hr : 1 ≤ r)
    (h : Q = 0 ∨ c ≤ ν {y | |Q| ≤ |y|}) :
    Gt M r Q * c ≤ ∫⁻ y, Gt M r y ∂ν := by
  rcases h with h | h
  · rw [h]; simp [Gt, not_le.2 hM]
  · apply q14_cheb ν Q c _ _ h
    intro y hy
    unfold Gt
    by_cases hQ : M ≤ |Q|
    · rw [if_pos hQ, if_pos (hQ.trans hy), mul_one, mul_one,
        Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hy) (by linarith)
    · rw [if_neg hQ, mul_zero]; exact zero_le'

lemma q15_main {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : StoneRegression.Criterion.WeightSeq d) (n : ℕ)
    (hWn : Measurable
      (fun q : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) => W n q.1 q.2))
    (hPn : ∀ x xs, (∀ i, 0 ≤ W n x xs i) ∧ ∑ i, W n x xs i = 1)
    (C : ℝ≥0) (hC : 1 ≤ C)
    (h1 : ∀ f : EuclideanSpace ℝ (Fin d) → ℝ≥0, Measurable f →
      ∫⁻ ω, ∑ i : Fin n, ‖StoneRegression.Criterion.wAt W n ω i‖ₑ * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(StoneRegression.Criterion.xLaw μ) ≤ C * ∫⁻ x, f x ∂μ)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤) (M : ℝ) (hM : 0 < M) (r : ℝ) (hr : 1 ≤ r)
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ]
    (Q : (ℕ → EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
    (hQ : ∀ ω, Q ω = 0 ∨ c ≤ empM W n ω {y | |Q ω| ≤ |y|}) :
    ∫⁻ ω, Gt M r (Q ω) ∂(StoneRegression.Criterion.pairLaw μ κ) ≤
      ((C : ℝ≥0∞) / c) * ∫⁻ q, Gt M r q.2 ∂(μ ⊗ₘ κ) := by
  set f : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun x => ∫⁻ y, Gt M r y ∂κ x with hfdef
  have hf : Measurable f := (Gt_meas M r).lintegral_kernel
  have hwm : ∀ i : Fin n, Measurable
      (fun xs : ℕ → EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (W n (xs 0) (fun j => xs (j.val + 1)) i)) := by
    intro i
    have hm2 : Measurable (fun xs : ℕ → EuclideanSpace ℝ (Fin d) =>
        ((xs 0), (fun j : Fin n => xs (j.val + 1)))) :=
      Measurable.prodMk (measurable_pi_apply 0) (measurable_pi_lambda _ (fun j => measurable_pi_apply _))
    have h3 : Measurable (fun xs : ℕ → EuclideanSpace ℝ (Fin d) =>
        W n (xs 0) (fun j => xs (j.val + 1))) := hWn.comp hm2
    exact ENNReal.measurable_ofReal.comp ((measurable_pi_apply i).comp h3)
  have step1 : ∀ ω, Gt M r (Q ω) ≤ (∑ i : Fin n, ENNReal.ofReal (W n (ω 0).1 (fun j => (ω (j.val + 1)).1) i) *
      Gt M r ((ω (i.val + 1)).2)) / c := by
    intro ω
    rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct), ← empM_lintegral]
    exact q15_point _ _ _ _ _ hM hr (hQ ω)
  have key : ∫⁻ ω, (∑ i : Fin n, ENNReal.ofReal (W n (ω 0).1 (fun j => (ω (j.val + 1)).1) i) *
      Gt M r ((ω (i.val + 1)).2)) ∂(StoneRegression.Criterion.pairLaw μ κ) ≤ C * ∫⁻ x, f x ∂μ := by
    rw [lintegral_finsetSum]
    swap
    · intro i _
      apply Measurable.mul
      · exact (hwm i).comp (measurable_pi_lambda _ (fun k => measurable_fst.comp (measurable_pi_apply k)))
      · exact (Gt_meas M r).comp (measurable_snd.comp (measurable_pi_apply _))
    have hd : ∀ i : Fin n, ∫⁻ ω, ENNReal.ofReal (W n (ω 0).1 (fun j => (ω (j.val + 1)).1) i) *
        Gt M r ((ω (i.val + 1)).2) ∂(StoneRegression.Criterion.pairLaw μ κ) =
        ∫⁻ xs, ENNReal.ofReal (W n (xs 0) (fun j => xs (j.val + 1)) i) * f (xs (i.val + 1))
          ∂(StoneRegression.Criterion.xLaw μ) := fun i =>
      disint μ κ (i.val + 1) _ (hwm i) (Gt M r) (Gt_meas M r)
    rw [Finset.sum_congr rfl (fun i _ => hd i), ← lintegral_finsetSum]
    swap
    · intro i _
      exact (hwm i).mul (hf.comp (measurable_pi_apply _))
    by_cases hfin : ∫⁻ x, f x ∂μ = ∞
    · rw [hfin, ENNReal.mul_top (by
        have : (1 : ℝ≥0∞) ≤ C := by exact_mod_cast hC
        exact (lt_of_lt_of_le one_pos this).ne')]
      exact le_top
    have hae : ∀ᵐ x ∂μ, f x < ∞ := ae_lt_top hf hfin
    have hae2 : ∀ᵐ xs ∂(StoneRegression.Criterion.xLaw μ), ∀ i : Fin n, f (xs (i.val + 1)) < ∞ := by
      rw [ae_all_iff]; intro i
      have hmap := Measure.infinitePi_map_eval (fun _ : ℕ => μ) (i.val + 1)
      refine ae_of_ae_map (μ := StoneRegression.Criterion.xLaw μ)
        (f := fun xs : ℕ → EuclideanSpace ℝ (Fin d) => xs (i.val + 1)) (p := fun y => f y < ∞)
        (measurable_pi_apply _).aemeasurable ?_
      unfold StoneRegression.Criterion.xLaw
      rw [hmap]; exact hae
    calc ∫⁻ xs, ∑ i : Fin n, ENNReal.ofReal (W n (xs 0) (fun j => xs (j.val + 1)) i) * f (xs (i.val + 1))
          ∂(StoneRegression.Criterion.xLaw μ)
        = ∫⁻ xs, ∑ i : Fin n, ‖StoneRegression.Criterion.wAt W n xs i‖ₑ *
            (((fun x => (f x).toNNReal) (xs (i.val + 1)) : ℝ≥0) : ℝ≥0∞)
          ∂(StoneRegression.Criterion.xLaw μ) := by
          apply lintegral_congr_ae
          filter_upwards [hae2] with xs hxs
          apply Finset.sum_congr rfl; intro i _
          rw [ENNReal.coe_toNNReal (hxs i).ne, Real.enorm_eq_ofReal_abs,
            abs_of_nonneg (show 0 ≤ StoneRegression.Criterion.wAt W n xs i from (hPn _ _).1 i)]
          rfl
      _ ≤ C * ∫⁻ x, (((fun x => (f x).toNNReal) x : ℝ≥0) : ℝ≥0∞) ∂μ := h1 _ hf.ennreal_toNNReal
      _ ≤ C * ∫⁻ x, f x ∂μ := by
          gcongr with x; exact ENNReal.coe_toNNReal_le_self
  calc ∫⁻ ω, Gt M r (Q ω) ∂(StoneRegression.Criterion.pairLaw μ κ)
      ≤ ∫⁻ ω, (∑ i : Fin n, ENNReal.ofReal (W n (ω 0).1 (fun j => (ω (j.val + 1)).1) i) *
          Gt M r ((ω (i.val + 1)).2)) / c ∂(StoneRegression.Criterion.pairLaw μ κ) := lintegral_mono step1
    _ = (∫⁻ ω, (∑ i : Fin n, ENNReal.ofReal (W n (ω 0).1 (fun j => (ω (j.val + 1)).1) i) *
          Gt M r ((ω (i.val + 1)).2)) ∂(StoneRegression.Criterion.pairLaw μ κ)) / c := by
        simp only [div_eq_mul_inv]
        rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hc0)]
    _ ≤ (C * ∫⁻ x, f x ∂μ) / c := by gcongr
    _ = ((C : ℝ≥0∞) / c) * ∫⁻ q, Gt M r q.2 ∂(μ ⊗ₘ κ) := by
        rw [Measure.lintegral_compProd (f := fun q => Gt M r q.2) ((Gt_meas M r).comp measurable_snd)]
        simp only [hfdef, div_eq_mul_inv]
        ring

theorem proposition_15_core {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : StoneRegression.Criterion.WeightSeq d) (n : ℕ) (hn : 1 ≤ n)
    (hWn : Measurable
      (fun q : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) => W n q.1 q.2))
    (hPn : ∀ x xs, (∀ i, 0 ≤ W n x xs i) ∧ ∑ i, W n x xs i = 1)
    (C : ℝ≥0) (hC : 1 ≤ C)
    (h1 : ∀ f : EuclideanSpace ℝ (Fin d) → ℝ≥0, Measurable f →
      ∫⁻ ω, ∑ i : Fin n, ‖StoneRegression.Criterion.wAt W n ω i‖ₑ * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(StoneRegression.Criterion.xLaw μ) ≤ C * ∫⁻ x, f x ∂μ)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (M : ℝ) (hM : 0 < M) (r : ℝ) (hr : 1 ≤ r)
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ] :
    ∫⁻ ω, ‖estLowerQ W n p ω‖ₑ ^ r * (if M ≤ |estLowerQ W n p ω| then 1 else 0) ∂(StoneRegression.Criterion.pairLaw μ κ) ≤
        ((C : ℝ≥0∞) / ENNReal.ofReal (min p (1 - p))) *
          ∫⁻ q, ‖q.2‖ₑ ^ r * (if M ≤ |q.2| then 1 else 0) ∂(μ ⊗ₘ κ) ∧
    ∫⁻ ω, ‖estUpperQ W n p ω‖ₑ ^ r * (if M ≤ |estUpperQ W n p ω| then 1 else 0) ∂(StoneRegression.Criterion.pairLaw μ κ) ≤
        ((C : ℝ≥0∞) / ENNReal.ofReal (min p (1 - p))) *
          ∫⁻ q, ‖q.2‖ₑ ^ r * (if M ≤ |q.2| then 1 else 0) ∂(μ ⊗ₘ κ) := by
  have hc0 : ENNReal.ofReal (min p (1 - p)) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; exact lt_min hp0 (by linarith)
  constructor
  · refine q15_main μ W n hWn hPn C hC h1 _ hc0 ENNReal.ofReal_ne_top M hM r hr κ
      (fun ω => estLowerQ W n p ω) ?_
    intro ω
    have hP := hPn (ω 0).1 (fun j => (ω (j.val + 1)).1)
    haveI := empM_prob W n ω hP
    have e : estLowerQ W n p ω = sInf {y | p ≤ (empM W n ω (Iic y)).toReal} := by
      simp only [estLowerQ, empM_cdf W n ω hP.1]
    rw [e]; exact q14_lower _ p hp0 hp1
  · refine q15_main μ W n hWn hPn C hC h1 _ hc0 ENNReal.ofReal_ne_top M hM r hr κ
      (fun ω => estUpperQ W n p ω) ?_
    intro ω
    have hP := hPn (ω 0).1 (fun j => (ω (j.val + 1)).1)
    haveI := empM_prob W n ω hP
    have e : estUpperQ W n p ω = sSup {y | (empM W n ω (Iic y)).toReal ≤ p} := by
      simp only [estUpperQ, empM_cdf W n ω hP.1]
    rw [e]; exact q14_upper _ p hp0 hp1

end StoneRegression.Quantile

open StoneRegression.Quantile
open StoneRegression.Quantile MeasureTheory ProbabilityTheory Filter Topology ENNReal NNReal

theorem solution {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : StoneRegression.Criterion.WeightSeq d) (n : ℕ) (hn : 1 ≤ n)
    (hWn : Measurable
      (fun q : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) => W n q.1 q.2))
    (hPn : ∀ x xs, (∀ i, 0 ≤ W n x xs i) ∧ ∑ i, W n x xs i = 1)
    (C : ℝ≥0) (hC : 1 ≤ C)
    (h1 : ∀ f : EuclideanSpace ℝ (Fin d) → ℝ≥0, Measurable f →
      ∫⁻ ω, ∑ i : Fin n, ‖StoneRegression.Criterion.wAt W n ω i‖ₑ * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(StoneRegression.Criterion.xLaw μ) ≤ C * ∫⁻ x, f x ∂μ)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (M : ℝ) (hM : 0 < M) (r : ℝ) (hr : 1 ≤ r)
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ] :
    ∫⁻ ω, ‖estLowerQ W n p ω‖ₑ ^ r * (if M ≤ |estLowerQ W n p ω| then 1 else 0) ∂(StoneRegression.Criterion.pairLaw μ κ) ≤
        ((C : ℝ≥0∞) / ENNReal.ofReal (min p (1 - p))) *
          ∫⁻ q, ‖q.2‖ₑ ^ r * (if M ≤ |q.2| then 1 else 0) ∂(μ ⊗ₘ κ) ∧
    ∫⁻ ω, ‖estUpperQ W n p ω‖ₑ ^ r * (if M ≤ |estUpperQ W n p ω| then 1 else 0) ∂(StoneRegression.Criterion.pairLaw μ κ) ≤
        ((C : ℝ≥0∞) / ENNReal.ofReal (min p (1 - p))) *
          ∫⁻ q, ‖q.2‖ₑ ^ r * (if M ≤ |q.2| then 1 else 0) ∂(μ ⊗ₘ κ) := by
  exact proposition_15_core μ W n hn hWn hPn C hC h1 p hp0 hp1 M hM r hr κ
