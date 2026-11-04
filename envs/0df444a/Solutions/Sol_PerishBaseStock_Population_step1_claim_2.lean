-- Prove2me | solution 2 for PerishBaseStock.Population.step1_claim
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T23:11:21.100704+00:00
-- url     : https://prove2.me/submissions/7e3f4a8b-b368-4414-8b12-5e9306db27f7

import Definitions.Def_PerishBaseStock_Population_Model
import Definitions.Def_PerishBaseStock_Population_CompoundDemand

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace Pop2T

section iid
variable (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]

def lap (t : ℝ) : ℝ := ∫ x : ℝ≥0, Real.exp (t * x) ∂ρ

abbrev seq : Measure (ℕ → ℝ≥0) := Measure.infinitePi fun _ => ρ

def S (k : ℕ) (ω : ℕ → ℝ≥0) : ℝ := ∑ i ∈ Finset.range k, ((ω i : ℝ≥0) : ℝ)

theorem meas_S (k : ℕ) : Measurable (S k) :=
  Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).coe_nnreal_real

theorem S_nonneg (k : ℕ) (ω : ℕ → ℝ≥0) : 0 ≤ S k ω :=
  Finset.sum_nonneg fun i _ => NNReal.coe_nonneg _

theorem S_mono (x : ℕ → ℝ≥0) {a b : ℕ} (hab : a ≤ b) : S a x ≤ S b x := by
  unfold S
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
    fun _ _ _ => NNReal.coe_nonneg _

theorem indep : iIndepFun (fun i (ω : ℕ → ℝ≥0) => ((ω i : ℝ≥0) : ℝ)) (seq ρ) :=
  iIndepFun_infinitePi (X := fun _ (x : ℝ≥0) => (x : ℝ)) (fun _ => by fun_prop)

theorem map_eval (i : ℕ) : (seq ρ).map (fun ω => ω i) = ρ := Measure.infinitePi_map_eval _ i

theorem integral_coord (f : ℝ≥0 → ℝ) (hf : Measurable f) (i : ℕ) :
    ∫ ω, f (ω i) ∂seq ρ = ∫ x, f x ∂ρ := by
  conv_rhs => rw [← map_eval ρ i]
  rw [integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable]

theorem mgf_coord (i : ℕ) (t : ℝ) :
    mgf (fun ω : ℕ → ℝ≥0 => ((ω i : ℝ≥0) : ℝ)) (seq ρ) t = lap ρ t := by
  unfold mgf lap
  exact integral_coord ρ (fun x => Real.exp (t * x)) (by fun_prop) i

theorem mgf_S (k : ℕ) (t : ℝ) : mgf (S k) (seq ρ) t = lap ρ t ^ k := by
  have hm := (indep ρ).mgf_sum (fun i => by fun_prop) (Finset.range k) (t := t)
  simp only [mgf_coord, Finset.prod_const, Finset.card_range] at hm
  rw [← hm]; congr 1; ext ω; simp [S]

theorem integrable_exp_coord {s : ℝ} (hs : Integrable (fun x : ℝ≥0 => Real.exp (s * x)) ρ)
    (i : ℕ) : Integrable (fun ω : ℕ → ℝ≥0 => Real.exp (s * ((ω i : ℝ≥0) : ℝ))) (seq ρ) := by
  have h : Integrable (fun x : ℝ≥0 => Real.exp (s * x)) ((seq ρ).map (fun ω => ω i)) := by
    rw [map_eval]; exact hs
  exact (integrable_map_measure h.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).1 h

/-- Chernoff upper-tail bound. -/
theorem upper_tail (k : ℕ) (ε : ℝ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : Integrable (fun x : ℝ≥0 => Real.exp (s * x)) ρ) :
    (seq ρ).real {ω | ε ≤ S k ω} ≤ Real.exp (-s * ε) * lap ρ s ^ k := by
  have hint := (indep ρ).integrable_exp_mul_sum (t := s) (fun i => by fun_prop)
    (s := Finset.range k) (fun i _ => integrable_exp_coord ρ hs i)
  have hSeq : (∑ i ∈ Finset.range k, fun ω : ℕ → ℝ≥0 => ((ω i : ℝ≥0) : ℝ)) = S k := by
    ext ω; simp [S]
  rw [hSeq] at hint
  have := measure_ge_le_exp_mul_mgf (μ := seq ρ) (X := S k) ε hs0 hint
  rwa [mgf_S] at this

theorem lap_nonneg (t : ℝ) : 0 ≤ lap ρ t :=
  integral_nonneg fun _ => (Real.exp_pos _).le

end iid

theorem exp_le (y : ℝ) (hy : 0 ≤ y) : Real.exp y ≤ 1 + y + y ^ 2 * Real.exp y := by
  have h1 : Real.exp y - 1 ≤ y * Real.exp y := by
    have := Real.add_one_le_exp (-y)
    have h : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos y]
  nlinarith [Real.exp_pos y]

section bounds
variable (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]

theorem lap_pos_le (h1 : Integrable (fun x : ℝ≥0 => (x : ℝ)) ρ) {s0 : ℝ} (hs0 : 0 < s0)
    (he : Integrable (fun x : ℝ≥0 => Real.exp (s0 * x)) ρ) {s : ℝ} (hs : 0 ≤ s)
    (hss : s ≤ s0 / 2) :
    lap ρ s ≤ 1 + s * ∫ x : ℝ≥0, (x : ℝ) ∂ρ +
      s ^ 2 * (32 / s0 ^ 2 * ∫ x : ℝ≥0, Real.exp (s0 * x) ∂ρ) := by
  unfold lap
  have key : ∀ x : ℝ≥0, Real.exp (s * x) ≤ 1 + s * x + s ^ 2 * (32 / s0 ^ 2 * Real.exp (s0 * x)) := by
    intro x
    have hx := NNReal.coe_nonneg x
    have e1 := exp_le (s * x) (mul_nonneg hs hx)
    have q := Real.quadratic_le_exp_of_nonneg (show 0 ≤ s0 * x / 4 by positivity)
    have hx2 : (x : ℝ) ^ 2 ≤ 32 / s0 ^ 2 * Real.exp (s0 * x / 4) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (s0 * x / 4), Real.exp_pos (s0 * x / 4)]
    have hmono : Real.exp (s0 * x / 4) * Real.exp (s * x) ≤ Real.exp (s0 * x) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
    have : (s * x) ^ 2 * Real.exp (s * x) ≤ s ^ 2 * (32 / s0 ^ 2 * Real.exp (s0 * x)) := by
      rw [mul_pow]
      have : (x : ℝ) ^ 2 * Real.exp (s * x) ≤ 32 / s0 ^ 2 * Real.exp (s0 * x) := by
        calc (x : ℝ) ^ 2 * Real.exp (s * x)
            ≤ 32 / s0 ^ 2 * Real.exp (s0 * x / 4) * Real.exp (s * x) :=
              mul_le_mul_of_nonneg_right hx2 (Real.exp_pos _).le
          _ = 32 / s0 ^ 2 * (Real.exp (s0 * x / 4) * Real.exp (s * x)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hmono (by positivity)
      calc s ^ 2 * (x : ℝ) ^ 2 * Real.exp (s * x) = s ^ 2 * ((x : ℝ) ^ 2 * Real.exp (s * x)) := by
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have hint : Integrable (fun x : ℝ≥0 => Real.exp (s * x)) ρ := by
    refine (((integrable_const 1).add (h1.const_mul s)).add
      ((he.const_mul (32 / s0 ^ 2)).const_mul (s ^ 2))).mono' (by fun_prop)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact key x
  have hR : Integrable (fun x : ℝ≥0 => 1 + s * (x : ℝ) + s ^ 2 * (32 / s0 ^ 2 *
      Real.exp (s0 * x))) ρ :=
    ((integrable_const 1).add (h1.const_mul s)).add ((he.const_mul _).const_mul _)
  calc ∫ x : ℝ≥0, Real.exp (s * x) ∂ρ ≤ ∫ x : ℝ≥0, (1 + s * (x : ℝ) + s ^ 2 * (32 / s0 ^ 2 *
        Real.exp (s0 * x))) ∂ρ := integral_mono hint hR key
    _ = _ := by
        have hA : Integrable (fun x : ℝ≥0 => 1 + s * (x : ℝ)) ρ :=
          (integrable_const _).add (h1.const_mul _)
        have hB : Integrable (fun x : ℝ≥0 => s * (x : ℝ)) ρ := h1.const_mul _
        have hC : Integrable (fun x : ℝ≥0 => s ^ 2 * (32 / s0 ^ 2 * Real.exp (s0 * x))) ρ :=
          (he.const_mul _).const_mul _
        rw [integral_add hA hC, integral_add (integrable_const _) hB, integral_const_mul,
          integral_const_mul, integral_const_mul]
        simp

theorem integrable_exp_of_le {s0 s : ℝ} (hs : 0 ≤ s) (hss : s ≤ s0)
    (he : Integrable (fun x : ℝ≥0 => Real.exp (s0 * x)) ρ) :
    Integrable (fun x : ℝ≥0 => Real.exp (s * x)) ρ := by
  refine he.mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hss (NNReal.coe_nonneg x))

end bounds

open PerishBaseStock.Population

theorem smithS_eq (j : ℕ) (x : ℕ → ℝ≥0) :
    SmithRenewal.Elementary.S interarrivals j x = S j x := rfl

/-- If `N(n) = N` then the `(N+1)`-st renewal epoch exceeds `n`. -/
theorem lt_S_succ_of_count (n : ℕ) (x : ℕ → ℝ≥0) (N : ℕ) (h : arrivalCount n x = (N : ℕ∞)) :
    (n : ℝ) < S (N + 1) x := by
  by_contra hc
  push Not at hc
  have hsub : ((Finset.Icc 1 (N + 1) : Finset ℕ) : Set ℕ) ⊆
      {j : ℕ | 1 ≤ j ∧ SmithRenewal.Elementary.S interarrivals j x ≤ (n : ℝ)} := by
    intro j hj
    simp only [Finset.coe_Icc, Set.mem_Icc] at hj
    refine ⟨hj.1, ?_⟩
    rw [smithS_eq]
    exact (S_mono x hj.2).trans hc
  have := Set.encard_le_encard hsub
  rw [Set.encard_coe_eq_coe_finsetCard] at this
  unfold arrivalCount SmithRenewal.Elementary.N at h
  rw [h] at this
  simp only [Nat.card_Icc, add_tsub_cancel_right] at this
  have h2 : ((N + 1 : ℕ) : ℕ∞) ≤ (N : ℕ∞) := this
  exact absurd (Nat.cast_le.1 h2) (by omega)


theorem exp_neg_le (y : ℝ) (hy : 0 ≤ y) : Real.exp (-y) ≤ 1 - y + y ^ 2 := by
  have h1 : 1 - y ≤ Real.exp (-y) := by linarith [Real.add_one_le_exp (-y)]
  have h2 : Real.exp (-y) * (1 + y) ≤ 1 := by
    have := Real.add_one_le_exp y
    calc Real.exp (-y) * (1 + y) ≤ Real.exp (-y) * Real.exp y := by
          apply mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  nlinarith

section neg
variable (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]

theorem integrable_exp_neg_one {l : ℝ} (hl : 0 ≤ l) :
    Integrable (fun x : ℝ≥0 => Real.exp (-l * x)) ρ := by
  refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (by nlinarith [NNReal.coe_nonneg x])

theorem lap_neg_le (h1 : Integrable (fun x : ℝ≥0 => (x : ℝ)) ρ)
    (h2 : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 2) ρ) {l : ℝ} (hl : 0 ≤ l) :
    lap ρ (-l) ≤ 1 - l * ∫ x : ℝ≥0, (x : ℝ) ∂ρ + l ^ 2 * ∫ x : ℝ≥0, (x : ℝ) ^ 2 ∂ρ := by
  unfold lap
  have hint := integrable_exp_neg_one ρ hl
  have hR : Integrable (fun x : ℝ≥0 => 1 - l * (x : ℝ) + l ^ 2 * (x : ℝ) ^ 2) ρ :=
    ((integrable_const _).sub (h1.const_mul _)).add (h2.const_mul _)
  calc ∫ x : ℝ≥0, Real.exp (-l * x) ∂ρ ≤ ∫ x : ℝ≥0, (1 - l * (x : ℝ) + l ^ 2 * (x : ℝ) ^ 2) ∂ρ :=
        integral_mono hint hR fun x => by
          have := exp_neg_le (l * x) (mul_nonneg hl (NNReal.coe_nonneg x))
          rw [neg_mul]; nlinarith
    _ = _ := by
        have hA : Integrable (fun x : ℝ≥0 => 1 - l * (x : ℝ)) ρ :=
          (integrable_const _).sub (h1.const_mul _)
        have hB : Integrable (fun x : ℝ≥0 => l * (x : ℝ)) ρ := h1.const_mul _
        have hC : Integrable (fun x : ℝ≥0 => l ^ 2 * (x : ℝ) ^ 2) ρ := h2.const_mul _
        rw [integral_add hA hC, integral_sub (integrable_const _) hB, integral_const_mul,
          integral_const_mul]
        simp

theorem lap_le_one {l : ℝ} (hl : 0 ≤ l) : lap ρ (-l) ≤ 1 := by
  unfold lap
  calc ∫ x : ℝ≥0, Real.exp (-l * x) ∂ρ ≤ ∫ _x : ℝ≥0, (1 : ℝ) ∂ρ :=
        integral_mono (integrable_exp_neg_one ρ hl) (integrable_const _) fun x =>
          Real.exp_le_one_iff.2 (by nlinarith [NNReal.coe_nonneg x])
    _ = 1 := by simp

theorem lap_pos (t : ℝ) (ht : Integrable (fun x : ℝ≥0 => Real.exp (t * x)) ρ) : 0 < lap ρ t := by
  have := mgf_pos (X := fun x : ℝ≥0 => (x : ℝ)) (μ := ρ) (t := t) ht
  simpa [mgf, lap] using this

theorem integrable_exp_neg (k : ℕ) {l : ℝ} (hl : 0 ≤ l) :
    Integrable (fun ω => Real.exp (-l * S k ω)) (seq ρ) := by
  refine Integrable.of_bound ((meas_S k).const_mul _).exp.aestronglyMeasurable 1
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (by nlinarith [S_nonneg k ω])

theorem integral_exp_neg_S (k : ℕ) (l : ℝ) :
    ∫ ω, Real.exp (-l * S k ω) ∂seq ρ = lap ρ (-l) ^ k := by
  rw [← mgf_S]; rfl

/-- Chernoff lower-tail bound. -/
theorem lower_tail (k : ℕ) (ε : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    (seq ρ).real {ω | S k ω ≤ ε} ≤ Real.exp (l * ε) * lap ρ (-l) ^ k := by
  have := measure_le_le_exp_mul_mgf (μ := seq ρ) (X := S k) ε (t := -l) (by linarith)
    (integrable_exp_neg ρ k hl)
  rw [mgf_S] at this; simpa using this

end neg

open PerishBaseStock.Population

instance isProb_seqX (X : InterarrivalLaw) : IsProbabilityMeasure (interarrivalSeqLaw X) := by
  unfold interarrivalSeqLaw; infer_instance

theorem S_le_of_top (n : ℕ) (x : ℕ → ℝ≥0) (h : arrivalCount n x = ⊤) (K : ℕ) :
    S K x ≤ n := by
  by_contra hc
  push Not at hc
  have hsub : {j : ℕ | 1 ≤ j ∧ SmithRenewal.Elementary.S interarrivals j x ≤ (n : ℝ)} ⊆
      ((Finset.range K : Finset ℕ) : Set ℕ) := by
    intro j hj
    simp only [Set.mem_ofPred_eq, smithS_eq] at hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hjK
    push Not at hjK
    have := S_mono x hjK
    linarith [hj.2]
  have := Set.encard_le_encard hsub
  rw [Set.encard_coe_eq_coe_finsetCard] at this
  unfold arrivalCount SmithRenewal.Elementary.N at h
  rw [h] at this
  exact absurd this (by simp)

theorem lapX_lt_one (X : InterarrivalLaw) :
    ∃ l : ℝ, 0 < l ∧ lap X.law (-l) < 1 ∧ 0 ≤ lap X.law (-l) := by
  have h1 : Integrable (fun x : ℝ≥0 => (x : ℝ)) X.law := X.memLp_two.integrable one_le_two
  have h2 : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 2) X.law :=
    X.memLp_two.integrable_sq
  set xm2 := ∫ y : ℝ≥0, (y : ℝ) ^ 2 ∂X.law
  have hxm2 : 0 ≤ xm2 := integral_nonneg fun y => sq_nonneg _
  set l := 1 / (2 * (xm2 + 1))
  have hl : 0 < l := by positivity
  refine ⟨l, hl, ?_, lap_nonneg _ _⟩
  have h := lap_neg_le X.law h1 h2 hl.le
  rw [X.mean_eq_one] at h
  have : l * xm2 ≤ 1 / 2 := by
    simp only [l]; rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  nlinarith

theorem top_null (X : InterarrivalLaw) (n : ℕ) :
    interarrivalSeqLaw X {x | arrivalCount n x = ⊤} = 0 := by
  obtain ⟨l, hl, hq1, hq0⟩ := lapX_lt_one X
  have hbound : ∀ K : ℕ, interarrivalSeqLaw X {x | arrivalCount n x = ⊤} ≤
      ENNReal.ofReal (Real.exp (l * n) * lap X.law (-l) ^ K) := by
    intro K
    have hsub : {x | arrivalCount n x = ⊤} ⊆ {x | S K x ≤ n} := fun x hx => S_le_of_top n x hx K
    calc _ ≤ interarrivalSeqLaw X {x | S K x ≤ n} := measure_mono hsub
      _ = ENNReal.ofReal ((seq X.law).real {x | S K x ≤ n}) := by
          rw [ofReal_measureReal (measure_ne_top _ _)]; rfl
      _ ≤ _ := ENNReal.ofReal_le_ofReal (lower_tail X.law K n hl.le)
  have ht : Tendsto (fun K : ℕ => ENNReal.ofReal (Real.exp (l * n) * lap X.law (-l) ^ K))
      atTop (nhds 0) := by
    rw [← ENNReal.ofReal_zero]
    apply ENNReal.tendsto_ofReal
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (Real.exp (l * n))
  exact le_antisymm (ge_of_tendsto' ht hbound) bot_le

theorem compound_eq (n : ℕ) (ω : PopSample) (N : ℕ) (h : arrivalCount n ω.2 = (N : ℕ∞)) :
    ((compoundDemand n ω : ℝ≥0) : ℝ) = S N ω.1 := by
  unfold compoundDemand
  rw [h, ENat.toNat_coe]
  push_cast [S]; rfl

theorem popSampleLaw_isProb (Dh : CustomerLaw) (X : InterarrivalLaw) :
    IsProbabilityMeasure (popSampleLaw Dh X) := by
  unfold popSampleLaw interarrivalSeqLaw; infer_instance

theorem map_snd (Dh : CustomerLaw) (X : InterarrivalLaw) :
    (popSampleLaw Dh X).map Prod.snd = interarrivalSeqLaw X := by
  unfold popSampleLaw
  rw [Measure.map_snd_prod]; simp

theorem map_fst (Dh : CustomerLaw) (X : InterarrivalLaw) :
    (popSampleLaw Dh X).map Prod.fst = seq Dh.law := by
  unfold popSampleLaw
  rw [Measure.map_fst_prod]
  simp

theorem integral_snd (Dh : CustomerLaw) (X : InterarrivalLaw) (f : (ℕ → ℝ≥0) → ℝ)
    (hf : AEStronglyMeasurable f (interarrivalSeqLaw X)) :
    ∫ ω, f ω.2 ∂popSampleLaw Dh X = ∫ x, f x ∂interarrivalSeqLaw X := by
  rw [← map_snd Dh X] at hf ⊢
  rw [integral_map measurable_snd.aemeasurable hf]

theorem integral_fst (Dh : CustomerLaw) (X : InterarrivalLaw) (f : (ℕ → ℝ≥0) → ℝ)
    (hf : AEStronglyMeasurable f (seq Dh.law)) :
    ∫ ω, f ω.1 ∂popSampleLaw Dh X = ∫ x, f x ∂seq Dh.law := by
  rw [← map_fst Dh X] at hf ⊢
  rw [integral_map measurable_fst.aemeasurable hf]

theorem ae_snd (Dh : CustomerLaw) (X : InterarrivalLaw) {p : (ℕ → ℝ≥0) → Prop}
    (h : ∀ᵐ x ∂interarrivalSeqLaw X, p x) : ∀ᵐ ω ∂popSampleLaw Dh X, p ω.2 := by
  rw [← map_snd Dh X] at h
  exact ae_of_ae_map measurable_snd.aemeasurable h

theorem count_finite_ae (X : InterarrivalLaw) (n : ℕ) :
    ∀ᵐ x ∂interarrivalSeqLaw X, ∃ N : ℕ, arrivalCount n x = (N : ℕ∞) := by
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) (top_null X n)
  simp only [Set.mem_ofPred_eq, not_exists] at hx ⊢
  by_contra hc
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 hc
  exact hx N hN.symm

theorem count_eq_iff (n : ℕ) (x : ℕ → ℝ≥0) (k : ℕ) :
    arrivalCount n x = (k : ℕ∞) ↔ (k = 0 ∨ S k x ≤ n) ∧ (n : ℝ) < S (k + 1) x := by
  constructor
  · intro h
    refine ⟨?_, lt_S_succ_of_count n x k h⟩
    by_contra hc
    push Not at hc
    obtain ⟨hk0, hkS⟩ := hc
    have hsub : {j : ℕ | 1 ≤ j ∧ SmithRenewal.Elementary.S interarrivals j x ≤ (n : ℝ)} ⊆
        ((Finset.Icc 1 (k - 1) : Finset ℕ) : Set ℕ) := by
      intro j hj
      simp only [Set.mem_ofPred_eq, smithS_eq] at hj
      simp only [Finset.coe_Icc, Set.mem_Icc]
      refine ⟨hj.1, ?_⟩
      by_contra hjk
      push Not at hjk
      have := S_mono x (show k ≤ j by omega)
      linarith [hj.2]
    have := Set.encard_le_encard hsub
    rw [Set.encard_coe_eq_coe_finsetCard] at this
    unfold arrivalCount SmithRenewal.Elementary.N at h
    rw [h] at this
    simp only [Nat.card_Icc] at this
    have h2 : (k : ℕ∞) ≤ ((k - 1 + 1 - 1 : ℕ) : ℕ∞) := this
    have := Nat.cast_le.1 h2
    omega
  · rintro ⟨h1, h2⟩
    have hset : {j : ℕ | 1 ≤ j ∧ SmithRenewal.Elementary.S interarrivals j x ≤ (n : ℝ)} =
        ((Finset.Icc 1 k : Finset ℕ) : Set ℕ) := by
      ext j
      simp only [Set.mem_ofPred_eq, smithS_eq, Finset.coe_Icc, Set.mem_Icc]
      constructor
      · rintro ⟨hj1, hj2⟩
        refine ⟨hj1, ?_⟩
        by_contra hjk
        push Not at hjk
        have := S_mono x (show k + 1 ≤ j by omega)
        linarith
      · rintro ⟨hj1, hj2⟩
        refine ⟨hj1, ?_⟩
        rcases h1 with h1 | h1
        · omega
        · exact (S_mono x hj2).trans h1
    unfold arrivalCount SmithRenewal.Elementary.N
    rw [hset, Set.encard_coe_eq_coe_finsetCard]
    simp

theorem measurable_count (n : ℕ) : Measurable (arrivalCount n) := by
  have hfin : ∀ k : ℕ, MeasurableSet (arrivalCount n ⁻¹' {(k : ℕ∞)}) := by
    intro k
    have : arrivalCount n ⁻¹' {(k : ℕ∞)} =
        {x | (k = 0 ∨ S k x ≤ n) ∧ (n : ℝ) < S (k + 1) x} := by
      ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      exact count_eq_iff n x k
    rw [this]
    refine MeasurableSet.inter ?_ (measurableSet_lt measurable_const (meas_S _))
    exact (MeasurableSet.const _).union (measurableSet_le (meas_S _) measurable_const)
  refine measurable_to_countable' fun y => ?_
  induction y using ENat.recTopCoe with
  | top =>
    have : arrivalCount n ⁻¹' {⊤} = (⋃ k : ℕ, arrivalCount n ⁻¹' {(k : ℕ∞)})ᶜ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
        not_exists]
      constructor
      · intro h k hk; rw [h] at hk; exact ENat.top_ne_coe k hk
      · intro h
        by_contra hc
        obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 hc
        exact h N hN.symm
    rw [this]
    exact (MeasurableSet.iUnion hfin).compl
  | coe k => exact hfin k

theorem measurable_countNat (n : ℕ) :
    Measurable (fun x : ℕ → ℝ≥0 => ((arrivalCount n x).toNat : ℝ)) :=
  ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
    ((measurable_of_countable ENat.toNat).comp (measurable_count n)))

theorem measurable_compound (n : ℕ) : Measurable (compoundDemand n) := by
  have hF : Measurable (fun p : PopSample × ℕ => ∑ j ∈ Finset.range p.2, p.1.1 j) :=
    measurable_from_prod_countable_left fun k => by
      simp only
      exact Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).comp measurable_fst
  have hN : Measurable (fun ω : PopSample => (arrivalCount n ω.2).toNat) :=
    (measurable_of_countable ENat.toNat).comp ((measurable_count n).comp measurable_snd)
  exact hF.comp (measurable_id.prodMk hN)

section moments
variable (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]

theorem memLp_coord (h2 : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 2) ρ) (i : ℕ) :
    MemLp (fun ω : ℕ → ℝ≥0 => ((ω i : ℝ≥0) : ℝ)) 2 (seq ρ) := by
  rw [memLp_two_iff_integrable_sq ((measurable_pi_apply i).coe_nnreal_real.aestronglyMeasurable)]
  have h : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 2) ((seq ρ).map (fun ω => ω i)) := by
    rw [map_eval]; exact h2
  exact (integrable_map_measure h.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).1 h

theorem var_coord (i : ℕ) :
    variance (fun ω : ℕ → ℝ≥0 => ((ω i : ℝ≥0) : ℝ)) (seq ρ) = variance (fun x : ℝ≥0 => (x : ℝ)) ρ :=
  (measurePreserving_eval_infinitePi (fun _ => ρ) i).variance_fun_comp (by fun_prop)

theorem integrable_coord (h1 : Integrable (fun x : ℝ≥0 => (x : ℝ)) ρ) (i : ℕ) :
    Integrable (fun ω : ℕ → ℝ≥0 => ((ω i : ℝ≥0) : ℝ)) (seq ρ) := by
  have h : Integrable (fun x : ℝ≥0 => (x : ℝ)) ((seq ρ).map (fun ω => ω i)) := by
    rw [map_eval]; exact h1
  exact (integrable_map_measure h.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).1 h

theorem integrable_S (h1 : Integrable (fun x : ℝ≥0 => (x : ℝ)) ρ) (k : ℕ) :
    Integrable (S k) (seq ρ) := by
  have : S k = fun ω => ∑ i ∈ Finset.range k, ((ω i : ℝ≥0) : ℝ) := rfl
  rw [this]; exact integrable_finsetSum _ fun i _ => integrable_coord ρ h1 i

theorem mean_S (h1 : Integrable (fun x : ℝ≥0 => (x : ℝ)) ρ) (k : ℕ) :
    ∫ ω, S k ω ∂seq ρ = k * ∫ x : ℝ≥0, (x : ℝ) ∂ρ := by
  unfold S
  rw [integral_finsetSum _ fun i _ => integrable_coord ρ h1 i]
  simp only [integral_coord ρ (fun x : ℝ≥0 => (x : ℝ)) (by fun_prop), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]

theorem memLp_S (h2 : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 2) ρ) (k : ℕ) :
    MemLp (S k) 2 (seq ρ) := by
  have : S k = ∑ i ∈ Finset.range k, fun ω : ℕ → ℝ≥0 => ((ω i : ℝ≥0) : ℝ) := by
    ext ω; simp [S]
  rw [this]; exact memLp_finsetSum' _ fun i _ => memLp_coord ρ h2 i

theorem var_S (h2 : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 2) ρ) (k : ℕ) :
    variance (S k) (seq ρ) = k * variance (fun x : ℝ≥0 => (x : ℝ)) ρ := by
  have hS : S k = fun ω => ∑ i ∈ Finset.range k, ((ω i : ℝ≥0) : ℝ) := rfl
  rw [hS, variance_fun_sum' (X := fun i (ω : ℕ → ℝ≥0) => ((ω i : ℝ≥0) : ℝ))
    (fun i _ => memLp_coord ρ h2 i)]
  have : ∀ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
      cov[fun ω : ℕ → ℝ≥0 => ((ω i : ℝ≥0) : ℝ), fun ω : ℕ → ℝ≥0 => ((ω j : ℝ≥0) : ℝ); seq ρ] =
      variance (fun x : ℝ≥0 => (x : ℝ)) ρ := by
    intro i hi
    rw [Finset.sum_eq_single i]
    · rw [covariance_self ((measurable_pi_apply i).coe_nnreal_real.aemeasurable), var_coord]
    · intro j _ hji
      exact ((indep ρ).indepFun hji.symm).covariance_eq_zero (memLp_coord ρ h2 i)
        (memLp_coord ρ h2 j)
    · intro h; exact absurd hi h
  rw [Finset.sum_congr rfl this]
  simp

theorem sq_S (h1 : Integrable (fun x : ℝ≥0 => (x : ℝ)) ρ)
    (h2 : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 2) ρ) (k : ℕ) :
    ∫ ω, S k ω ^ 2 ∂seq ρ = k * variance (fun x : ℝ≥0 => (x : ℝ)) ρ +
      (k : ℝ) ^ 2 * (∫ x : ℝ≥0, (x : ℝ) ∂ρ) ^ 2 := by
  have h := variance_eq_sub (memLp_S ρ h2 k)
  rw [var_S ρ h2, mean_S ρ h1] at h
  have : ∫ ω, S k ω ^ 2 ∂seq ρ = (seq ρ)[S k ^ 2] := rfl
  rw [this]; linarith [h]

end moments

theorem countNat_le (n : ℕ) (x : ℕ → ℝ≥0) (K : ℕ) (hK : 1 ≤ K)
    (h : (arrivalCount n x).toNat = K) : S K x ≤ n := by
  have hne : arrivalCount n x ≠ ⊤ := by
    intro ht; rw [ht] at h; simp at h; omega
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 hne
  rw [← hN, ENat.toNat_coe] at h
  subst h
  rcases ((count_eq_iff n x N).1 hN.symm).1 with h0 | h0
  · omega
  · exact h0

/-- The renewal count has a finite second moment. -/
theorem countNat_sq_integrable (X : InterarrivalLaw) (n : ℕ) :
    Integrable (fun x : ℕ → ℝ≥0 => ((arrivalCount n x).toNat : ℝ) ^ 2) (interarrivalSeqLaw X) := by
  obtain ⟨l, hl, hq1, hq0⟩ := lapX_lt_one X
  set q := lap X.law (-l)
  set C := Real.exp (l * n)
  set Kf : (ℕ → ℝ≥0) → ℕ := fun x => (arrivalCount n x).toNat with hKf
  have hKm : Measurable Kf := (measurable_of_countable ENat.toNat).comp (measurable_count n)
  have hbound : ∀ K : ℕ, (interarrivalSeqLaw X).map Kf {K} ≤
      ENNReal.ofReal (if K = 0 then 1 else C * q ^ K) := by
    intro K
    rw [Measure.map_apply hKm (measurableSet_singleton K)]
    split_ifs with hK
    · rw [ENNReal.ofReal_one]; exact prob_le_one
    · have hsub : Kf ⁻¹' {K} ⊆ {x | S K x ≤ n} := fun x hx =>
        countNat_le n x K (by omega) hx
      calc _ ≤ interarrivalSeqLaw X {x | S K x ≤ n} := measure_mono hsub
        _ = ENNReal.ofReal ((seq X.law).real {x | S K x ≤ n}) := by
            rw [ofReal_measureReal (measure_ne_top _ _)]; rfl
        _ ≤ _ := ENNReal.ofReal_le_ofReal (lower_tail X.law K n hl.le)
  have hsum : Summable (fun K : ℕ => (K : ℝ) ^ 2 * (C * q ^ K)) := by
    have := (summable_pow_mul_geometric_of_norm_lt_one 2
      (show ‖q‖ < 1 by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)).mul_left C
    refine this.congr fun K => ?_
    ring
  have hlin : ∫⁻ x, ENNReal.ofReal (((Kf x : ℕ) : ℝ) ^ 2) ∂interarrivalSeqLaw X < ⊤ := by
    have e1 : ∫⁻ x, ENNReal.ofReal (((Kf x : ℕ) : ℝ) ^ 2) ∂interarrivalSeqLaw X =
        ∫⁻ K, ENNReal.ofReal ((K : ℝ) ^ 2) ∂(interarrivalSeqLaw X).map Kf := by
      rw [lintegral_map (measurable_of_countable _) hKm]
    rw [e1, lintegral_countable']
    calc ∑' K : ℕ, ENNReal.ofReal ((K : ℝ) ^ 2) * (interarrivalSeqLaw X).map Kf {K}
        ≤ ∑' K : ℕ, ENNReal.ofReal ((K : ℝ) ^ 2 * (C * q ^ K)) := by
          refine ENNReal.tsum_le_tsum fun K => ?_
          rw [ENNReal.ofReal_mul (sq_nonneg _)]
          refine mul_le_mul_right ?_ _
          rcases Nat.eq_zero_or_pos K with hK | hK
          · subst hK
            rw [Measure.map_apply hKm (measurableSet_singleton 0), pow_zero, mul_one]
            refine prob_le_one.trans ?_
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by positivity))
          · have := hbound K; rw [if_neg (by omega)] at this; exact this
      _ = ENNReal.ofReal (∑' K : ℕ, (K : ℝ) ^ 2 * (C * q ^ K)) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun K => by positivity) hsum).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  refine ⟨(measurable_countNat n).pow_const 2 |>.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _)]
  exact hlin

end Pop2T
end

namespace Pop2T
open PerishBaseStock.Population

/-- Chebyshev upper-tail bound for i.i.d. sums. -/
theorem cheb (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (h1 : Integrable (fun x : ℝ≥0 => (x : ℝ)) ρ)
    (h2 : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 2) ρ) (k : ℕ) (y : ℝ)
    (hy : k * ∫ x : ℝ≥0, (x : ℝ) ∂ρ < y) :
    (seq ρ).real {ω | y ≤ S k ω} ≤
      k * variance (fun x : ℝ≥0 => (x : ℝ)) ρ / (y - k * ∫ x : ℝ≥0, (x : ℝ) ∂ρ) ^ 2 := by
  set c := y - k * ∫ x : ℝ≥0, (x : ℝ) ∂ρ
  have hc : 0 < c := by simp only [c]; linarith
  have hcheb := meas_ge_le_variance_div_sq (memLp_S ρ h2 k) hc
  rw [mean_S ρ h1, var_S ρ h2] at hcheb
  have hsub : {ω | y ≤ S k ω} ⊆ {ω | c ≤ |S k ω - k * ∫ x : ℝ≥0, (x : ℝ) ∂ρ|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [abs_of_nonneg (by simp only [c] at hc ⊢; linarith)]
    simp only [c]; linarith
  have hv : 0 ≤ (k : ℝ) * variance (fun x : ℝ≥0 => (x : ℝ)) ρ / c ^ 2 := by
    have := variance_nonneg (fun x : ℝ≥0 => (x : ℝ)) ρ; positivity
  calc (seq ρ).real {ω | y ≤ S k ω}
      ≤ (seq ρ).real {ω | c ≤ |S k ω - k * ∫ x : ℝ≥0, (x : ℝ) ∂ρ|} := measureReal_mono hsub
    _ ≤ _ := by
        rw [measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal hv hcheb

/-- The newsvendor level is at most any `T ≥ 0` whose upper tail is at most `h/(p+h)`. -/
theorem nv_le_of_tail (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] {h p : ℝ} (hh : 0 < h)
    (hp : 0 < p) (T : ℝ) (hT0 : 0 ≤ T) (hc : ρ.real {x : ℝ≥0 | T < (x : ℝ)} ≤ h / (p + h)) :
    (LostSalesOrderUpTo.Asymptotic.newsvendorLevel ρ h p : ℝ) ≤ T := by
  set S0 := T.toNNReal with hS0
  have hS0T : (S0 : ℝ) = T := Real.coe_toNNReal _ hT0
  have hsetc : Set.Iic S0 = {x : ℝ≥0 | T < (x : ℝ)}ᶜ := by
    ext x
    simp only [Set.mem_Iic, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
    rw [← NNReal.coe_le_coe, hS0T]
  have hmeas : MeasurableSet {x : ℝ≥0 | T < (x : ℝ)} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hmemS : S0 ∈ {S : ℝ≥0 | ENNReal.ofReal (p / (p + h)) ≤
      LostSalesOrderUpTo.Asymptotic.distribution ρ S} := by
    simp only [Set.mem_ofPred_eq, LostSalesOrderUpTo.Asymptotic.distribution]
    rw [hsetc, prob_compl_eq_one_sub hmeas]
    have h1 : ρ {x : ℝ≥0 | T < (x : ℝ)} ≤ ENNReal.ofReal (h / (p + h)) := by
      rw [← ofReal_measureReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal hc
    have hpos : 0 < p + h := add_pos hp hh
    have h2 : p / (p + h) = 1 - h / (p + h) := by field_simp; ring
    rw [h2, ENNReal.ofReal_sub _ (div_nonneg hh.le hpos.le), ENNReal.ofReal_one]
    exact tsub_le_tsub_left h1 _
  have hle : LostSalesOrderUpTo.Asymptotic.newsvendorLevel ρ h p ≤ S0 :=
    csInf_le (OrderBot.bddBelow _) hmemS
  calc _ ≤ (S0 : ℝ) := NNReal.coe_le_coe.2 hle
    _ = T := hS0T

/-- Pathwise: if `T_{K+1} > n` then `D(n) ≤ Σ_{j<K} D̂_j`. -/
theorem compound_le (n : ℕ) (ω : PopSample) (K : ℕ) (h : (n : ℝ) < S (K + 1) ω.2) :
    ((compoundDemand n ω : ℝ≥0) : ℝ) ≤ S K ω.1 := by
  have hne : arrivalCount n ω.2 ≠ ⊤ := fun ht => by
    have := S_le_of_top n ω.2 ht (K + 1); linarith
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 hne
  rw [compound_eq n ω N hN.symm]
  apply S_mono
  by_contra hc
  push Not at hc
  rcases ((count_eq_iff n ω.2 N).1 hN.symm).1 with h0 | h0
  · omega
  · have := S_mono ω.2 (show K + 1 ≤ N by omega); linarith

end Pop2T

open Pop2T PerishBaseStock.Population in
theorem solution (c : PerishBaseStock.Lifetime.Params) (Dh : CustomerLaw) (X : InterarrivalLaw)
    (hμ : 0 < customerMean Dh)
    (P : ℕ → CappedBaseStock.DemandLaw) (hP : IsPopulationFamily Dh X P)
    (k : ℝ) (hk : 1 < k) :
    ∃ n₁ : ℕ, 0 < n₁ ∧ ∀ n : ℕ, n₁ ≤ n →
      (newsvendorLevel (P n) c : ℝ) ≤ k * customerMean Dh * (n : ℝ) := by
  haveI := popSampleLaw_isProb Dh X
  set μ := customerMean Dh with hμdef
  have h1D : Integrable (fun x : ℝ≥0 => (x : ℝ)) Dh.law := Dh.memLp_two.integrable one_le_two
  have h2D : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 2) Dh.law := Dh.memLp_two.integrable_sq
  have h1X : Integrable (fun x : ℝ≥0 => (x : ℝ)) X.law := X.memLp_two.integrable one_le_two
  have h2X : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 2) X.law := X.memLp_two.integrable_sq
  set σ2 := variance (fun x : ℝ≥0 => (x : ℝ)) Dh.law with hσ2
  have hσ0 : 0 ≤ σ2 := variance_nonneg _ _
  set δ := (k - 1) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set M2 := ∫ y : ℝ≥0, (y : ℝ) ^ 2 ∂X.law with hM2
  have hM20 : 0 ≤ M2 := integral_nonneg fun _ => sq_nonneg _
  set l := δ / (2 * (1 + δ) * (M2 + 1)) with hl
  have hl0 : 0 < l := by positivity
  have hlM : l * M2 ≤ δ / (2 * (1 + δ)) := by
    rw [hl, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ δ * (2 * (1 + δ)) := by positivity
    nlinarith
  set κ := l * δ / 2 with hκ
  have hκ0 : 0 < κ := by positivity
  set C2 := (1 + δ) * σ2 / (δ ^ 2 * μ ^ 2) with hC2
  have hthr : 0 < c.h / (c.p + c.h) := div_pos c.h_pos (add_pos c.p_pos c.h_pos)
  -- eventually the tail bound is small
  have hlim : Tendsto (fun n : ℕ => Real.exp (-(κ * n)) + C2 / n) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.exp (-(κ * n))) atTop (nhds 0) := by
      have : (fun n : ℕ => Real.exp (-(κ * n))) = fun n : ℕ => Real.exp (-κ) ^ n := by
        ext n; rw [← Real.exp_nat_mul]; ring_nf
      rw [this]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le
        (Real.exp_lt_one_iff.2 (by linarith))
    simpa using h1.add (tendsto_const_div_atTop_nhds_zero_nat C2)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hthr))
  refine ⟨max N0 1, by omega, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsmall := hN0 n (le_of_max_le_left hn)
  set K := ⌊(1 + δ) * (n : ℝ)⌋₊ with hK
  have hK1 : (K : ℝ) ≤ (1 + δ) * n := Nat.floor_le (by positivity)
  have hK2 : (1 + δ) * (n : ℝ) < K + 1 := Nat.lt_floor_add_one _
  set y := k * μ * n with hy
  have hlaw : (P n).law = (popSampleLaw Dh X).map (compoundDemand n) := hP n hn1
  -- split of the tail event
  have hA : MeasurableSet {x : ℕ → ℝ≥0 | S (K + 1) x ≤ n} :=
    measurableSet_le (meas_S _) measurable_const
  have hB : MeasurableSet {x : ℕ → ℝ≥0 | y ≤ S K x} := measurableSet_le measurable_const (meas_S _)
  have htail : (P n).law.real {x : ℝ≥0 | y < (x : ℝ)} ≤
      (interarrivalSeqLaw X).real {x | S (K + 1) x ≤ n} + (seq Dh.law).real {x | y ≤ S K x} := by
    have hmeas : MeasurableSet {x : ℝ≥0 | y < (x : ℝ)} :=
      measurableSet_lt measurable_const (by fun_prop)
    rw [hlaw, map_measureReal_apply (measurable_compound n) hmeas]
    have hsub : compoundDemand n ⁻¹' {x : ℝ≥0 | y < (x : ℝ)} ⊆
        Prod.snd ⁻¹' {x | S (K + 1) x ≤ n} ∪ Prod.fst ⁻¹' {x | y ≤ S K x} := by
      intro ω hω
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
      by_cases h : S (K + 1) ω.2 ≤ n
      · exact Or.inl h
      · right; push Not at h
        have := compound_le n ω K h; linarith
    calc _ ≤ (popSampleLaw Dh X).real (Prod.snd ⁻¹' {x | S (K + 1) x ≤ n} ∪
          Prod.fst ⁻¹' {x | y ≤ S K x}) := measureReal_mono hsub
      _ ≤ (popSampleLaw Dh X).real (Prod.snd ⁻¹' {x | S (K + 1) x ≤ n}) +
          (popSampleLaw Dh X).real (Prod.fst ⁻¹' {x | y ≤ S K x}) := measureReal_union_le _ _
      _ = _ := by
          rw [← map_measureReal_apply measurable_snd hA, ← map_measureReal_apply measurable_fst hB,
            map_snd, map_fst]
  -- renewal lower deviation
  have hpart1 : (interarrivalSeqLaw X).real {x | S (K + 1) x ≤ n} ≤ Real.exp (-(κ * n)) := by
    have hlt := lower_tail X.law (K + 1) n hl0.le
    have hlap := lap_neg_le X.law h1X h2X hl0.le
    rw [X.mean_eq_one] at hlap
    have hlap0 : 0 ≤ lap X.law (-l) := lap_nonneg _ _
    have hlap2 : lap X.law (-l) ≤ Real.exp (-(l * (1 - l * M2))) := by
      have := Real.add_one_le_exp (-(l * (1 - l * M2)))
      rw [← hM2] at hlap; nlinarith
    have hpow : lap X.law (-l) ^ (K + 1) ≤ Real.exp ((K + 1 : ℕ) * -(l * (1 - l * M2))) := by
      rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ hlap0 hlap2 _
    refine (show (interarrivalSeqLaw X).real {x | S (K + 1) x ≤ n} =
      (seq X.law).real {x | S (K + 1) x ≤ n} from rfl) ▸ hlt.trans ?_
    calc Real.exp (l * n) * lap X.law (-l) ^ (K + 1)
        ≤ Real.exp (l * n) * Real.exp ((K + 1 : ℕ) * -(l * (1 - l * M2))) :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = Real.exp (l * n + (K + 1 : ℕ) * -(l * (1 - l * M2))) := by rw [← Real.exp_add]
      _ ≤ _ := by
          apply Real.exp_le_exp.2
          push_cast
          have hq : 1 + δ / 2 ≤ (1 + δ) * (1 - l * M2) := by
            have : (1 + δ) * (l * M2) ≤ δ / 2 := by
              calc (1 + δ) * (l * M2) ≤ (1 + δ) * (δ / (2 * (1 + δ))) :=
                    mul_le_mul_of_nonneg_left hlM (by positivity)
                _ = δ / 2 := by field_simp
            nlinarith
          have h8 : 0 ≤ 1 - l * M2 := by
            have : δ / (2 * (1 + δ)) ≤ 1 := by
              rw [div_le_one (by positivity)]; linarith
            linarith
          have p1 := mul_le_mul_of_nonneg_left hK2.le (mul_nonneg hl0.le h8)
          have p2 := mul_le_mul_of_nonneg_left hq (mul_nonneg hl0.le hnpos.le)
          rw [hκ]
          nlinarith [p1, p2]
  -- Chebyshev for customer demands
  have hpart2 : (seq Dh.law).real {x | y ≤ S K x} ≤ C2 / n := by
    have hKy : (K : ℝ) * (∫ y : ℝ≥0, (y : ℝ) ∂Dh.law) < y := by
      change (K : ℝ) * μ < k * μ * n
      have : (K : ℝ) < k * n := by
        have : (1 + δ) * (n : ℝ) < k * n := by
          apply mul_lt_mul_of_pos_right _ hnpos; rw [hδ]; linarith
        linarith
      nlinarith
    have hc := cheb Dh.law h1D h2D K y hKy
    refine hc.trans ?_
    change (K : ℝ) * σ2 / (y - K * μ) ^ 2 ≤ C2 / n
    have hgap : δ * n * μ ≤ y - K * μ := by
      have := mul_le_mul_of_nonneg_right hK1 hμ.le
      have hk' : k = 1 + 2 * δ := by rw [hδ]; ring
      rw [hy, hk']; linarith
    have hgap0 : 0 < δ * n * μ := by positivity
    calc (K : ℝ) * σ2 / (y - K * μ) ^ 2 ≤ (1 + δ) * n * σ2 / (δ * n * μ) ^ 2 := by
          apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hK1 hσ0) (by positivity)
          exact pow_le_pow_left₀ hgap0.le hgap 2
      _ = _ := by rw [hC2]; field_simp
  have hT0 : 0 ≤ y := by positivity
  exact nv_le_of_tail (P n).law c.h_pos c.p_pos y hT0
    ((htail.trans (add_le_add hpart1 hpart2)).trans hsmall.le)
