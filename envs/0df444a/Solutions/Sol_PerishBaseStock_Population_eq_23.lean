-- Prove2me | solution 1 for PerishBaseStock.Population.eq_23
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T23:07:59.562987+00:00
-- url     : https://prove2.me/submissions/74d2928d-51a5-41cb-ba2d-d99626e0fcc5

import Definitions.Def_PerishBaseStock_Population_Model
import Definitions.Def_PerishBaseStock_Population_CompoundDemand
import Theorems.Thm_PerishBaseStock_Lifetime_theorem_1

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

end Pop2T
end

noncomputable section
namespace Pop2B
open PerishBaseStock

variable {m : ℕ}

/-- Embedding of a `ℝ≥0`-valued state into the `ℝ`-valued state space. -/
def toL (x : Population.State m) : Lifetime.State m := fun j => (x j : ℝ)

theorem topLevel_toL (x : Population.State m) :
    Lifetime.topLevel (toL x) = (Population.topLevel x : ℝ) := by
  unfold Lifetime.topLevel Population.topLevel toL
  split_ifs <;> simp

theorem firstLevel_toL (x : Population.State m) (q : ℝ≥0) :
    Lifetime.firstLevel (toL x) q = (Population.level x q 1 : ℝ) := by
  unfold Lifetime.firstLevel Population.level Lifetime.orderUpTo
  by_cases hm : 1 < m
  · have h1 : 0 < m - 1 := by omega
    rw [dif_pos h1, dif_pos hm, dif_pos le_rfl]; rfl
  · have h1 : ¬ 0 < m - 1 := by omega
    rw [dif_neg h1, dif_neg hm, topLevel_toL]; push_cast; rfl

theorem levelAbove_toL (x : Population.State m) (q : ℝ≥0) (j : Fin (m - 1)) :
    Lifetime.levelAbove (toL x) q j = (Population.level x q (j.val + 2) : ℝ) := by
  unfold Lifetime.levelAbove Population.level Lifetime.orderUpTo
  by_cases hm : j.val + 1 < m - 1
  · have h1 : j.val + 2 < m := by omega
    rw [dif_pos hm, dif_pos h1, dif_pos (by omega : 1 ≤ j.val + 2)]; rfl
  · have h1 : ¬ j.val + 2 < m := by omega
    rw [dif_neg hm, dif_neg h1, topLevel_toL]; push_cast; rfl

theorem outdate_toL (x : Population.State m) (q d : ℝ≥0) :
    Lifetime.outdate (toL x) q d = (Population.outdate x q d : ℝ) := by
  unfold Lifetime.outdate Population.outdate
  rw [firstLevel_toL, NNReal.coe_sub_def]

theorem step_toL (x : Population.State m) (q d : ℝ≥0) :
    Lifetime.step (toL x) q d = toL (Population.next x q d) := by
  funext j
  unfold Lifetime.step
  simp only [toL, Population.next]
  rw [levelAbove_toL, outdate_toL]
  rw [NNReal.coe_sub_def, NNReal.coe_sub_def]
  have ho : (0 : ℝ) ≤ (Population.outdate x q d : ℝ) := NNReal.coe_nonneg _
  rcases le_total ((Population.level x q (j.val + 2) : ℝ) - d) 0 with h | h
  · rw [max_eq_right h]
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
  · rw [max_eq_left h]

theorem upTo_eq (x : Population.State m) (q : ℝ≥0) :
    Lifetime.orderUpTo (toL x) q = (Population.level x q m : ℝ) := by
  unfold Lifetime.orderUpTo Population.level
  rw [dif_neg (lt_irrefl m), topLevel_toL]; push_cast; rfl

/-- Trajectories of corresponding policies agree. -/
theorem run_toL (π : Population.Policy m) (π' : Lifetime.Policy m)
    (hφ : ∀ t x, π'.φ t (toL x) = π.φ t x) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    Lifetime.run π' d t = toL (Population.run π d t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show Lifetime.step (Lifetime.runFrom (Lifetime.emptyState m) π' d t)
        (π'.φ t (Lifetime.runFrom (Lifetime.emptyState m) π' d t)) (d t) = _
    change Lifetime.run π' d t = _ at ih
    unfold Lifetime.run at ih
    rw [ih, hφ, step_toL]; rfl

theorem periodCost_eq (c : Lifetime.Params) (π : Population.Policy c.m) (π' : Lifetime.Policy c.m)
    (hφ : ∀ t x, π'.φ t (toL x) = π.φ t x) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    Lifetime.periodCost c π' d t = Population.policyPeriodCost c π t d := by
  unfold Lifetime.periodCost Population.policyPeriodCost Population.periodCost Lifetime.upTo
    Lifetime.outdated Lifetime.outdateFrom
  have hr := run_toL π π' hφ d t
  have hr2 : Lifetime.runFrom (Lifetime.emptyState c.m) π' d t = toL (Population.run π d t) := hr
  rw [hr]
  try rw [hr2]
  rw [hφ, upTo_eq, outdate_toL]
  have hh := c.h_pos.le
  have hp := c.p_pos.le
  have hθ := c.θ_nonneg
  rw [ENNReal.ofReal_mul hh, ENNReal.ofReal_mul hp, ENNReal.ofReal_mul hθ]
  rw [← NNReal.coe_sub_def, ← NNReal.coe_sub_def]
  simp only [ENNReal.ofReal_coe_nnreal]

theorem policyCost_eq (P : CappedBaseStock.DemandLaw) (c : Lifetime.Params)
    (π : Population.Policy c.m) (π' : Lifetime.Policy c.m)
    (hφ : ∀ t x, π'.φ t (toL x) = π.φ t x) :
    Lifetime.policyCost P c π' = Population.policyCost P c π := by
  unfold Lifetime.policyCost Lifetime.cesaroLimsup Population.policyCost
  simp only [periodCost_eq c π π' hφ]

/-- Every policy of the `ℝ≥0`-state model is simulated by a policy of the `ℝ`-state model. -/
def liftPolicy (π : Population.Policy m) : Lifetime.Policy m where
  φ t x := π.φ t (fun j => (x j).toNNReal)
  measurable_φ t := (π.measurable_φ t).comp
    (measurable_pi_lambda _ fun j => (measurable_pi_apply j).real_toNNReal)

theorem liftPolicy_spec (π : Population.Policy m) (t : ℕ) (x : Population.State m) :
    (liftPolicy π).φ t (toL x) = π.φ t x := by
  simp [liftPolicy, toL]

theorem OPT_le (P : CappedBaseStock.DemandLaw) (c : Lifetime.Params) :
    Lifetime.OPT P c ≤ Population.OPT P c := by
  unfold Population.OPT
  refine le_iInf fun π => ?_
  rw [← policyCost_eq P c π (liftPolicy π) (liftPolicy_spec π)]
  exact iInf_le _ _

theorem baseStock_spec (S : ℝ≥0) (t : ℕ) (x : Population.State m) :
    (Lifetime.baseStock m S).φ t (toL x) = (Population.baseStockPolicy m S).φ t x := by
  simp only [Lifetime.baseStock, Population.baseStockPolicy, topLevel_toL]
  apply NNReal.coe_injective
  simp only [Real.coe_toNNReal', NNReal.coe_sub_def]

theorem bsCost_eq (P : CappedBaseStock.DemandLaw) (c : Lifetime.Params) (S : ℝ≥0) :
    Lifetime.bsCost P c S = Population.baseStockCost P c S :=
  policyCost_eq P c _ _ (baseStock_spec S)

end Pop2B
end

open Pop2T Pop2B PerishBaseStock.Population in
theorem solution (c : PerishBaseStock.Lifetime.Params) (Dh : CustomerLaw) (X : InterarrivalLaw)
    (hμ : 0 < customerMean Dh)
    (P : ℕ → CappedBaseStock.DemandLaw) (hP : IsPopulationFamily Dh X P)
    (n : ℕ) (hn : 1 ≤ n) (lam : ℝ) (hlam : 0 < lam)
    (S : ℝ≥0) (hS : PerishBaseStock.Lifetime.IsHeuristicLevel (P n) c S) :
    baseStockCost (P n) c S ≤
      OPT (P n) c + ENNReal.ofReal
        (((c.m : ℝ) - 1) * c.θ / (lam * (c.m : ℝ) * Real.exp 1) *
          (Real.exp ((1 / (c.m : ℝ)) * lam * (newsvendorLevel (P n) c : ℝ)) *
            ∫ ω, Real.exp (-(lam * (compoundDemand n ω : ℝ))) ∂popSampleLaw Dh X) ^ c.m) := by
  have h1 := PerishBaseStock.Lifetime.theorem_1 (P n) c lam hlam S hS
  rw [bsCost_eq] at h1
  have hlaw : (P n).law = (popSampleLaw Dh X).map (compoundDemand n) := hP n hn
  have hint : ∫ x : ℝ≥0, Real.exp (-(lam * (x : ℝ))) ∂(P n).law =
      ∫ ω, Real.exp (-(lam * (compoundDemand n ω : ℝ))) ∂popSampleLaw Dh X := by
    rw [hlaw, integral_map (measurable_compound n).aemeasurable (by fun_prop)]
  have hm0 : (c.m : ℝ) ≠ 0 := by have := c.one_le_m; positivity
  have hpow : (Real.exp ((1 / (c.m : ℝ)) * lam * (newsvendorLevel (P n) c : ℝ)) *
      ∫ ω, Real.exp (-(lam * (compoundDemand n ω : ℝ))) ∂popSampleLaw Dh X) ^ c.m =
      Real.exp (lam * (PerishBaseStock.Lifetime.newsvendorNP (P n) c : ℝ)) *
        (∫ x : ℝ≥0, Real.exp (-(lam * (x : ℝ))) ∂(P n).law) ^ c.m := by
    rw [mul_pow, ← Real.exp_nat_mul, hint]
    congr 2
    unfold PerishBaseStock.Lifetime.newsvendorNP newsvendorLevel
    field_simp
  rw [hpow, ← mul_assoc]
  exact h1.trans (add_le_add (OPT_le (P n) c) le_rfl)
