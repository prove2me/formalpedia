-- Prove2me | solution 1 for PerishBaseStock.Population.step1_claim
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T22:58:23.853508+00:00
-- url     : https://prove2.me/submissions/b9427613-917b-48e3-8c66-b3570b29573b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_PerishBaseStock_Population_Model
import Definitions.Def_PerishBaseStock_Population_CompoundDemand
import Theorems.Thm_PerishBaseStock_Population_eq_EC_6
import Theorems.Thm_PerishBaseStock_Population_eq_EC_7
import Theorems.Thm_PerishBaseStock_Population_renewal_limits

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

namespace Pop2T
open PerishBaseStock.Population

/-- `E[D(n)]` and `Var[D(n)]` of the law `P n` in terms of the renewal count. -/
theorem mean_var_P (Dh : CustomerLaw) (X : InterarrivalLaw)
    (hμ : 0 < customerMean Dh)
    (P : ℕ → CappedBaseStock.DemandLaw) (hP : IsPopulationFamily Dh X P) (n : ℕ) (hn : 1 ≤ n) :
    CappedBaseStock.mean (P n) = customerMean Dh *
        ∫ x, ((arrivalCount n x).toNat : ℝ) ∂interarrivalSeqLaw X ∧
    variance (fun x : ℝ≥0 => (x : ℝ)) (P n).law =
      customerVariance Dh * ∫ x, ((arrivalCount n x).toNat : ℝ) ∂interarrivalSeqLaw X +
        customerMean Dh ^ 2 *
          variance (fun x => ((arrivalCount n x).toNat : ℝ)) (interarrivalSeqLaw X) := by
  obtain ⟨_, _, hE, hV⟩ := PerishBaseStock.Population.eq_EC_7 Dh X hμ n hn
  have hlaw : (P n).law = (popSampleLaw Dh X).map (compoundDemand n) := hP n hn
  have hEN : ∫ ω, ((arrivalCount n ω.2).toNat : ℝ) ∂popSampleLaw Dh X =
      ∫ x, ((arrivalCount n x).toNat : ℝ) ∂interarrivalSeqLaw X :=
    integral_snd Dh X _ (measurable_countNat n).aestronglyMeasurable
  have hVN : variance (fun ω : PopSample => ((arrivalCount n ω.2).toNat : ℝ)) (popSampleLaw Dh X) =
      variance (fun x => ((arrivalCount n x).toNat : ℝ)) (interarrivalSeqLaw X) := by
    have := variance_map (μ := popSampleLaw Dh X) (Y := Prod.snd)
      (X := fun x : ℕ → ℝ≥0 => ((arrivalCount n x).toNat : ℝ))
      (by rw [map_snd]; exact (measurable_countNat n).aemeasurable) measurable_snd.aemeasurable
    rw [map_snd] at this
    rw [this]; rfl
  constructor
  · unfold CappedBaseStock.mean
    rw [hlaw, integral_map (measurable_compound n).aemeasurable
      (by fun_prop : Measurable fun x : ℝ≥0 => (x : ℝ)).aestronglyMeasurable, hE, hEN]
  · rw [hlaw, variance_map (by fun_prop) (measurable_compound n).aemeasurable]
    change variance (fun ω : PopSample => (compoundDemand n ω : ℝ)) (popSampleLaw Dh X) = _
    rw [hV, hEN, hVN]

end Pop2T

open Pop2T PerishBaseStock.Population in
theorem solution (c : PerishBaseStock.Lifetime.Params) (Dh : CustomerLaw) (X : InterarrivalLaw)
    (hμ : 0 < customerMean Dh)
    (P : ℕ → CappedBaseStock.DemandLaw) (hP : IsPopulationFamily Dh X P)
    (k : ℝ) (hk : 1 < k) :
    ∃ n₁ : ℕ, 0 < n₁ ∧ ∀ n : ℕ, n₁ ≤ n →
      (newsvendorLevel (P n) c : ℝ) ≤ k * customerMean Dh * (n : ℝ) := by
  obtain ⟨hL1, hL2⟩ := PerishBaseStock.Population.renewal_limits X
  set μ := customerMean Dh
  set σ2 := customerVariance Dh
  set e : ℕ → ℝ := fun n => ∫ x, ((arrivalCount n x).toNat : ℝ) ∂interarrivalSeqLaw X with he
  set v : ℕ → ℝ := fun n =>
    variance (fun x => ((arrivalCount n x).toNat : ℝ)) (interarrivalSeqLaw X) with hv
  set f : ℕ → ℝ := fun n => μ * (e n / n) +
    Real.sqrt (c.p * (σ2 * (e n / n) + μ ^ 2 * (v n / n)) / c.h) * (Real.sqrt n)⁻¹ with hf
  have hinv : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hlim : Tendsto f atTop (nhds μ) := by
    have h1 : Tendsto (fun n : ℕ => μ * (e n / n)) atTop (nhds (μ * 1)) :=
      tendsto_const_nhds.mul hL1
    have h2 : Tendsto (fun n : ℕ => Real.sqrt (c.p * (σ2 * (e n / n) + μ ^ 2 * (v n / n)) / c.h) *
        (Real.sqrt n)⁻¹) atTop (nhds (Real.sqrt (c.p * (σ2 * 1 + μ ^ 2 *
          interarrivalVariance X) / c.h) * 0)) := by
      refine Tendsto.mul ?_ hinv
      refine (Real.continuous_sqrt.tendsto _).comp ?_
      exact ((tendsto_const_nhds.mul ((tendsto_const_nhds.mul hL1).add
        (tendsto_const_nhds.mul hL2))).div_const _)
    have := h1.add h2
    simpa using this
  have hev : ∀ᶠ n in atTop, f n < k * μ := (tendsto_order.1 hlim).2 _ (by nlinarith)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨max N0 1, by omega, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hfn := hN0 n (le_of_max_le_left hn)
  obtain ⟨hmean, hvar⟩ := mean_var_P Dh X hμ P hP n hn1
  have h6 := PerishBaseStock.Population.eq_EC_6 c Dh X hμ P hP n hn1
  rw [hmean, hvar] at h6
  have heq : μ * e n + Real.sqrt (c.p * (σ2 * e n + μ ^ 2 * v n) / c.h) = n * f n := by
    simp only [hf]
    have hB : c.p * (σ2 * e n + μ ^ 2 * v n) / c.h =
        (n : ℝ) * (c.p * (σ2 * (e n / n) + μ ^ 2 * (v n / n)) / c.h) := by
      field_simp
    rw [hB, Real.sqrt_mul hnpos.le]
    have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
    have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
    generalize Real.sqrt (c.p * (σ2 * (e n / n) + μ ^ 2 * (v n / n)) / c.h) = Q
    have h1' : (n : ℝ) * (μ * (e n / n)) = μ * e n := by field_simp
    have h2' : (n : ℝ) * (Q * (Real.sqrt n)⁻¹) = Real.sqrt n * Q := by
      rw [show (n : ℝ) * (Q * (Real.sqrt n)⁻¹) =
        (Real.sqrt n * Real.sqrt n) * (Q * (Real.sqrt n)⁻¹) by rw [hs]]
      field_simp
    rw [mul_add, h1', h2']
  calc (newsvendorLevel (P n) c : ℝ) ≤ μ * e n + Real.sqrt (c.p * (σ2 * e n + μ ^ 2 * v n) / c.h) :=
        h6
    _ = n * f n := heq
    _ ≤ n * (k * μ) := mul_le_mul_of_nonneg_left hfn.le hnpos.le
    _ = k * μ * n := by ring
