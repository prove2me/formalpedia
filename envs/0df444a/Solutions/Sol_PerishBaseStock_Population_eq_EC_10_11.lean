-- Prove2me | solution 1 for PerishBaseStock.Population.eq_EC_10_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T22:46:05.495231+00:00
-- url     : https://prove2.me/submissions/b38a850b-a8a7-430a-80aa-c688767345d0

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

end Pop2T
end

open Pop2T in
theorem solution (X : PerishBaseStock.Population.InterarrivalLaw) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ δ : ℝ, 0 < δ → δ < ν →
      ∀ n : ℕ, 2 * (1 + δ) / δ ≤ (n : ℝ) →
        PerishBaseStock.Population.interarrivalSeqLaw X
            {x | ∃ N : ℕ, PerishBaseStock.Population.arrivalCount n x = (N : ℕ∞) ∧
              (N : ℝ) < (n : ℝ) / (1 + δ)} ≤
          ENNReal.ofReal (Real.exp (-(δ ^ 2 * (n : ℝ) / (8 * (1 + δ) ^ 2 * ν ^ 2)))) := by
  obtain ⟨s0, hs0, he⟩ := X.exp_moment
  have h1 : Integrable (fun x : ℝ≥0 => (x : ℝ)) X.law := X.memLp_two.integrable one_le_two
  set C : ℝ := 32 / s0 ^ 2 * ∫ x : ℝ≥0, Real.exp (s0 * x) ∂X.law with hC
  have hC0 : 0 ≤ C := mul_nonneg (by positivity) (integral_nonneg fun _ => (Real.exp_pos _).le)
  set A : ℝ := C + 1 / s0 + 1 with hA
  have hA0 : 0 < A := by positivity
  refine ⟨Real.sqrt (2 * A), Real.sqrt_pos.2 (by positivity), ?_⟩
  intro δ hδ _ n hn
  have hν2 : Real.sqrt (2 * A) ^ 2 = 2 * A := Real.sq_sqrt (by positivity)
  set r : ℝ := δ / (1 + δ) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one (by linarith)]; linarith
  have hnr : 2 ≤ (n : ℝ) * r := by
    rw [hr, mul_div_assoc']
    rw [le_div_iff₀ (by linarith)]
    rw [div_le_iff₀ hδ] at hn; linarith
  set s : ℝ := r / (4 * A) with hs
  have hs0' : 0 ≤ s := by positivity
  have hsA : s * A = r / 4 := by rw [hs]; field_simp
  have hss : s ≤ s0 / 2 := by
    have hA1 : 1 / s0 ≤ A := by rw [hA]; linarith
    have : s * (1 / s0) ≤ s * A := mul_le_mul_of_nonneg_left hA1 hs0'
    rw [hsA] at this
    have : s ≤ r / 4 * s0 := by
      rw [mul_one_div, div_le_iff₀ hs0] at this; linarith
    nlinarith
  have hlap : lap X.law s ≤ Real.exp (s + s ^ 2 * A) := by
    have := lap_pos_le X.law h1 hs0 he hs0' hss
    rw [X.mean_eq_one] at this
    calc lap X.law s ≤ 1 + (s + s ^ 2 * A) := by
          have hCA : C ≤ A := by rw [hA]; have := one_div_pos.2 hs0; linarith
          have : s ^ 2 * C ≤ s ^ 2 * A := mul_le_mul_of_nonneg_left hCA (sq_nonneg s)
          nlinarith
      _ ≤ _ := by linarith [Real.add_one_le_exp (s + s ^ 2 * A)]
  set k0 : ℕ := ⌈(n : ℝ) / (1 + δ)⌉₊ with hk0
  have hq0 : 0 ≤ (n : ℝ) / (1 + δ) := by positivity
  have hk0lt : (k0 : ℝ) < (n : ℝ) / (1 + δ) + 1 := Nat.ceil_lt_add_one hq0
  have hq : (n : ℝ) / (1 + δ) = n - n * r := by rw [hr]; field_simp; ring
  have hsub : {x | ∃ N : ℕ, PerishBaseStock.Population.arrivalCount n x = (N : ℕ∞) ∧
      (N : ℝ) < (n : ℝ) / (1 + δ)} ⊆ {x | (n : ℝ) ≤ S k0 x} := by
    rintro x ⟨N, hN, hNlt⟩
    have h1 := lt_S_succ_of_count n x N hN
    have hNk : N + 1 ≤ k0 := by
      have : (N : ℝ) < k0 := hNlt.trans_le (Nat.le_ceil _)
      exact_mod_cast this
    exact (h1.trans_le (S_mono x hNk)).le
  have hint : Integrable (fun x : ℝ≥0 => Real.exp (s * x)) X.law :=
    integrable_exp_of_le X.law hs0' (by linarith) he
  have hT := upper_tail X.law k0 (n : ℝ) hs0' hint
  have hbound : Real.exp (-s * n) * lap X.law s ^ k0 ≤
      Real.exp (-(δ ^ 2 * (n : ℝ) / (8 * (1 + δ) ^ 2 * Real.sqrt (2 * A) ^ 2))) := by
    calc Real.exp (-s * n) * lap X.law s ^ k0
        ≤ Real.exp (-s * n) * Real.exp (s + s ^ 2 * A) ^ k0 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (lap_nonneg _ _) hlap _)
            (Real.exp_pos _).le
      _ = Real.exp (-s * n + k0 * (s + s ^ 2 * A)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ ≤ _ := by
          apply Real.exp_le_exp.2
          rw [hν2]
          have e1 : δ ^ 2 * (n : ℝ) / (8 * (1 + δ) ^ 2 * (2 * A)) = n * r ^ 2 / (16 * A) := by
            rw [hr]; field_simp; ring
          rw [e1]
          have hkn : (k0 : ℝ) ≤ n := by linarith
          have hgap : (n : ℝ) * r / 2 ≤ n - k0 := by linarith
          have hsq : (k0 : ℝ) * (s ^ 2 * A) ≤ n * (s ^ 2 * A) :=
            mul_le_mul_of_nonneg_right hkn (by positivity)
          have hlin : s * ((n : ℝ) * r / 2) ≤ s * (n - k0) := mul_le_mul_of_nonneg_left hgap hs0'
          have key : -s * n + k0 * (s + s ^ 2 * A) ≤ - (s * ((n : ℝ) * r / 2)) + n * (s ^ 2 * A) := by
            nlinarith
          have e2 : - (s * ((n : ℝ) * r / 2)) + n * (s ^ 2 * A) = -(n * r ^ 2 / (16 * A)) := by
            rw [hs]; field_simp; ring
          linarith
  calc PerishBaseStock.Population.interarrivalSeqLaw X _
      ≤ PerishBaseStock.Population.interarrivalSeqLaw X {x | (n : ℝ) ≤ S k0 x} := measure_mono hsub
    _ = ENNReal.ofReal ((seq X.law).real {x | (n : ℝ) ≤ S k0 x}) := by
        rw [ofReal_measureReal (measure_ne_top _ _)]; rfl
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hT.trans hbound)
