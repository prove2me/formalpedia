-- Prove2me | solution 1 for VdNSim.Sparse.complex_hoeffding
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T18:13:55.251851+00:00
-- url     : https://prove2.me/submissions/f056f4f6-5001-4e67-9f34-122ec059bb35

import Mathlib
import Definitions.Def_VdNSim_Sparse_Model

noncomputable section

open VdNSim.Sparse

namespace Prove2SwarmSubmission


open scoped BigOperators

namespace ComplexHoeffding.Norm

theorem sqrt_two_pos : 0 < Real.sqrt 2 :=
  Real.sqrt_pos.mpr (by norm_num)

theorem threshold_pos {ε : ℝ} (hε : 0 < ε) : 0 < ε / Real.sqrt 2 :=
  div_pos hε sqrt_two_pos

/-- The sharp deterministic projection bound already present in pinned Mathlib. -/
theorem norm_le_sqrt_two_mul_max (z : ℂ) :
    ‖z‖ ≤ Real.sqrt 2 * max |z.re| |z.im| :=
  Complex.norm_le_sqrt_two_mul_max z

/-- A strict complex deviation forces one of the two sharp projection deviations.
The implication is valid for all real thresholds; positive thresholds are the application. -/
theorem norm_gt_implies_re_or_im (z : ℂ) {ε : ℝ} (h : ε < ‖z‖) :
    ε / Real.sqrt 2 < |z.re| ∨ ε / Real.sqrt 2 < |z.im| := by
  have hmax : ε / Real.sqrt 2 < max |z.re| |z.im| := by
    apply (div_lt_iff₀ sqrt_two_pos).mpr
    calc
      ε < ‖z‖ := h
      _ ≤ Real.sqrt 2 * max |z.re| |z.im| := norm_le_sqrt_two_mul_max z
      _ = max |z.re| |z.im| * Real.sqrt 2 := mul_comm _ _
  exact lt_max_iff.mp hmax

/-- No probability-space or measurability structure is required for this inclusion. -/
theorem bad_event_subset_union {ι : Type*} (Z : ι → ℂ) (ε : ℝ) :
    {i | ε < ‖Z i‖} ⊆
      {i | ε / Real.sqrt 2 < |(Z i).re|} ∪
        {i | ε / Real.sqrt 2 < |(Z i).im|} := by
  intro i hi
  exact norm_gt_implies_re_or_im (Z i) hi

theorem re_mem_Icc (z : ℂ) (hz : ‖z‖ ≤ 1) : z.re ∈ Set.Icc (-1) 1 :=
  abs_le.mp ((Complex.abs_re_le_norm z).trans hz)

theorem im_mem_Icc (z : ℂ) (hz : ‖z‖ ≤ 1) : z.im ∈ Set.Icc (-1) 1 :=
  abs_le.mp ((Complex.abs_im_le_norm z).trans hz)

/-- The unit-disc hypothesis gives both real-valued range hypotheses for Eq. (18). -/
theorem projection_families_mem_Icc {ι : Type*} (Z : ι → ℂ)
    (hZ : ∀ i, ‖Z i‖ ≤ 1) :
    (∀ i, (Z i).re ∈ Set.Icc (-1) 1) ∧
      (∀ i, (Z i).im ∈ Set.Icc (-1) 1) :=
  ⟨fun i => re_mem_Icc (Z i) (hZ i), fun i => im_mem_Icc (Z i) (hZ i)⟩

theorem threshold_sq (ε : ℝ) : (ε / Real.sqrt 2) ^ 2 = ε ^ 2 / 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The literal real Eq. (18) denominator four becomes the desired denominator eight. -/
theorem exponent_at_threshold (a ε : ℝ) :
    -(a * (ε / Real.sqrt 2) ^ 2) / 4 = -(a * ε ^ 2) / 8 := by
  rw [threshold_sq]
  ring

end ComplexHoeffding.Norm


namespace ComplexHoeffding.Union

/-- An ordinary set indicator taking values in the nonnegative reals 0 and 1. -/
theorem indicator_one_nonneg {I : Type*} (A : Set I) (i : I) :
    0 ≤ A.indicator (fun _ => (1 : ℝ)) i := by
  classical
  by_cases hi : i ∈ A
  · simpa only [Set.indicator_of_mem hi] using (show (0 : ℝ) ≤ 1 by norm_num)
  · simpa only [Set.indicator_of_notMem hi] using (le_refl (0 : ℝ))

theorem indicator_one_mono {I : Type*} {A B : Set I} (hAB : A ⊆ B) (i : I) :
    A.indicator (fun _ => (1 : ℝ)) i ≤ B.indicator (fun _ => (1 : ℝ)) i := by
  classical
  by_cases hi : i ∈ A
  · simpa only [Set.indicator_of_mem hi, Set.indicator_of_mem (hAB hi)] using
      (le_refl (1 : ℝ))
  · simpa only [Set.indicator_of_notMem hi] using indicator_one_nonneg B i

/-- The pointwise union estimate uses only the stated event inclusion. -/
theorem indicator_one_le_add_of_subset_union {I : Type*} {A B C : Set I}
    (hABC : A ⊆ B ∪ C) (i : I) :
    A.indicator (fun _ => (1 : ℝ)) i ≤
      B.indicator (fun _ => (1 : ℝ)) i + C.indicator (fun _ => (1 : ℝ)) i := by
  classical
  by_cases hi : i ∈ A
  · rcases hABC hi with hB | hC
    · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hB]
      linarith [indicator_one_nonneg C i]
    · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hC]
      linarith [indicator_one_nonneg B i]
  · rw [Set.indicator_of_notMem hi]
    exact add_nonneg (indicator_one_nonneg B i) (indicator_one_nonneg C i)

/-- Unnormalized finite weighted event mass. No decidability premises are exposed. -/
noncomputable def weightedSum {I : Type*} [Fintype I] (w : I → ℝ) (A : Set I) : ℝ :=
  ∑ i : I, w i * A.indicator (fun _ => (1 : ℝ)) i

theorem weightedSum_nonneg {I : Type*} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (A : Set I) : 0 ≤ weightedSum w A := by
  unfold weightedSum
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (indicator_one_nonneg A i)

theorem weightedSum_mono {I : Type*} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) {A B : Set I} (hAB : A ⊆ B) :
    weightedSum w A ≤ weightedSum w B := by
  unfold weightedSum
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (indicator_one_mono hAB i) (hw i)

/-- Finite nonnegative weighted union bound, without a normalization hypothesis. -/
theorem weightedSum_le_add_of_subset_union {I : Type*} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) {A B C : Set I} (hABC : A ⊆ B ∪ C) :
    weightedSum w A ≤ weightedSum w B + weightedSum w C := by
  unfold weightedSum
  calc
    _ ≤ ∑ i : I, (w i * B.indicator (fun _ => (1 : ℝ)) i +
        w i * C.indicator (fun _ => (1 : ℝ)) i) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_add] using
        mul_le_mul_of_nonneg_left (indicator_one_le_add_of_subset_union hABC i) (hw i)
    _ = _ := Finset.sum_add_distrib

theorem weightedSum_union_le {I : Type*} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (B C : Set I) :
    weightedSum w (B ∪ C) ≤ weightedSum w B + weightedSum w C :=
  weightedSum_le_add_of_subset_union w hw (fun _ h => h)

/-- Combine two independently supplied event bounds. -/
theorem weightedSum_le_of_two_bounds {I : Type*} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) {A B C : Set I} (hABC : A ⊆ B ∪ C)
    {bB bC : ℝ} (hB : weightedSum w B ≤ bB) (hC : weightedSum w C ≤ bC) :
    weightedSum w A ≤ bB + bC :=
  (weightedSum_le_add_of_subset_union w hw hABC).trans (add_le_add hB hC)

/- Literal finite-sum form for a predicate-based probability model. -/
open Classical in
theorem sum_weight_mul_ite_le_add {I : Type*} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (A B C : I → Prop)
    (hABC : ∀ i, A i → B i ∨ C i) :
    (∑ i : I, w i * (if A i then (1 : ℝ) else 0)) ≤
      (∑ i : I, w i * (if B i then (1 : ℝ) else 0)) +
      (∑ i : I, w i * (if C i then (1 : ℝ) else 0)) := by
  have hsub : {i | A i} ⊆ {i | B i} ∪ {i | C i} := fun i hi => hABC i hi
  have hUnion := weightedSum_le_add_of_subset_union w hw hsub
  have hEq (P : I → Prop) :
      weightedSum w {i | P i} = ∑ i : I, w i * (if P i then (1 : ℝ) else 0) := by
    unfold weightedSum
    apply Finset.sum_congr rfl
    intro i _
    by_cases hPi : P i <;> simp [hPi]
  rw [hEq A, hEq B, hEq C] at hUnion
  exact hUnion

end ComplexHoeffding.Union


open scoped BigOperators

namespace ComplexHoeffding.Projections

/-- Real projection commutes with a finite complex sum. -/
theorem re_finset_sum {I : Type*} (s : Finset I) (F : I → ℂ) :
    (∑ i ∈ s, F i).re = ∑ i ∈ s, (F i).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, Complex.add_re, ih]

/-- Imaginary projection commutes with a finite complex sum. -/
theorem im_finset_sum {I : Type*} (s : Finset I) (F : I → ℂ) :
    (∑ i ∈ s, F i).im = ∑ i ∈ s, (F i).im := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, Complex.add_im, ih]

theorem re_real_mul_sum {I : Type*} [Fintype I] (a : ℝ) (F : I → ℂ) :
    ((a : ℂ) * ∑ i, F i).re = a * ∑ i, (F i).re := by
  rw [Complex.mul_re]
  change a * (∑ i, F i).re - 0 * (∑ i, F i).im = _
  rw [zero_mul, sub_zero, re_finset_sum]

theorem im_real_mul_sum {I : Type*} [Fintype I] (a : ℝ) (F : I → ℂ) :
    ((a : ℂ) * ∑ i, F i).im = a * ∑ i, (F i).im := by
  rw [Complex.mul_im]
  change a * (∑ i, F i).im + 0 * (∑ i, F i).re = _
  rw [zero_mul, add_zero, im_finset_sum]

theorem re_weighted_sum {X : Type*} [Fintype X] (p : X → ℝ) (f : X → ℂ) :
    (∑ x, (p x : ℂ) * f x).re = ∑ x, p x * (f x).re := by
  rw [re_finset_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  simp

theorem im_weighted_sum {X : Type*} [Fintype X] (p : X → ℝ) (f : X → ℂ) :
    (∑ x, (p x : ℂ) * f x).im = ∑ x, p x * (f x).im := by
  rw [im_finset_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  simp

/-- A purely algebraic identity for a real-scaled finite sample minus a
real-weighted complex mean. No probability definition is assumed. -/
theorem re_centered_weighted_sample {X I : Type*} [Fintype X] [Fintype I]
    (a : ℝ) (p : X → ℝ) (f : X → ℂ) (xs : I → X) :
    ((a : ℂ) * (∑ i, f (xs i)) - ∑ x, (p x : ℂ) * f x).re =
      a * (∑ i, (f (xs i)).re) - ∑ x, p x * (f x).re := by
  rw [Complex.sub_re, re_real_mul_sum, re_weighted_sum]

theorem im_centered_weighted_sample {X I : Type*} [Fintype X] [Fintype I]
    (a : ℝ) (p : X → ℝ) (f : X → ℂ) (xs : I → X) :
    ((a : ℂ) * (∑ i, f (xs i)) - ∑ x, (p x : ℂ) * f x).im =
      a * (∑ i, (f (xs i)).im) - ∑ x, p x * (f x).im := by
  rw [Complex.sub_im, im_real_mul_sum, im_weighted_sum]

/-- Both sides use Lean's total inverse, so the identity includes K=0. -/
theorem inv_natCast_eq_ofReal_inv (K : ℕ) :
    (K : ℂ)⁻¹ = (((K : ℝ)⁻¹ : ℝ) : ℂ) := by
  simp

theorem re_sample_deviation {X : Type*} [Fintype X]
    (p : X → ℝ) (f : X → ℂ) (K : ℕ) (xs : Fin K → X) :
    ((K : ℂ)⁻¹ * (∑ k, f (xs k)) - ∑ x, (p x : ℂ) * f x).re =
      (K : ℝ)⁻¹ * (∑ k, (f (xs k)).re) - ∑ x, p x * (f x).re := by
  exact (congrArg (fun a : ℂ =>
    (a * (∑ k, f (xs k)) - ∑ x, (p x : ℂ) * f x).re)
    (inv_natCast_eq_ofReal_inv K)).trans
      (re_centered_weighted_sample ((K : ℝ)⁻¹) p f xs)

theorem im_sample_deviation {X : Type*} [Fintype X]
    (p : X → ℝ) (f : X → ℂ) (K : ℕ) (xs : Fin K → X) :
    ((K : ℂ)⁻¹ * (∑ k, f (xs k)) - ∑ x, (p x : ℂ) * f x).im =
      (K : ℝ)⁻¹ * (∑ k, (f (xs k)).im) - ∑ x, p x * (f x).im := by
  exact (congrArg (fun a : ℂ =>
    (a * (∑ k, f (xs k)) - ∑ x, (p x : ℂ) * f x).im)
    (inv_natCast_eq_ofReal_inv K)).trans
      (im_centered_weighted_sample ((K : ℝ)⁻¹) p f xs)

end ComplexHoeffding.Projections


namespace ComplexHoeffding

/-- Combine exactly the literal real Eq. (18) tail bound at ε/√2 for
each projection. The finite-weight model is abstract until its capture. -/
theorem weighted_complex_tail_of_component_tails {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (Z : I → ℂ) (a ε : ℝ)
    (hRe : Union.weightedSum w {i | ε / Real.sqrt 2 < |(Z i).re|} ≤
      2 * Real.exp (-(a * (ε / Real.sqrt 2) ^ 2) / 4))
    (hIm : Union.weightedSum w {i | ε / Real.sqrt 2 < |(Z i).im|} ≤
      2 * Real.exp (-(a * (ε / Real.sqrt 2) ^ 2) / 4)) :
    Union.weightedSum w {i | ε < ‖Z i‖} ≤
      4 * Real.exp (-(a * ε ^ 2) / 8) := by
  calc
    Union.weightedSum w {i | ε < ‖Z i‖} ≤
        2 * Real.exp (-(a * (ε / Real.sqrt 2) ^ 2) / 4) +
          2 * Real.exp (-(a * (ε / Real.sqrt 2) ^ 2) / 4) :=
      Union.weightedSum_le_of_two_bounds w hw
        (Norm.bad_event_subset_union Z ε) hRe hIm
    _ = 4 * Real.exp (-(a * ε ^ 2) / 8) := by
      simp only [Norm.exponent_at_threshold]
      ring

end ComplexHoeffding


/-! Shared finite Hoeffding core for `VdNSim.Sparse.eq_18` and `complex_hoeffding`
(graph-scout %72). Helpers only; this file does not prove either frozen target.

Owner interface: analysis-prover's vdnsim-eq18 INTERFACE.md v1 (sha256 cffbb4e2).

The model is the finite iid product: a sample `xs : Fin K → X` has weight `∏ k, p (xs k)`,
and the probability of an event is `∑ xs, (∏ k, p (xs k)) * (if E xs then 1 else 0)`.
No measurable structure on `X` is assumed by any exported statement.

* `mgf_le_of_mem_Icc`: finite Hoeffding lemma. For a probability vector `p` and a centred `h`
  with values in `[a, b]`, `∑ x, p x * exp (s * h x) ≤ exp (((b - a) / 2) ^ 2 * s ^ 2 / 2)`.
  It is Mathlib's `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` on `PMF.ofFintype`, with `⊤`.
* `sum_prod_exp_eq_pow`: the K-fold product moment generating function.
* `hoeffding_upper`: `P(t ≤ ∑ k, (g (xs k) - μ)) ≤ exp (-(2 t²) / (K (b - a)²))`.
* `hoeffding_abs_gt` (exported last):
  `P(ε < |K⁻¹ ∑ k, g (xs k) - μ|) ≤ 2 exp (-(2 K ε²) / (b - a)²)`. -/

namespace VdNSim.Sparse.GSHoeff

open MeasureTheory ProbabilityTheory

/-- Finite Hoeffding lemma. -/
theorem mgf_le_of_mem_Icc {X : Type*} [Fintype X] (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (h : X → ℝ) {a b : ℝ} (hh : ∀ x, h x ∈ Set.Icc a b)
    (hmean : ∑ x, p x * h x = 0) (s : ℝ) :
    ∑ x, p x * Real.exp (s * h x) ≤ Real.exp (((b - a) / 2) ^ 2 * s ^ 2 / 2) := by
  let _ : MeasurableSpace X := ⊤
  have _ : MeasurableSingletonClass X := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hsum : ∑ x, ENNReal.ofReal (p x) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hp0 x), hp1, ENNReal.ofReal_one]
  have hq : ∀ F : X → ℝ,
      ∫ y, F y ∂(PMF.ofFintype (fun x => ENNReal.ofReal (p x)) hsum).toMeasure =
        ∑ x, p x * F x := by
    intro F
    rw [PMF.integral_eq_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (hp0 x), smul_eq_mul]
  have hm : AEMeasurable h (PMF.ofFintype (fun x => ENNReal.ofReal (p x)) hsum).toMeasure :=
    measurable_from_top.aemeasurable
  have hb : ∀ᵐ y ∂(PMF.ofFintype (fun x => ENNReal.ofReal (p x)) hsum).toMeasure,
      h y ∈ Set.Icc a b := ae_of_all _ hh
  have hc : ∫ y, h y ∂(PMF.ofFintype (fun x => ENNReal.ofReal (p x)) hsum).toMeasure = 0 := by
    rw [hq]
    exact hmean
  have hmgf := (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm hb hc).mgf_le s
  rw [mgf, hq] at hmgf
  have hcoef : (((‖b - a‖₊ / 2) ^ 2 : NNReal) : ℝ) = ((b - a) / 2) ^ 2 := by
    rw [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat,
      div_pow, div_pow, sq_abs]
  rw [hcoef] at hmgf
  exact hmgf

/-- The K-fold product moment generating function. -/
theorem sum_prod_exp_eq_pow {X : Type*} [Fintype X] (p h : X → ℝ) (K : ℕ) (s : ℝ) :
    ∑ xs : Fin K → X, (∏ k, p (xs k)) * Real.exp (s * ∑ k, h (xs k)) =
      (∑ x, p x * Real.exp (s * h x)) ^ K := by
  rw [← Fin.prod_const K (∑ x, p x * Real.exp (s * h x)), Fintype.prod_sum]
  refine Finset.sum_congr rfl fun xs _ => ?_
  rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]

/-- One-sided Hoeffding bound in the finite iid model. -/
theorem hoeffding_upper {X : Type*} [Fintype X] (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (g : X → ℝ) {a b : ℝ} (hg : ∀ x, g x ∈ Set.Icc a b)
    (K : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∑ xs : Fin K → X, (∏ k, p (xs k)) *
        (if t ≤ ∑ k, (g (xs k) - ∑ x, p x * g x) then 1 else 0) ≤
      Real.exp (-(2 * t ^ 2) / ((K : ℝ) * (b - a) ^ 2)) := by
  have hw : ∀ xs : Fin K → X, 0 ≤ ∏ k, p (xs k) := fun xs =>
    Finset.prod_nonneg fun k _ => hp0 (xs k)
  have hmean : ∑ x, p x * (g x - ∑ y, p y * g y) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul, sub_self]
  have hrange : ∀ x, g x - ∑ y, p y * g y ∈
      Set.Icc (a - ∑ y, p y * g y) (b - ∑ y, p y * g y) := fun x =>
    ⟨by linarith [(hg x).1], by linarith [(hg x).2]⟩
  have hwidth : ((b - ∑ y, p y * g y) - (a - ∑ y, p y * g y)) / 2 = (b - a) / 2 := by ring
  have hchern : ∀ s : ℝ, 0 ≤ s →
      ∑ xs : Fin K → X, (∏ k, p (xs k)) *
          (if t ≤ ∑ k, (g (xs k) - ∑ x, p x * g x) then 1 else 0) ≤
        Real.exp (-(s * t) + K * (((b - a) / 2) ^ 2 * s ^ 2 / 2)) := by
    intro s hs
    have hmgf := mgf_le_of_mem_Icc p hp0 hp1 (fun x => g x - ∑ y, p y * g y) hrange hmean s
    rw [hwidth] at hmgf
    have hbase : 0 ≤ ∑ x, p x * Real.exp (s * (g x - ∑ y, p y * g y)) :=
      Finset.sum_nonneg fun x _ => mul_nonneg (hp0 x) (Real.exp_pos _).le
    have hpow : (∑ x, p x * Real.exp (s * (g x - ∑ y, p y * g y))) ^ K ≤
        Real.exp (((b - a) / 2) ^ 2 * s ^ 2 / 2) ^ K := by
      rw [← Fin.prod_const K (∑ x, p x * Real.exp (s * (g x - ∑ y, p y * g y))),
        ← Fin.prod_const K (Real.exp (((b - a) / 2) ^ 2 * s ^ 2 / 2))]
      exact Finset.prod_le_prod (fun _ _ => hbase) (fun _ _ => hmgf)
    calc ∑ xs : Fin K → X, (∏ k, p (xs k)) *
          (if t ≤ ∑ k, (g (xs k) - ∑ x, p x * g x) then 1 else 0)
        ≤ ∑ xs : Fin K → X, (∏ k, p (xs k)) *
            (Real.exp (-(s * t)) * Real.exp (s * ∑ k, (g (xs k) - ∑ x, p x * g x))) := by
          refine Finset.sum_le_sum fun xs _ => mul_le_mul_of_nonneg_left ?_ (hw xs)
          rw [← Real.exp_add]
          split_ifs with hle
          · exact Real.one_le_exp (by nlinarith)
          · exact (Real.exp_pos _).le
      _ = Real.exp (-(s * t)) * ∑ xs : Fin K → X, (∏ k, p (xs k)) *
            Real.exp (s * ∑ k, (g (xs k) - ∑ x, p x * g x)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun xs _ => ?_
          ring
      _ = Real.exp (-(s * t)) * (∑ x, p x * Real.exp (s * (g x - ∑ y, p y * g y))) ^ K := by
          rw [sum_prod_exp_eq_pow p (fun x => g x - ∑ y, p y * g y) K s]
      _ ≤ Real.exp (-(s * t)) * Real.exp (((b - a) / 2) ^ 2 * s ^ 2 / 2) ^ K :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = Real.exp (-(s * t) + K * (((b - a) / 2) ^ 2 * s ^ 2 / 2)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
  by_cases hD : (K : ℝ) * (b - a) ^ 2 = 0
  · rw [hD, div_zero, Real.exp_zero]
    calc ∑ xs : Fin K → X, (∏ k, p (xs k)) *
          (if t ≤ ∑ k, (g (xs k) - ∑ x, p x * g x) then 1 else 0)
        ≤ Real.exp (-(0 * t) + K * (((b - a) / 2) ^ 2 * 0 ^ 2 / 2)) := hchern 0 le_rfl
      _ = 1 := by norm_num
  · have hDpos : 0 < (K : ℝ) * (b - a) ^ 2 :=
      lt_of_le_of_ne (mul_nonneg (Nat.cast_nonneg K) (sq_nonneg _)) (Ne.symm hD)
    have h1 := hchern (4 * t / ((K : ℝ) * (b - a) ^ 2)) (div_nonneg (by linarith) hDpos.le)
    have hsD : 4 * t / ((K : ℝ) * (b - a) ^ 2) * ((K : ℝ) * (b - a) ^ 2) = 4 * t :=
      div_mul_cancel₀ _ hD
    have hexp : -(4 * t / ((K : ℝ) * (b - a) ^ 2) * t) +
        K * (((b - a) / 2) ^ 2 * (4 * t / ((K : ℝ) * (b - a) ^ 2)) ^ 2 / 2) =
          -(2 * t ^ 2) / ((K : ℝ) * (b - a) ^ 2) := by
      have e1 : (K : ℝ) * (((b - a) / 2) ^ 2 * (4 * t / ((K : ℝ) * (b - a) ^ 2)) ^ 2 / 2) =
          4 * t / ((K : ℝ) * (b - a) ^ 2) * ((K : ℝ) * (b - a) ^ 2) *
            (4 * t / ((K : ℝ) * (b - a) ^ 2)) / 8 := by
        ring
      rw [e1, hsD]
      ring
    rw [hexp] at h1
    exact h1

/-- Two-sided Hoeffding bound in the finite iid model. -/
theorem hoeffding_abs_gt {X : Type*} [Fintype X] (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (g : X → ℝ) {a b : ℝ} (hg : ∀ x, g x ∈ Set.Icc a b)
    {K : ℕ} (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) :
    ∑ xs : Fin K → X, (∏ k, p (xs k)) *
        (if ε < |(K : ℝ)⁻¹ * ∑ k, g (xs k) - ∑ x, p x * g x| then 1 else 0) ≤
      2 * Real.exp (-(2 * (K : ℝ) * ε ^ 2) / (b - a) ^ 2) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hK0 : (K : ℝ) ≠ 0 := hKpos.ne'
  have hw : ∀ xs : Fin K → X, 0 ≤ ∏ k, p (xs k) := fun xs =>
    Finset.prod_nonneg fun k _ => hp0 (xs k)
  have hgneg : ∀ x, -g x ∈ Set.Icc (-b) (-a) := fun x =>
    ⟨by linarith [(hg x).2], by linarith [(hg x).1]⟩
  have hup := hoeffding_upper p hp0 hp1 g hg K (t := (K : ℝ) * ε) (by positivity)
  have hdn := hoeffding_upper p hp0 hp1 (fun x => -g x) hgneg K (t := (K : ℝ) * ε)
    (by positivity)
  have hwid : (-a - -b) = b - a := by ring
  rw [hwid] at hdn
  have hexp : -(2 * ((K : ℝ) * ε) ^ 2) / ((K : ℝ) * (b - a) ^ 2) =
      -(2 * (K : ℝ) * ε ^ 2) / (b - a) ^ 2 := by
    rw [show -(2 * ((K : ℝ) * ε) ^ 2) = (K : ℝ) * (-(2 * (K : ℝ) * ε ^ 2)) by ring,
      mul_div_mul_left _ _ hK0]
  rw [hexp] at hup hdn
  have hpt : ∀ xs : Fin K → X,
      (if ε < |(K : ℝ)⁻¹ * ∑ k, g (xs k) - ∑ x, p x * g x| then (1 : ℝ) else 0) ≤
        (if (K : ℝ) * ε ≤ ∑ k, (g (xs k) - ∑ x, p x * g x) then 1 else 0) +
          (if (K : ℝ) * ε ≤ ∑ k, (-g (xs k) - ∑ x, p x * -g x) then 1 else 0) := by
    intro xs
    have hS : (K : ℝ)⁻¹ * ∑ k, g (xs k) - ∑ x, p x * g x =
        (K : ℝ)⁻¹ * ∑ k, (g (xs k) - ∑ x, p x * g x) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_sub, ← mul_assoc, inv_mul_cancel₀ hK0, one_mul]
    have hS' : ∑ k, (-g (xs k) - ∑ x, p x * -g x) = -∑ k, (g (xs k) - ∑ x, p x * g x) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show ∑ x, p x * -g x = -∑ x, p x * g x by
        simp only [mul_neg, Finset.sum_neg_distrib]]
      ring
    rw [hS, hS']
    have hnn1 : (0 : ℝ) ≤
        (if (K : ℝ) * ε ≤ ∑ k, (g (xs k) - ∑ x, p x * g x) then 1 else 0) := by
      split_ifs <;> norm_num
    have hnn2 : (0 : ℝ) ≤
        (if (K : ℝ) * ε ≤ -∑ k, (g (xs k) - ∑ x, p x * g x) then 1 else 0) := by
      split_ifs <;> norm_num
    by_cases h1 : ε < |(K : ℝ)⁻¹ * ∑ k, (g (xs k) - ∑ x, p x * g x)|
    · rw [if_pos h1]
      rw [abs_mul, abs_inv, abs_of_pos hKpos] at h1
      have h2 : (K : ℝ) * ε < |∑ k, (g (xs k) - ∑ x, p x * g x)| := by
        have h3 := mul_lt_mul_of_pos_left h1 hKpos
        rwa [mul_inv_cancel_left₀ hK0] at h3
      rcases le_or_gt 0 (∑ k, (g (xs k) - ∑ x, p x * g x)) with hs | hs
      · rw [abs_of_nonneg hs] at h2
        rw [if_pos h2.le]
        linarith
      · rw [abs_of_neg hs] at h2
        rw [if_pos h2.le]
        linarith
    · rw [if_neg h1]
      linarith
  calc ∑ xs : Fin K → X, (∏ k, p (xs k)) *
        (if ε < |(K : ℝ)⁻¹ * ∑ k, g (xs k) - ∑ x, p x * g x| then 1 else 0)
      ≤ ∑ xs : Fin K → X, (∏ k, p (xs k)) *
          ((if (K : ℝ) * ε ≤ ∑ k, (g (xs k) - ∑ x, p x * g x) then 1 else 0) +
            (if (K : ℝ) * ε ≤ ∑ k, (-g (xs k) - ∑ x, p x * -g x) then 1 else 0)) :=
        Finset.sum_le_sum fun xs _ => mul_le_mul_of_nonneg_left (hpt xs) (hw xs)
    _ = (∑ xs : Fin K → X, (∏ k, p (xs k)) *
            (if (K : ℝ) * ε ≤ ∑ k, (g (xs k) - ∑ x, p x * g x) then 1 else 0)) +
          ∑ xs : Fin K → X, (∏ k, p (xs k)) *
            (if (K : ℝ) * ε ≤ ∑ k, (-g (xs k) - ∑ x, p x * -g x) then 1 else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun xs _ => ?_
        ring
    _ ≤ Real.exp (-(2 * (K : ℝ) * ε ^ 2) / (b - a) ^ 2) +
          Real.exp (-(2 * (K : ℝ) * ε ^ 2) / (b - a) ^ 2) := add_le_add hup hdn
    _ = 2 * Real.exp (-(2 * (K : ℝ) * ε ^ 2) / (b - a) ^ 2) := by ring

end VdNSim.Sparse.GSHoeff


/-!
# Real/imaginary tail interface for `VdNSim.Sparse.complex_hoeffding` (v2, finite-weight form)

Consumes the shared finite-weight Hoeffding tail of analysis-prover's team (interface v1,
`cffbb4e2…`): `VdNSim.Sparse.GSHoeff.hoeffding_abs_gt` (graph-scout), instantiated at
`g := Re ∘ f` (resp. `Im ∘ f`), `a = -1`, `b = 1`, `ε' = ε / √2`. That instance is taken as the
hypothesis `hH`, with exactly its type, so this file is Mathlib-only and independently checkable.
No complement of `sampleProb` is used.

Owner instantiation (after pasting GSHoeff once):
`re_tail_weights p f (expect p f) hReE ε (VdNSim.Sparse.GSHoeff.hoeffding_abs_gt p hp0 hp1
  (fun x => (f x).re) (fun x => re_mem_Icc (hf x)) hK (sqrt_two_pos_div hε))`.
`hReE`/`hImE` (real/imaginary part of `expect`) are discharged after the R1 capture.
proof-reviewer's pointwise norm reduction and indicator union bound, then
`AABridge.sampleProb_eq_weights`, finish `4 * exp(-K ε² / 8)`.
-/

namespace VdNSim.Sparse.ComplexInterface

theorem sqrt_two_pos_div {ε : ℝ} (hε : 0 < ε) : 0 < ε / Real.sqrt 2 :=
  div_pos hε (Real.sqrt_pos.mpr (by norm_num))

theorem re_mem_Icc {z : ℂ} (hz : ‖z‖ ≤ 1) : z.re ∈ Set.Icc (-1 : ℝ) 1 :=
  abs_le.mp ((Complex.abs_re_le_norm z).trans hz)

theorem im_mem_Icc {z : ℂ} (hz : ‖z‖ ≤ 1) : z.im ∈ Set.Icc (-1 : ℝ) 1 :=
  abs_le.mp ((Complex.abs_im_le_norm z).trans hz)

/-- Real part of the empirical mean. -/
theorem re_mean {K : ℕ} (w : Fin K → ℂ) :
    ((K : ℂ)⁻¹ * ∑ k, w k).re = (K : ℝ)⁻¹ * ∑ k, (w k).re := by
  rw [show ((K : ℂ)⁻¹) = (((K : ℝ)⁻¹ : ℝ) : ℂ) by exact ComplexHoeffding.Projections.inv_natCast_eq_ofReal_inv K,
    Complex.re_ofReal_mul,
    Complex.re_sum]

/-- Imaginary part of the empirical mean. -/
theorem im_mean {K : ℕ} (w : Fin K → ℂ) :
    ((K : ℂ)⁻¹ * ∑ k, w k).im = (K : ℝ)⁻¹ * ∑ k, (w k).im := by
  rw [show ((K : ℂ)⁻¹) = (((K : ℝ)⁻¹ : ℝ) : ℂ) by exact ComplexHoeffding.Projections.inv_natCast_eq_ofReal_inv K,
    Complex.im_ofReal_mul,
    Complex.im_sum]

/-- The Hoeffding exponent at `a = -1`, `b = 1`, `ε / √2` is at most the target exponent. -/
theorem exponent_le (K ε : ℝ) (hK : 0 ≤ K) :
    -(2 * K * (ε / Real.sqrt 2) ^ 2) / (1 - (-1)) ^ 2 ≤ -(K * ε ^ 2) / 8 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [mul_nonneg hK (sq_nonneg ε)]

/-- Real-part tail, in finite-weight form. -/
theorem re_tail_weights {X : Type*} [Fintype X] {K : ℕ} (p : X → ℝ) (f : X → ℂ) (E : ℂ)
    (hReE : E.re = ∑ x, p x * (f x).re) (ε : ℝ)
    (hH : ∑ xs : Fin K → X, (∏ k, p (xs k)) *
        (if ε / Real.sqrt 2 < |(K : ℝ)⁻¹ * ∑ k, (f (xs k)).re - ∑ x, p x * (f x).re|
          then 1 else 0) ≤
      2 * Real.exp (-(2 * (K : ℝ) * (ε / Real.sqrt 2) ^ 2) / (1 - (-1)) ^ 2)) :
    ∑ xs : Fin K → X, (∏ k, p (xs k)) *
        (if ε / Real.sqrt 2 < |((K : ℂ)⁻¹ * ∑ k, f (xs k) - E).re| then 1 else 0) ≤
      2 * Real.exp (-((K : ℝ) * ε ^ 2) / 8) := by
  have hsum : ∑ xs : Fin K → X, (∏ k, p (xs k)) *
        (if ε / Real.sqrt 2 < |((K : ℂ)⁻¹ * ∑ k, f (xs k) - E).re| then 1 else 0) =
      ∑ xs : Fin K → X, (∏ k, p (xs k)) *
        (if ε / Real.sqrt 2 < |(K : ℝ)⁻¹ * ∑ k, (f (xs k)).re - ∑ x, p x * (f x).re|
          then 1 else 0) :=
    Finset.sum_congr rfl (fun xs _ => by rw [Complex.sub_re, re_mean, hReE])
  rw [hsum]
  refine hH.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
  exact exponent_le (K : ℝ) ε (Nat.cast_nonneg K)

/-- Imaginary-part tail, in finite-weight form. -/
theorem im_tail_weights {X : Type*} [Fintype X] {K : ℕ} (p : X → ℝ) (f : X → ℂ) (E : ℂ)
    (hImE : E.im = ∑ x, p x * (f x).im) (ε : ℝ)
    (hH : ∑ xs : Fin K → X, (∏ k, p (xs k)) *
        (if ε / Real.sqrt 2 < |(K : ℝ)⁻¹ * ∑ k, (f (xs k)).im - ∑ x, p x * (f x).im|
          then 1 else 0) ≤
      2 * Real.exp (-(2 * (K : ℝ) * (ε / Real.sqrt 2) ^ 2) / (1 - (-1)) ^ 2)) :
    ∑ xs : Fin K → X, (∏ k, p (xs k)) *
        (if ε / Real.sqrt 2 < |((K : ℂ)⁻¹ * ∑ k, f (xs k) - E).im| then 1 else 0) ≤
      2 * Real.exp (-((K : ℝ) * ε ^ 2) / 8) := by
  have hsum : ∑ xs : Fin K → X, (∏ k, p (xs k)) *
        (if ε / Real.sqrt 2 < |((K : ℂ)⁻¹ * ∑ k, f (xs k) - E).im| then 1 else 0) =
      ∑ xs : Fin K → X, (∏ k, p (xs k)) *
        (if ε / Real.sqrt 2 < |(K : ℝ)⁻¹ * ∑ k, (f (xs k)).im - ∑ x, p x * (f x).im|
          then 1 else 0) :=
    Finset.sum_congr rfl (fun xs _ => by rw [Complex.sub_im, im_mean, hImE])
  rw [hsum]
  refine hH.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
  exact exponent_le (K : ℝ) ε (Nat.cast_nonneg K)

end VdNSim.Sparse.ComplexInterface

namespace BacklogCuratorComplexHoeffding

/-- Finite-weight analogue of the exact target. All analytical proof bodies are
included in this source; no imported sampling-model definition is guessed. -/
theorem finite_weight_complex_hoeffding {X : Type*} [Fintype X]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {K : ℕ} (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) :
    (∑ xs : Fin K → X, (∏ k, p (xs k)) *
      (if ε < ‖(K : ℂ)⁻¹ * (∑ k, f (xs k)) - ∑ x, (p x : ℂ) * f x‖
        then (1 : ℝ) else 0)) ≤
      4 * Real.exp (-((K : ℝ) * ε ^ 2) / 8) := by
  classical
  let E : ℂ := ∑ x, (p x : ℂ) * f x
  let Z : (Fin K → X) → ℂ := fun xs =>
    (K : ℂ)⁻¹ * (∑ k, f (xs k)) - E
  have hw : ∀ xs : Fin K → X, 0 ≤ ∏ k, p (xs k) := fun xs =>
    Finset.prod_nonneg fun k _ => hp0 (xs k)
  have hReE : E.re = ∑ x, p x * (f x).re :=
    ComplexHoeffding.Projections.re_weighted_sum p f
  have hImE : E.im = ∑ x, p x * (f x).im :=
    ComplexHoeffding.Projections.im_weighted_sum p f
  have hReCore := VdNSim.Sparse.GSHoeff.hoeffding_abs_gt p hp0 hp1
    (fun x => (f x).re)
    (fun x => VdNSim.Sparse.ComplexInterface.re_mem_Icc (hf x))
    hK (VdNSim.Sparse.ComplexInterface.sqrt_two_pos_div hε)
  have hImCore := VdNSim.Sparse.GSHoeff.hoeffding_abs_gt p hp0 hp1
    (fun x => (f x).im)
    (fun x => VdNSim.Sparse.ComplexInterface.im_mem_Icc (hf x))
    hK (VdNSim.Sparse.ComplexInterface.sqrt_two_pos_div hε)
  have hRe := VdNSim.Sparse.ComplexInterface.re_tail_weights p f E hReE ε hReCore
  have hIm := VdNSim.Sparse.ComplexInterface.im_tail_weights p f E hImE ε hImCore
  have hUnion := ComplexHoeffding.Union.sum_weight_mul_ite_le_add
    (fun xs : Fin K → X => ∏ k, p (xs k)) hw
    (fun xs => ε < ‖Z xs‖)
    (fun xs => ε / Real.sqrt 2 < |(Z xs).re|)
    (fun xs => ε / Real.sqrt 2 < |(Z xs).im|)
    (fun xs h => ComplexHoeffding.Norm.norm_gt_implies_re_or_im (Z xs) h)
  calc
    _ ≤ (∑ xs : Fin K → X, (∏ k, p (xs k)) *
        (if ε / Real.sqrt 2 < |((K : ℂ)⁻¹ * (∑ k, f (xs k)) - E).re|
          then 1 else 0)) +
        ∑ xs : Fin K → X, (∏ k, p (xs k)) *
        (if ε / Real.sqrt 2 < |((K : ℂ)⁻¹ * (∑ k, f (xs k)) - E).im|
          then 1 else 0) := hUnion
    _ ≤ 2 * Real.exp (-((K : ℝ) * ε ^ 2) / 8) +
        2 * Real.exp (-((K : ℝ) * ε ^ 2) / 8) := add_le_add hRe hIm
    _ = 4 * Real.exp (-((K : ℝ) * ε ^ 2) / 8) := by ring

end BacklogCuratorComplexHoeffding


namespace VdNSim.Sparse.AABridge

theorem sampleProb_eq_weights {X : Type*} [Fintype X]
    [_instDecidableEq : DecidableEq X] (p : X → ℝ) (K : ℕ)
    (E : (Fin K → X) → Prop) [DecidablePred E] :
    sampleProb p K E =
      ∑ xs : Fin K → X, (∏ k, p (xs k)) * (if E xs then 1 else 0) := by
  apply Finset.sum_congr rfl
  intro xs _hxs
  by_cases h : E xs
  · simp only [if_pos h]
  · simp only [if_neg h]

end VdNSim.Sparse.AABridge

namespace VdNSim.Sparse

/-- Appendix A, p. 23, the complex-valued consequence of Eq. (18). -/
theorem complex_hoeffding {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {K : ℕ} (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) :
    sampleProb p K (fun xs =>
      ε < ‖(K : ℂ)⁻¹ * ∑ k, f (xs k) - expect p f‖) ≤
      4 * Real.exp (-((K : ℝ) * ε ^ 2) / 8) := by
  classical
  rw [VdNSim.Sparse.AABridge.sampleProb_eq_weights p K
    (fun xs => ε < ‖(K : ℂ)⁻¹ * ∑ k, f (xs k) - expect p f‖)]
  change (∑ xs : Fin K → X, (∏ k, p (xs k)) *
    (if ε < ‖(K : ℂ)⁻¹ * (∑ k, f (xs k)) - ∑ x, (p x : ℂ) * f x‖
      then (1 : ℝ) else 0)) ≤
        4 * Real.exp (-((K : ℝ) * ε ^ 2) / 8)
  exact BacklogCuratorComplexHoeffding.finite_weight_complex_hoeffding
    p hp0 hp1 f hf hK hε

end VdNSim.Sparse


end Prove2SwarmSubmission

theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {K : ℕ} (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) :
    sampleProb p K (fun xs =>
      ε < ‖(K : ℂ)⁻¹ * ∑ k, f (xs k) - expect p f‖) ≤
      4 * Real.exp (-((K : ℝ) * ε ^ 2) / 8) := by
  exact _root_.Prove2SwarmSubmission.VdNSim.Sparse.complex_hoeffding p hp0 hp1 f hf hK hε
