-- Prove2me | solution 1 for VdNSim.Sparse.eq_18
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T18:06:59.451972+00:00
-- url     : https://prove2.me/submissions/69680763-44ad-4d70-848a-a9ace055a9d2

import Mathlib
import Definitions.Def_VdNSim_Sparse_Model

noncomputable section

open VdNSim.Sparse

namespace Prove2SwarmSubmission


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

noncomputable section

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

/-! Owner piece for `VdNSim.Sparse.eq_18` in the finite iid weight model (interface v1).
Compose after `VdNSim.Sparse.GSHoeff` (graph-scout), which exports `hoeffding_abs_gt`. -/

namespace VdNSim.Sparse.Owner18

/-- The iid product weights `∏ k, p (xs k)` of a probability vector have total mass one. -/
theorem weights_sum_one {X : Type*} [Fintype X] (p : X → ℝ) (hp1 : ∑ x, p x = 1) (K : ℕ) :
    ∑ xs : Fin K → X, ∏ k, p (xs k) = 1 := by
  calc ∑ xs : Fin K → X, ∏ k, p (xs k) = ∏ _k : Fin K, ∑ x, p x :=
        (Fintype.prod_sum (fun (_ : Fin K) (x : X) => p x)).symm
    _ = 1 := by rw [hp1, Finset.prod_const_one]

/-- Eq. (18) with the sampling probability written as the finite iid weight sum. -/
theorem eq_18_weights {X : Type*} [Fintype X] (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (f : X → ℝ) (hf : ∀ x, f x ∈ Set.Icc (-1) 1)
    {K : ℕ} (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) :
    1 - 2 * Real.exp (-((K : ℝ) * ε ^ 2) / 4) ≤
      ∑ xs : Fin K → X, (∏ k, p (xs k)) *
        (if |(K : ℝ)⁻¹ * ∑ k, f (xs k) - ∑ x, p x * f x| ≤ ε then 1 else 0) := by
  have htail := GSHoeff.hoeffding_abs_gt p hp0 hp1 f hf hK hε
  have hsplit : ∀ xs : Fin K → X,
      (∏ k, p (xs k)) *
          (if |(K : ℝ)⁻¹ * ∑ k, f (xs k) - ∑ x, p x * f x| ≤ ε then 1 else 0) =
        (∏ k, p (xs k)) - (∏ k, p (xs k)) *
          (if ε < |(K : ℝ)⁻¹ * ∑ k, f (xs k) - ∑ x, p x * f x| then 1 else 0) := by
    intro xs
    by_cases h : |(K : ℝ)⁻¹ * ∑ k, f (xs k) - ∑ x, p x * f x| ≤ ε
    · rw [if_pos h, if_neg (not_lt.mpr h)]
      ring
    · rw [if_neg h, if_pos (not_le.mp h)]
      ring
  have hsum : ∑ xs : Fin K → X, (∏ k, p (xs k)) *
        (if |(K : ℝ)⁻¹ * ∑ k, f (xs k) - ∑ x, p x * f x| ≤ ε then 1 else 0) =
      1 - ∑ xs : Fin K → X, (∏ k, p (xs k)) *
        (if ε < |(K : ℝ)⁻¹ * ∑ k, f (xs k) - ∑ x, p x * f x| then 1 else 0) := by
    calc ∑ xs : Fin K → X, (∏ k, p (xs k)) *
          (if |(K : ℝ)⁻¹ * ∑ k, f (xs k) - ∑ x, p x * f x| ≤ ε then 1 else 0)
        = ∑ xs : Fin K → X, ((∏ k, p (xs k)) - (∏ k, p (xs k)) *
          (if ε < |(K : ℝ)⁻¹ * ∑ k, f (xs k) - ∑ x, p x * f x| then 1 else 0)) :=
          Finset.sum_congr rfl (fun xs _ => hsplit xs)
      _ = (∑ xs : Fin K → X, ∏ k, p (xs k)) - ∑ xs : Fin K → X, (∏ k, p (xs k)) *
          (if ε < |(K : ℝ)⁻¹ * ∑ k, f (xs k) - ∑ x, p x * f x| then 1 else 0) := by
          rw [Finset.sum_sub_distrib]
      _ = 1 - ∑ xs : Fin K → X, (∏ k, p (xs k)) *
          (if ε < |(K : ℝ)⁻¹ * ∑ k, f (xs k) - ∑ x, p x * f x| then 1 else 0) := by
          rw [weights_sum_one p hp1 K]
  have hexp : Real.exp (-(2 * (K : ℝ) * ε ^ 2) / (1 - -1) ^ 2) ≤
      Real.exp (-((K : ℝ) * ε ^ 2) / 4) := by
    apply Real.exp_le_exp.mpr
    have hKε : (0 : ℝ) ≤ (K : ℝ) * ε ^ 2 := mul_nonneg (Nat.cast_nonneg K) (sq_nonneg ε)
    have h4 : ((1 : ℝ) - -1) ^ 2 = 4 := by norm_num
    rw [h4]
    linarith
  rw [hsum]
  linarith

end VdNSim.Sparse.Owner18

namespace VdNSim.Sparse

/-- Appendix A, Eq. (18), in the finite sampling model used by the paper. -/
theorem eq_18 {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (f : X → ℝ) (hf : ∀ x, f x ∈ Set.Icc (-1) 1)
    {K : ℕ} (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) :
    1 - 2 * Real.exp (-((K : ℝ) * ε ^ 2) / 4) ≤
      sampleProb p K (fun xs =>
        |(K : ℝ)⁻¹ * ∑ k, f (xs k) - ∑ x, p x * f x| ≤ ε) := by
  rw [AABridge.sampleProb_eq_weights p K
    (fun xs => |(K : ℝ)⁻¹ * ∑ k, f (xs k) - ∑ x, p x * f x| ≤ ε)]
  exact Owner18.eq_18_weights p hp0 hp1 f hf hK hε

end VdNSim.Sparse

end

end Prove2SwarmSubmission

theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (f : X → ℝ) (hf : ∀ x, f x ∈ Set.Icc (-1) 1)
    {K : ℕ} (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) :
    1 - 2 * Real.exp (-((K : ℝ) * ε ^ 2) / 4) ≤
      sampleProb p K (fun xs =>
        |(K : ℝ)⁻¹ * ∑ k, f (xs k) - ∑ x, p x * f x| ≤ ε) := by
  exact _root_.Prove2SwarmSubmission.VdNSim.Sparse.eq_18 p hp0 hp1 f hf hK hε
