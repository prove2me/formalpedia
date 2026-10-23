-- Prove2me | solution 1 for SubsetShrink.BIC.union_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T00:46:57.037186+00:00
-- url     : https://prove2.me/submissions/6f16c6f4-0a6b-4689-8ddb-b145707cec67

import Mathlib
import Definitions.Def_SubsetShrink_BIC_Model
import Theorems.Thm_SubsetShrink_Events_prob_G_corrected

open MeasureTheory ProbabilityTheory

namespace BICUnionAux

/-- `(s/(e p))^s ≤ e^{-s}` for `1 ≤ s ≤ p`. -/
lemma delta_le_exp {p s : ℕ} (hp : 1 ≤ p) (hsp : s ≤ p) :
    ((s : ℝ) / (Real.exp 1 * p)) ^ s ≤ Real.exp (-(s : ℝ)) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have h0 : 0 ≤ (s : ℝ) / (Real.exp 1 * p) := by positivity
  have h1 : (s : ℝ) / (Real.exp 1 * p) ≤ Real.exp (-1) := by
    rw [div_le_iff₀ (by positivity), Real.exp_neg]
    have : (s : ℝ) ≤ p := by exact_mod_cast hsp
    calc (s : ℝ) ≤ p := this
      _ = (Real.exp 1)⁻¹ * (Real.exp 1 * p) := by field_simp
  calc ((s : ℝ) / (Real.exp 1 * p)) ^ s ≤ (Real.exp (-1)) ^ s := pow_le_pow_left₀ h0 h1 s
    _ = Real.exp (-(s : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf

lemma sum_exp_neg_le (p : ℕ) : ∑ s ∈ Finset.Icc 1 p, Real.exp (-(s : ℝ)) ≤ 1 := by
  have hq : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; linarith
  have key : ∀ m : ℕ, ∑ s ∈ Finset.Icc 1 m, Real.exp (-(s : ℝ)) ≤ 1 - (1 / 2 : ℝ) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have : Real.exp (-((m + 1 : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) ^ (m + 1) := by
        have e1 : Real.exp (-((m + 1 : ℕ) : ℝ)) = (Real.exp (-1)) ^ (m + 1) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
        rw [e1]; exact pow_le_pow_left₀ (Real.exp_pos _).le hq _
      have h2 : (1 / 2 : ℝ) ^ (m + 1) = (1 / 2) ^ m / 2 := by rw [pow_succ]; ring
      rw [h2] at this ⊢
      linarith
  have := key p
  have : (0 : ℝ) ≤ (1 / 2) ^ p := by positivity
  linarith

end BICUnionAux

open BICUnionAux in
theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (σ ϵ0 : ℝ)
    (hX : SubsetShrink.Events.UnitCols X) (hp : 1 ≤ p) (hσ : 0 < σ) (hϵ0 : 0 < ϵ0) (hϵ1 : ϵ0 < 1) :
    MeasurableSet (⋂ s ∈ Finset.Icc 1 p,
        SubsetShrink.Events.Gc X σ (((s : ℝ) / (Real.exp 1 * p)) ^ s * ϵ0) s) ∧
    (SubsetShrink.Events.noiseLaw n σ (⋂ s ∈ Finset.Icc 1 p,
        SubsetShrink.Events.Gc X σ (((s : ℝ) / (Real.exp 1 * p)) ^ s * ϵ0) s)ᶜ).toReal ≤
      ∑ s ∈ Finset.Icc 1 p,
        (SubsetShrink.Events.noiseLaw n σ (SubsetShrink.Events.Gc X σ (((s : ℝ) / (Real.exp 1 * p)) ^ s * ϵ0) s)ᶜ).toReal ∧
    (∀ s ∈ Finset.Icc 1 p,
      (SubsetShrink.Events.noiseLaw n σ (SubsetShrink.Events.Gc X σ (((s : ℝ) / (Real.exp 1 * p)) ^ s * ϵ0) s)ᶜ).toReal ≤
        ((s : ℝ) / (Real.exp 1 * p)) ^ s * ϵ0) ∧
    ∑ s ∈ Finset.Icc 1 p, ((s : ℝ) / (Real.exp 1 * p)) ^ s * ϵ0 ≤
      ∑ s ∈ Finset.Icc 1 p, Real.exp (-(s : ℝ)) * ϵ0 ∧
    ∑ s ∈ Finset.Icc 1 p, Real.exp (-(s : ℝ)) * ϵ0 ≤ ϵ0 ∧
    1 - ϵ0 ≤ (SubsetShrink.Events.noiseLaw n σ (⋂ s ∈ Finset.Icc 1 p,
        SubsetShrink.Events.Gc X σ (((s : ℝ) / (Real.exp 1 * p)) ^ s * ϵ0) s)).toReal := by
  set μ := SubsetShrink.Events.noiseLaw n σ with hμ
  have : IsProbabilityMeasure μ := by
    rw [hμ]; unfold SubsetShrink.Events.noiseLaw
    have hv : ∀ v : NNReal, IsProbabilityMeasure (Measure.pi (fun _ : Fin n => gaussianReal 0 v)) :=
      fun v => inferInstance
    exact hv ⟨σ ^ 2, sq_nonneg σ⟩
  set δ : ℕ → ℝ := fun s => ((s : ℝ) / (Real.exp 1 * p)) ^ s * ϵ0 with hδ
  set G : ℕ → Set (Fin n → ℝ) := fun s => SubsetShrink.Events.Gc X σ (δ s) s with hG
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hδpos : ∀ s ∈ Finset.Icc 1 p, 0 < δ s := by
    intro s hs
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
    have : (0 : ℝ) < s := by exact_mod_cast hs1
    simp only [hδ]; positivity
  have hδle : ∀ s ∈ Finset.Icc 1 p, δ s ≤ Real.exp (-(s : ℝ)) * ϵ0 := by
    intro s hs
    exact mul_le_mul_of_nonneg_right (delta_le_exp hp (Finset.mem_Icc.mp hs).2) hϵ0.le
  have hδ1 : ∀ s ∈ Finset.Icc 1 p, δ s ≤ 1 := by
    intro s hs
    have h1 := hδle s hs
    have : Real.exp (-(s : ℝ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; simp
    have : Real.exp (-(s : ℝ)) * ϵ0 ≤ 1 * 1 :=
      mul_le_mul this hϵ1.le hϵ0.le zero_le_one
    linarith
  have hGs : ∀ s ∈ Finset.Icc 1 p, MeasurableSet (G s) ∧ 1 - δ s ≤ (μ (G s)).toReal := by
    intro s hs
    exact SubsetShrink.Events.prob_G_corrected X hX σ hσ (Finset.mem_Icc.mp hs).1
      (Finset.mem_Icc.mp hs).2 (δ s) (hδpos s hs) (hδ1 s hs)
  have hmeas : MeasurableSet (⋂ s ∈ Finset.Icc 1 p, G s) :=
    Finset.measurableSet_biInter _ (fun s hs => (hGs s hs).1)
  have hcompl : ∀ s ∈ Finset.Icc 1 p, (μ (G s)ᶜ).toReal ≤ δ s := by
    intro s hs
    have := prob_compl_eq_one_sub (μ := μ) (hGs s hs).1
    rw [this, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
    simp only [ENNReal.toReal_one]
    linarith [(hGs s hs).2]
  have hunion : (μ (⋂ s ∈ Finset.Icc 1 p, G s)ᶜ).toReal ≤
      ∑ s ∈ Finset.Icc 1 p, (μ (G s)ᶜ).toReal := by
    rw [Set.compl_iInter₂]
    rw [← ENNReal.toReal_sum (fun s _ => measure_ne_top μ _)]
    exact ENNReal.toReal_mono (by
      exact ne_of_lt (ENNReal.sum_lt_top.mpr (fun s _ => measure_lt_top μ _)))
      (measure_biUnion_finset_le _ _)
  have hsum1 : ∑ s ∈ Finset.Icc 1 p, δ s ≤ ∑ s ∈ Finset.Icc 1 p, Real.exp (-(s : ℝ)) * ϵ0 :=
    Finset.sum_le_sum hδle
  have hsum2 : ∑ s ∈ Finset.Icc 1 p, Real.exp (-(s : ℝ)) * ϵ0 ≤ ϵ0 := by
    rw [← Finset.sum_mul]
    have := sum_exp_neg_le p
    nlinarith
  refine ⟨hmeas, hunion, hcompl, hsum1, hsum2, ?_⟩
  have hc : (μ (⋂ s ∈ Finset.Icc 1 p, G s)ᶜ).toReal ≤ ϵ0 := by
    linarith [Finset.sum_le_sum hcompl]
  have := prob_compl_eq_one_sub (μ := μ) hmeas
  rw [this, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top] at hc
  simp only [ENNReal.toReal_one] at hc
  linarith
