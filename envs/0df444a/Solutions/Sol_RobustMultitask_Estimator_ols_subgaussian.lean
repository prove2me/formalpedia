-- Prove2me | solution 1 for RobustMultitask.Estimator.ols_subgaussian
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T14:19:59.897872+00:00
-- url     : https://prove2.me/submissions/7ad88fc0-f012-48f9-adcd-cd3b05422766

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation
import Definitions.Def_RobustMultitask_Estimator_TrimmedMean
import Definitions.Def_RobustMultitask_Estimator_Model
import Definitions.Def_RobustMultitask_Estimator_Algorithm

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal
open RobustMultitask.Estimator

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N d : ℕ} (n : Fin N → ℕ) (X : (j : Fin N) → Matrix (Fin (n j)) (Fin d) ℝ)
    (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ) (s : ℕ) (σ : Fin N → ℝ≥0)
    (ε : (j : Fin N) → Fin (n j) → Ω → ℝ)
    (hmodel : IsMultitaskModel P n X β βdag s σ ε) (ψ : ℝ) (hA1 : Assumption1 n X ψ)
    (j : Fin N) (i : Fin d) :
    HasSubgaussianMGF (fun ω => ols (X j) (response X β ε j ω) i - β j i)
      (σ j ^ 2 / ((n j : ℝ≥0) * Real.toNNReal ψ)) P := by
  have hψ : 0 < ψ := hA1.1
  have hn : (0 : ℝ) < n j := by exact_mod_cast hmodel.pos_n j
  set M := X j with hM
  set A : Matrix (Fin d) (Fin d) ℝ := Mᵀ * M with hA
  -- Rayleigh-quotient lower bound for `A = XᵀX`
  have hray : ∀ v : Fin d → ℝ, (n j : ℝ) * ψ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v) := by
    intro v
    have h := hA1.2 j v
    simp only [sampleCov, smul_mulVec, dotProduct_smul, smul_eq_mul] at h
    rw [← hM] at h
    have := mul_le_mul_of_nonneg_left h hn.le
    have e1 : (n j : ℝ) * (1 / (n j : ℝ) * (v ⬝ᵥ (A *ᵥ v))) = v ⬝ᵥ (A *ᵥ v) := by
      field_simp
    rw [e1] at this
    linarith
  -- `A` is invertible
  have hdet : IsUnit A.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hAv⟩ := (exists_mulVec_eq_zero_iff (M := A)).2 h0
    have h1 := hray v
    rw [hAv, dotProduct_zero] at h1
    have h2 : v ⬝ᵥ v = 0 := by
      have := dotProduct_self_star_nonneg v
      have hpos : 0 < (n j : ℝ) * ψ := by positivity
      have h3 : 0 ≤ v ⬝ᵥ v := by
        simpa [dotProduct] using Finset.sum_nonneg (fun k _ => mul_self_nonneg (v k))
      nlinarith
    exact hv (dotProduct_self_eq_zero.1 h2)
  -- the row `w` of `A⁻¹`
  set w : Fin d → ℝ := A⁻¹ i with hw
  have hwA : w ᵥ* A = Pi.single i 1 := by
    have h := congrFun (nonsing_inv_mul A hdet) i
    rw [hw]
    ext l
    have := congrFun h l
    simp only [mul_apply, one_apply] at this
    simp only [vecMul, dotProduct, this, Pi.single_apply]
    by_cases hil : l = i
    · subst hil; simp
    · simp [hil, Ne.symm hil]
  have hwAw : w ⬝ᵥ (A *ᵥ w) = w i := by
    rw [dotProduct_mulVec, hwA]
    simp [Pi.single_apply, dotProduct]
  -- coefficient vector `a = X w`
  set a : Fin (n j) → ℝ := M *ᵥ w with ha
  have hasq : a ⬝ᵥ a = w i := by
    rw [← hwAw, ha, hA, ← mulVec_mulVec, dotProduct_mulVec w Mᵀ (M *ᵥ w), vecMul_transpose]
  have hwi : w i ≤ 1 / ((n j : ℝ) * ψ) := by
    have h1 := hray w
    rw [hwAw] at h1
    have hpos : 0 < (n j : ℝ) * ψ := by positivity
    have h2 : w i ^ 2 ≤ w ⬝ᵥ w := by
      simp only [dotProduct]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), sq]
      have : 0 ≤ ∑ x ∈ Finset.univ.erase i, w x * w x :=
        Finset.sum_nonneg (fun k _ => mul_self_nonneg (w k))
      linarith
    rw [le_div_iff₀ hpos]
    by_contra hc
    push Not at hc
    have hwpos : 0 < w i := by
      by_contra h0; push Not at h0; nlinarith
    have h3 : (n j : ℝ) * ψ * w i ^ 2 ≤ w i := by
      have := mul_le_mul_of_nonneg_left h2 hpos.le; linarith
    have h4 : w i < w i * (w i * ((n j : ℝ) * ψ)) := by
      have := mul_lt_mul_of_pos_left hc hwpos; linarith
    nlinarith
  -- the centred OLS component is `∑ₖ aₖ εₖ`
  have hrepr : ∀ ω, ols (X j) (response X β ε j ω) i - β j i = ∑ k, a k * ε j k ω := by
    intro ω
    simp only [ols, response]
    rw [← hM, mulVec_add, mulVec_mulVec, ← hA, mulVec_add, mulVec_mulVec, nonsing_inv_mul A hdet,
      one_mulVec, Pi.add_apply, add_sub_cancel_left]
    have : (A⁻¹ *ᵥ (Mᵀ *ᵥ fun k => ε j k ω)) i = w ⬝ᵥ (Mᵀ *ᵥ fun k => ε j k ω) := rfl
    rw [this, dotProduct_mulVec, vecMul_transpose, ← ha]
    rfl
  -- independence and subgaussianity
  have hind : iIndepFun (fun k : Fin (n j) => ε j k) P :=
    hmodel.indep.precomp (g := fun k : Fin (n j) => (⟨j, k⟩ : Σ j : Fin N, Fin (n j)))
      (fun a b h => by simpa using h)
  have hind' : iIndepFun (fun k : Fin (n j) => fun ω => a k * ε j k ω) P :=
    hind.comp (fun k x => a k * x) (fun k => measurable_const.mul measurable_id)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hind' (s := Finset.univ)
    (c := fun k => Real.toNNReal (a k ^ 2) * σ j ^ 2)
    (fun k _ => by
      have h := (hmodel.subgaussian j k).const_mul (a k)
      convert h using 2
      apply NNReal.eq
      simp [Real.coe_toNNReal _ (sq_nonneg (a k))]
      rfl)
  have hsum' : HasSubgaussianMGF (fun ω => ols (X j) (response X β ε j ω) i - β j i)
      (∑ k, Real.toNNReal (a k ^ 2) * σ j ^ 2) P :=
    hsum.congr (ae_of_all _ fun ω => by simp only [hrepr ω])
  have hle : ((∑ k, Real.toNNReal (a k ^ 2) * σ j ^ 2 : ℝ≥0) : ℝ)
      ≤ ((σ j ^ 2 / ((n j : ℝ≥0) * Real.toNNReal ψ) : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_sum]
    simp only [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg _), NNReal.coe_pow,
      NNReal.coe_div, NNReal.coe_natCast, Real.coe_toNNReal _ hψ.le]
    rw [← Finset.sum_mul]
    have : ∑ k, a k ^ 2 = w i := by rw [← hasq]; simp [dotProduct, sq]
    rw [this, div_eq_mul_one_div, mul_comm ((σ j : ℝ) ^ 2)]
    exact mul_le_mul_of_nonneg_right hwi (by positivity)
  exact ⟨hsum'.integrable_exp_mul, fun t => (hsum'.mgf_le t).trans
    (Real.exp_le_exp.2 (by gcongr))⟩
