-- Prove2me | solution 1 for SAARate.Polyhedral.pointwise_exponential_bounds
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:52:52.890991+00:00
-- url     : https://prove2.me/submissions/80edae62-786d-4cc1-a558-8e09275b933f

import Mathlib
import Definitions.Def_SAARate_Polyhedral_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

lemma saap_tail {S : Type*} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (X : ℕ → S → ℝ) (hind : iIndepFun X Q) (c : ℝ≥0) (hc : 0 < c)
    (hsub : ∀ i, HasSubgaussianMGF (X i) c Q) (ε : ℝ) (hε : 0 < ε) :
    ∃ β > 0, ∀ δ > 0, ∀ᶠ N : ℕ in atTop,
      Q {s | (N : ℝ) * ε ≤ ∑ i ∈ Finset.range N, X i s} ≤
        ENNReal.ofReal (Real.exp (-(β - δ) * (N : ℝ))) := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  refine ⟨ε ^ 2 / (2 * c), by positivity, fun δ hδ => ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hind (n := N) (fun i _ => hsub i)
    (ε := N * ε) (by positivity)
  have e : -(↑N * ε) ^ 2 / (2 * ↑N * (c : ℝ)) = -(ε ^ 2 / (2 * c)) * N := by
    field_simp
  rw [e] at h
  calc Q {s | (N : ℝ) * ε ≤ ∑ i ∈ Finset.range N, X i s}
      = ENNReal.ofReal (Q.real {s | (N : ℝ) * ε ≤ ∑ i ∈ Finset.range N, X i s}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        refine h.trans (Real.exp_le_exp.mpr ?_)
        nlinarith [mul_pos hδ hN']

theorem solution {m : ℕ} {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : SAARate.Sharp.E m → Ω → ℝ)
    {S : Type*} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (ω : ℕ → S → Ω) (hω : SAARate.SharpLD.IsIIDSample Q P ω) (x : SAARate.Sharp.E m) (ε : ℝ) (hε : 0 < ε) :
    (∃ β > 0, ∀ δ > 0, ∀ᶠ N : ℕ in atTop,
        Q {s | SAARate.Sharp.expectedObj P h x + ε ≤ SAARate.Sharp.saaObj h (fun j => ω j s) N x} ≤
          ENNReal.ofReal (Real.exp (-(β - δ) * (N : ℝ)))) ∧
      (∃ β > 0, ∀ δ > 0, ∀ᶠ N : ℕ in atTop,
        Q {s | SAARate.Sharp.saaObj h (fun j => ω j s) N x ≤ SAARate.Sharp.expectedObj P h x - ε} ≤
          ENNReal.ofReal (Real.exp (-(β - δ) * (N : ℝ)))) := by
  obtain ⟨hmeas, hind, hlaw⟩ := hω
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → S → ℝ, ∀ j s, Y j s = h x (ω j s) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = SAARate.Sharp.expectedObj P h x := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ∑ w, |h x w| := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBdef]; exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hB : ∀ w, |h x w| ≤ B := fun w => by
    rw [hBdef]
    exact Finset.single_le_sum (f := fun w => |h x w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)
  have hhm : Measurable (h x) := Measurable.of_discrete
  have hYeq : Y = fun j => (h x) ∘ (ω j) := by funext j s; exact hY j s
  have hYmeas : ∀ j, Measurable (Y j) := fun j => by rw [hYeq]; exact hhm.comp (hmeas j)
  have hYind : iIndepFun Y Q := by
    rw [hYeq]; exact hind.comp (fun _ => h x) (fun _ => hhm)
  have hmean : ∀ j, ∫ s, Y j s ∂Q = μ := by
    intro j
    rw [hμ]
    unfold SAARate.Sharp.expectedObj
    rw [← hlaw j, integral_map (hmeas j).aemeasurable hhm.aestronglyMeasurable]
    exact integral_congr_ae (ae_of_all _ (fun s => hY j s))
  have hbd : ∀ j, ∀ᵐ s ∂Q, Y j s ∈ Set.Icc (-(B + 1)) (B + 1) := fun j => ae_of_all _ (fun s => by
    have := abs_le.mp (hB (ω j s))
    rw [hY]
    constructor <;> linarith [this.1, this.2])
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ≥0, c = (‖(B + 1) - -(B + 1)‖₊ / 2) ^ 2 := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hcdef]
    refine pow_pos (div_pos (nnnorm_pos.mpr ?_) two_pos) 2
    intro h0; linarith
  have hsub : ∀ j, HasSubgaussianMGF (fun s => Y j s - μ) c Q := by
    intro j
    have := hasSubgaussianMGF_of_mem_Icc (μ := Q) (hYmeas j).aemeasurable (hbd j)
    rw [hmean j] at this
    rw [hcdef]; exact this
  have hX1 : iIndepFun (fun j s => Y j s - μ) Q :=
    hYind.comp (fun _ y => y - μ) (fun _ => measurable_sub_const _)
  have hX2 : iIndepFun (fun j s => -(Y j s - μ)) Q :=
    hYind.comp (fun _ y => -(y - μ)) (fun _ => (measurable_sub_const _).neg)
  have hsub2 : ∀ j, HasSubgaussianMGF (fun s => -(Y j s - μ)) c Q := fun j => (hsub j).neg
  obtain ⟨β₁, hβ₁, h₁⟩ := saap_tail Q (fun j s => Y j s - μ) hX1 c hc hsub ε hε
  obtain ⟨β₂, hβ₂, h₂⟩ := saap_tail Q (fun j s => -(Y j s - μ)) hX2 c hc hsub2 ε hε
  refine ⟨⟨β₁, hβ₁, fun δ hδ => ?_⟩, ⟨β₂, hβ₂, fun δ hδ => ?_⟩⟩
  · filter_upwards [h₁ δ hδ, eventually_ge_atTop 1] with N hN hN1
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN1
    have e : {s | SAARate.Sharp.expectedObj P h x + ε ≤
          SAARate.Sharp.saaObj h (fun j => ω j s) N x} =
        {s | (N : ℝ) * ε ≤ ∑ i ∈ Finset.range N, (Y i s - μ)} := by
      ext s
      simp only [Set.mem_setOf_eq, SAARate.Sharp.saaObj, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, hY, ← hμ]
      rw [le_inv_mul_iff₀ hN']
      constructor <;> intro hh <;> nlinarith
    rw [e]; exact hN
  · filter_upwards [h₂ δ hδ, eventually_ge_atTop 1] with N hN hN1
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN1
    have e : {s | SAARate.Sharp.saaObj h (fun j => ω j s) N x ≤
          SAARate.Sharp.expectedObj P h x - ε} =
        {s | (N : ℝ) * ε ≤ ∑ i ∈ Finset.range N, -(Y i s - μ)} := by
      ext s
      simp only [Set.mem_setOf_eq, SAARate.Sharp.saaObj, Finset.sum_neg_distrib,
        Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hY, ← hμ]
      rw [inv_mul_le_iff₀ hN']
      constructor <;> intro hh <;> nlinarith
    rw [e]; exact hN
