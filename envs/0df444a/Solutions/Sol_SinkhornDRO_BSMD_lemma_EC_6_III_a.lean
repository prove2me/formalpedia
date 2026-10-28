-- Prove2me | solution 1 for SinkhornDRO.BSMD.lemma_EC_6_III_a
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T00:41:47.431487+00:00
-- url     : https://prove2.me/submissions/aca7cec6-4f88-4029-abf5-20dc97f46179

import Mathlib
import Definitions.Def_SinkhornDRO_BSMD_MirrorSetup
import Definitions.Def_SinkhornDRO_BSMD_Objective
import Definitions.Def_SinkhornDRO_BSMD_Estimators

open MeasureTheory ProbabilityTheory

namespace Aux_SDBEC6
open SinkhornDRO.BSMD

lemma sg_bound {d : ℕ} {Z : Type*} (f : Param d → Z → ℝ) (Lf : ℝ) (hA2II : Asm2Lipschitz f Lf)
    (sg : Param d → Z → Param d) (hsg : IsSubgradSel f sg) (θ : Param d) (z : Z) :
    ‖sg θ z‖ ≤ |Lf| := by
  have h1 := hsg θ z (θ + sg θ z)
  have h2 := hA2II z (θ + sg θ z) θ
  rw [add_sub_cancel_left, real_inner_self_eq_norm_sq] at h1
  rw [add_sub_cancel_left] at h2
  have h3 : ‖sg θ z‖ ^ 2 ≤ |Lf| * ‖sg θ z‖ := by
    have := le_abs_self (f (θ + sg θ z) z - f θ z)
    have := mul_le_mul_of_nonneg_right (le_abs_self Lf) (norm_nonneg (sg θ z))
    linarith
  rcases eq_or_lt_of_le (norm_nonneg (sg θ z)) with h | h
  · rw [← h]; exact abs_nonneg _
  · nlinarith

lemma levelg_bound {d : ℕ} {Z : Type*} (lam eps : ℝ) (f : Param d → Z → ℝ) (Lf : ℝ)
    (hA2II : Asm2Lipschitz f Lf) (sg : Param d → Z → Param d) (hsg : IsSubgradSel f sg)
    (ℓ : ℕ) (θ : Param d) (zs : Fin (2 ^ ℓ) → Z) :
    ‖levelg lam eps f sg ℓ θ zs‖ ≤ |Lf| := by
  unfold levelg blockGrad
  set e : Fin (2 ^ ℓ) → ℝ := fun j => Real.exp (f θ (zs j) / (lam * eps)) with he
  have hepos : ∀ j, 0 < e j := fun j => Real.exp_pos _
  have hne : (Finset.univ : Finset (Fin (2 ^ ℓ))).Nonempty := ⟨⟨0, by positivity⟩, Finset.mem_univ _⟩
  have hS : 0 < ∑ k, e k := Finset.sum_pos (fun k _ => hepos k) hne
  calc ‖∑ j, (e j / ∑ k, e k) • sg θ (zs j)‖
      ≤ ∑ j, ‖(e j / ∑ k, e k) • sg θ (zs j)‖ := norm_sum_le _ _
    _ ≤ ∑ j, (e j / ∑ k, e k) * |Lf| := by
        apply Finset.sum_le_sum; intro j _
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (hepos j) hS)]
        exact mul_le_mul_of_nonneg_left (sg_bound f Lf hA2II sg hsg θ (zs j))
          (div_pos (hepos j) hS).le
    _ = |Lf| := by
        rw [← Finset.sum_mul, ← Finset.sum_div, div_self hS.ne', one_mul]

end Aux_SDBEC6

open SinkhornDRO.BSMD Aux_SDBEC6 in
theorem solution {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (Θ : Set (Param d)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ)
    (P : Measure Z) [IsProbabilityMeasure P] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (lam eps : ℝ) (hlam : 0 < lam) (heps : 0 < eps)
    (f : Param d → Z → ℝ) (hf_meas : ∀ θ, Measurable (f θ))
    (Lf : ℝ) (hA2I : Asm2Convex f) (hA2II : Asm2Lipschitz f Lf)
    (sg : Param d → Z → Param d) (hsg : IsSubgradSel f sg) (hsg_meas : ∀ θ, Measurable (sg θ))
    (ℓ : ℕ) :
    ∀ θ ∈ Θ,
      Integrable (fun ζ : Z × (Fin (2 ^ ℓ) → Z) => ‖levelg lam eps f sg ℓ θ ζ.2‖ ^ 2)
          (levelLaw P Q (2 ^ ℓ)) ∧
        ∫ ζ, ‖levelg lam eps f sg ℓ θ ζ.2‖ ^ 2 ∂(levelLaw P Q (2 ^ ℓ)) ≤ Lf ^ 2 := by
  intro θ _
  -- total mass at most one
  have hmass : levelLaw P Q (2 ^ ℓ) Set.univ ≤ 1 := by
    unfold levelLaw
    refine (Measure.bind_apply_le _ MeasurableSet.univ).trans ?_
    simp only [measure_univ, lintegral_const, one_mul]
    exact le_rfl
  haveI : IsFiniteMeasure (levelLaw P Q (2 ^ ℓ)) :=
    ⟨lt_of_le_of_lt hmass ENNReal.one_lt_top⟩
  -- measurability
  have hm1 : ∀ j : Fin (2 ^ ℓ), Measurable (fun ζ : Z × (Fin (2 ^ ℓ) → Z) => ζ.2 j) :=
    fun j => (measurable_pi_apply j).comp measurable_snd
  have hE : ∀ j : Fin (2 ^ ℓ), Measurable
      (fun ζ : Z × (Fin (2 ^ ℓ) → Z) => Real.exp (f θ (ζ.2 j) / (lam * eps))) :=
    fun j => Real.measurable_exp.comp (((hf_meas θ).comp (hm1 j)).div_const _)
  have hS : Measurable (fun ζ : Z × (Fin (2 ^ ℓ) → Z) =>
      ∑ k, Real.exp (f θ (ζ.2 k) / (lam * eps))) :=
    Finset.measurable_sum _ (fun k _ => hE k)
  have hG : Measurable (fun ζ : Z × (Fin (2 ^ ℓ) → Z) => levelg lam eps f sg ℓ θ ζ.2) := by
    unfold levelg blockGrad
    exact Finset.measurable_sum _ (fun j _ => ((hE j).div hS).smul ((hsg_meas θ).comp (hm1 j)))
  have hmeas : AEStronglyMeasurable (fun ζ : Z × (Fin (2 ^ ℓ) → Z) =>
      ‖levelg lam eps f sg ℓ θ ζ.2‖ ^ 2) (levelLaw P Q (2 ^ ℓ)) :=
    (hG.norm.pow_const 2).aestronglyMeasurable
  have hpt : ∀ ζ : Z × (Fin (2 ^ ℓ) → Z), ‖levelg lam eps f sg ℓ θ ζ.2‖ ^ 2 ≤ Lf ^ 2 := by
    intro ζ
    have := levelg_bound lam eps f Lf hA2II sg hsg ℓ θ ζ.2
    have h0 := norm_nonneg (levelg lam eps f sg ℓ θ ζ.2)
    rw [← sq_abs Lf]
    exact pow_le_pow_left₀ h0 this 2
  have hint : Integrable (fun ζ : Z × (Fin (2 ^ ℓ) → Z) => ‖levelg lam eps f sg ℓ θ ζ.2‖ ^ 2)
      (levelLaw P Q (2 ^ ℓ)) := by
    refine Integrable.of_bound hmeas (Lf ^ 2) (Filter.Eventually.of_forall (fun ζ => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt ζ
  refine ⟨hint, ?_⟩
  calc ∫ ζ, ‖levelg lam eps f sg ℓ θ ζ.2‖ ^ 2 ∂(levelLaw P Q (2 ^ ℓ))
      ≤ ∫ _ζ, Lf ^ 2 ∂(levelLaw P Q (2 ^ ℓ)) := integral_mono hint (integrable_const _) hpt
    _ = (levelLaw P Q (2 ^ ℓ)).real Set.univ * Lf ^ 2 := by rw [integral_const, smul_eq_mul]
    _ ≤ 1 * Lf ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        rw [measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hmass)
    _ = Lf ^ 2 := one_mul _
