-- Prove2me | solution 1 for WangMinimaxRegret.Reformulation.eq_2_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:12:23.244198+00:00
-- url     : https://prove2.me/submissions/ec08b335-7f8f-4b6f-90e9-9478bd0d40e5

import Mathlib
import Definitions.Def_WangMinimaxRegret_Reformulation_Programs

open MeasureTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false

open WangMinimaxRegret.Reformulation

lemma s225mb_rev_smul (m : StieltjesFunction ℝ) (c : ℝ≥0∞) (H : Measure ℝ) :
    revenue m (c • H) = c * revenue m H := by
  unfold revenue
  rw [lintegral_smul_measure]
  rfl

lemma s225mb_part2 (d : Data) (m : StieltjesFunction ℝ) (p : ℝ) (F : Measure ℝ)
    (hF : MomentLaw d F) (ht : 0 < tail F p) :
    (homogenizedLP d m p).Feasible (scaleToTail F p) ∧
      normalizeMass (scaleToTail F p) = F ∧
      revenue m (scaleToTail F p) = revenue m F / tail F p := by
  obtain ⟨hprob, hcompl, hmom⟩ := hF
  have htle : tail F p ≤ 1 := prob_le_one
  have htne : tail F p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top htle
  have hc0 : (tail F p)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr htne
  have hctop : (tail F p)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr ht.ne'
  have hfin : IsFiniteMeasure (scaleToTail F p) := Measure.smul_finite F hctop
  refine ⟨⟨hfin, ?_, ?_⟩, ?_, ?_⟩
  · show ((tail F p)⁻¹ • F) (interval d)ᶜ = 0
    rw [Measure.smul_apply, hcompl, smul_zero]
  · intro i
    cases i with
    | none =>
      show Integrable ((Ici p).indicator (fun _ => (1 : ℝ))) _ ∧
        (∫ x, (Ici p).indicator (fun _ => (1 : ℝ)) x ∂(scaleToTail F p)) = 1
      refine ⟨(integrable_const (1 : ℝ)).indicator measurableSet_Ici, ?_⟩
      have := integral_indicator_one (μ := scaleToTail F p) (measurableSet_Ici (a := p))
      simp only [Pi.one_def] at this
      rw [this, Measure.real, scaleToTail, Measure.smul_apply, smul_eq_mul]
      show ((tail F p)⁻¹ * tail F p).toReal = 1
      rw [ENNReal.inv_mul_cancel ht.ne' htne]; rfl
    | some j =>
      show Integrable (fun x : ℝ => x ^ (j.val + 1) - d.mu j) _ ∧
        (∫ x, (x ^ (j.val + 1) - d.mu j) ∂(scaleToTail F p)) = 0
      have hint : Integrable (fun x : ℝ => x ^ (j.val + 1)) (scaleToTail F p) :=
        (hmom j).1.smul_measure hctop
      refine ⟨hint.sub (integrable_const _), ?_⟩
      rw [integral_sub hint (integrable_const _), scaleToTail, integral_smul_measure,
        (hmom j).2, integral_const, smul_eq_mul, smul_eq_mul, Measure.real,
        Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      ring
  · show (((tail F p)⁻¹ • F) univ)⁻¹ • ((tail F p)⁻¹ • F) = F
    rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, smul_smul,
      ENNReal.inv_mul_cancel hc0 hctop, one_smul]
  · rw [scaleToTail, s225mb_rev_smul, div_eq_mul_inv, mul_comm]

lemma s225mb_part3 (d : Data) (m : StieltjesFunction ℝ) (p : ℝ) (H : Measure ℝ)
    (hH : (homogenizedLP d m p).Feasible H) :
    0 < H univ ∧ MomentLaw d (normalizeMass H) ∧
      0 < tail (normalizeMass H) p ∧ scaleToTail (normalizeMass H) p = H ∧
      revenue m (normalizeMass H) / tail (normalizeMass H) p = revenue m H := by
  obtain ⟨hfin, hcompl, htest⟩ := hH
  have hnone := htest none
  have hI : (∫ x, (Ici p).indicator (fun _ => (1 : ℝ)) x ∂H) = 1 := hnone.2
  have := integral_indicator_one (μ := H) (measurableSet_Ici (a := p))
  simp only [Pi.one_def] at this
  rw [this] at hI
  have hIci : H (Ici p) = 1 := by
    rw [Measure.real] at hI
    have hne : H (Ici p) ≠ ∞ := measure_ne_top H _
    rw [← ENNReal.ofReal_toReal hne, hI, ENNReal.ofReal_one]
  set M := H univ with hM
  have hM1 : 1 ≤ M := hIci ▸ measure_mono (subset_univ _)
  have hM0 : M ≠ 0 := (lt_of_lt_of_le one_pos hM1).ne'
  have hMt : M ≠ ∞ := measure_ne_top H _
  have hMi0 : M⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hMt
  have hMit : M⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hM0
  have htail : tail (normalizeMass H) p = M⁻¹ := by
    show (M⁻¹ • H) (Ici p) = M⁻¹
    rw [Measure.smul_apply, hIci, smul_eq_mul, mul_one]
  have hMr : M.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hM0, hMt⟩
  refine ⟨lt_of_lt_of_le one_pos hM1, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · constructor
    show (M⁻¹ • H) univ = 1
    rw [Measure.smul_apply, smul_eq_mul, ← hM, ENNReal.inv_mul_cancel hM0 hMt]
  · show (M⁻¹ • H) (interval d)ᶜ = 0
    rw [Measure.smul_apply, show H (interval d)ᶜ = 0 from hcompl, smul_zero]
  · intro j
    have hj : Integrable (fun x : ℝ => x ^ (j.val + 1) - d.mu j) H ∧
        (∫ x, (x ^ (j.val + 1) - d.mu j) ∂H) = 0 := htest (some j)
    have hint : Integrable (fun x : ℝ => x ^ (j.val + 1)) H := by
      refine (hj.1.add (integrable_const (d.mu j))).congr
        (Filter.Eventually.of_forall fun x => ?_)
      simp
    have hval : (∫ x, x ^ (j.val + 1) ∂H) = M.toReal * d.mu j := by
      have h2 := hj.2
      rw [integral_sub hint (integrable_const _), integral_const, smul_eq_mul,
        Measure.real] at h2
      rw [hM]; linarith
    refine ⟨hint.smul_measure hMit, ?_⟩
    show (∫ x, x ^ (j.val + 1) ∂(M⁻¹ • H)) = d.mu j
    rw [integral_smul_measure, hval, smul_eq_mul, ENNReal.toReal_inv, ← mul_assoc,
      inv_mul_cancel₀ hMr, one_mul]
  · rw [htail]; exact ENNReal.inv_pos.mpr hMt
  · show (tail (normalizeMass H) p)⁻¹ • (M⁻¹ • H) = H
    rw [htail, smul_smul, inv_inv, ENNReal.mul_inv_cancel hM0 hMt, one_smul]
  · rw [htail]
    show revenue m (M⁻¹ • H) / M⁻¹ = revenue m H
    rw [s225mb_rev_smul, mul_comm, ENNReal.mul_div_cancel_right hMi0 hMit]

theorem solution (d : Data) (hc : Consistent d) (m : StieltjesFunction ℝ)
    (hm : IsPayment d m) (p : ℝ) (hp : p ∈ interval d) :
    fractionalValue {F | MomentLaw d F} m p = (homogenizedLP d m p).value ∧
    (∀ F : Measure ℝ, MomentLaw d F → 0 < tail F p →
      (homogenizedLP d m p).Feasible (scaleToTail F p) ∧
      normalizeMass (scaleToTail F p) = F ∧
      revenue m (scaleToTail F p) = revenue m F / tail F p) ∧
    (∀ H : Measure ℝ, (homogenizedLP d m p).Feasible H →
      0 < H univ ∧ MomentLaw d (normalizeMass H) ∧
      0 < tail (normalizeMass H) p ∧ scaleToTail (normalizeMass H) p = H ∧
      revenue m (normalizeMass H) / tail (normalizeMass H) p = revenue m H) := by
  refine ⟨?_, fun F hF ht => s225mb_part2 d m p F hF ht, fun H hH => s225mb_part3 d m p H hH⟩
  apply le_antisymm
  · refine le_iInf₂ fun H hH => ?_
    obtain ⟨-, hlaw, ht, -, hrev⟩ := s225mb_part3 d m p H hH
    refine (iInf₂_le (normalizeMass H) hlaw).trans ((iInf_le _ ht).trans ?_)
    rw [hrev]; exact le_rfl
  · refine le_iInf₂ fun F hF => le_iInf fun ht => ?_
    obtain ⟨hfeas, -, hrev⟩ := s225mb_part2 d m p F hF ht
    refine (iInf₂_le (scaleToTail F p) hfeas).trans ?_
    show revenue m (scaleToTail F p) ≤ _
    rw [hrev]
