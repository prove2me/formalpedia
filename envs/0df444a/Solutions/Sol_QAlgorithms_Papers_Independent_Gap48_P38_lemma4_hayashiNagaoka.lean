-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P38.lemma4_hayashiNagaoka
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:51:57.268145+00:00
-- url     : https://prove2.me/submissions/86f09b95-5231-4dbf-a026-66bd2b35f966

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P38
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator MatrixOrder

set_option backward.isDefEq.respectTransparency false

namespace X4HN

variable {J : Type} [Fintype J] [DecidableEq J]

local notation "M" => Matrix J J ℂ

lemma cont (f : ℝ → ℝ) (A : M) : ContinuousOn f (spectrum ℝ A) :=
  (Matrix.finite_real_spectrum (A := A)).continuousOn f

/-- `Π ≤ √Π` for an effect. -/
lemma le_sqrt_self {P : M} (h0 : 0 ≤ P) (h1 : P ≤ 1) : P ≤ CFC.sqrt P := by
  have hsa : IsSelfAdjoint P := IsSelfAdjoint.of_nonneg h0
  have hspec : ∀ x ∈ spectrum ℝ P, 0 ≤ x ∧ x ≤ 1 := by
    intro x hx
    refine ⟨spectrum_nonneg_of_nonneg h0 hx, ?_⟩
    have := (le_algebraMap_iff_spectrum_le (r := (1 : ℝ)) (a := P) hsa).1
      (by simpa using h1)
    exact this x hx
  rw [CFC.sqrt_eq_real_sqrt P h0, cfcₙ_eq_cfc]
  conv_lhs => rw [← cfc_id' ℝ P]
  refine cfc_mono (fun x hx => ?_) (cont _ P) (cont _ P)
  obtain ⟨a, b⟩ := hspec x hx
  calc x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt a).symm
    _ ≤ Real.sqrt x * 1 := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg x)
        exact Real.sqrt_le_one.mpr b
    _ = Real.sqrt x := mul_one _


/-- scalar inequality behind step D -/
lemma scalar (x : ℝ) (hx : 0 ≤ x) :
    1 - (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ +
      (((Real.sqrt x)⁻¹ - 1) * x * ((Real.sqrt x)⁻¹ - 1) +
        ((Real.sqrt x)⁻¹ - 1) * x * ((Real.sqrt x)⁻¹ - 1)) ≤
    1 + 1 - (Real.sqrt x + Real.sqrt x + Real.sqrt x + Real.sqrt x) + (x + x) := by
  rcases hx.eq_or_lt with rfl | hpos
  · norm_num
  · have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hpos
    have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx
    have e1 : (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ = 1 := by
      calc (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹
          = (Real.sqrt x)⁻¹ * (Real.sqrt x * Real.sqrt x) * (Real.sqrt x)⁻¹ := by rw [hsq]
        _ = 1 := by field_simp
    have e2 : ((Real.sqrt x)⁻¹ - 1) * x * ((Real.sqrt x)⁻¹ - 1) = (1 - Real.sqrt x) ^ 2 := by
      calc ((Real.sqrt x)⁻¹ - 1) * x * ((Real.sqrt x)⁻¹ - 1)
          = ((Real.sqrt x)⁻¹ - 1) * (Real.sqrt x * Real.sqrt x) * ((Real.sqrt x)⁻¹ - 1) := by
            rw [hsq]
        _ = (1 - Real.sqrt x) ^ 2 := by field_simp
    rw [e1, e2]
    nlinarith [hsq]

lemma stepD (L : M) (hL : 0 ≤ L) :
    1 - cfc (fun x : ℝ => (Real.sqrt x)⁻¹) L * L * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) L +
      ((cfc (fun x : ℝ => (Real.sqrt x)⁻¹) L - 1) * L * (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) L - 1) +
       (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) L - 1) * L * (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) L - 1)) ≤
    1 + 1 - (CFC.sqrt L + CFC.sqrt L + CFC.sqrt L + CFC.sqrt L) + (L + L) := by
  have hsa : IsSelfAdjoint L := IsSelfAdjoint.of_nonneg hL
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ L) := fun f => cont f L
  set y : ℝ → ℝ := fun x => (Real.sqrt x)⁻¹ with hy
  have hR : CFC.sqrt L = cfc Real.sqrt L := by
    rw [CFC.sqrt_eq_real_sqrt L hL, cfcₙ_eq_cfc]
  have hone : (1 : M) = cfc (fun _ : ℝ => (1 : ℝ)) L := by rw [cfc_const (1 : ℝ) L]; simp
  have hid : L = cfc (fun x : ℝ => x) L := (cfc_id' ℝ L).symm
  have hY1 : cfc y L - 1 = cfc (fun x => y x - 1) L := by
    rw [cfc_sub (hf := hc _) (hg := hc _), ← hone]
  have hYLY : cfc y L * L * cfc y L = cfc (fun x => y x * x * y x) L := by
    conv_lhs => rw [hid]
    rw [cfc_mul (hf := hc _) (hg := hc _), cfc_mul (hf := hc _) (hg := hc _)]
    simp only [cfc_id' ℝ L]
  have hZ : (cfc y L - 1) * L * (cfc y L - 1) =
      cfc (fun x => (y x - 1) * x * (y x - 1)) L := by
    rw [hY1]
    conv_lhs => rw [hid]
    rw [cfc_mul (hf := hc _) (hg := hc _), cfc_mul (hf := hc _) (hg := hc _)]
    simp only [cfc_id' ℝ L]
  have hlhs : 1 - cfc y L * L * cfc y L +
      ((cfc y L - 1) * L * (cfc y L - 1) + (cfc y L - 1) * L * (cfc y L - 1)) =
      cfc (fun x => 1 - y x * x * y x + ((y x - 1) * x * (y x - 1) + (y x - 1) * x * (y x - 1))) L := by
    rw [hYLY, hZ, cfc_add (hf := hc _) (hg := hc _), cfc_add (a := L) (hf := hc _) (hg := hc _),
      cfc_sub (a := L) (hf := hc _) (hg := hc _), ← hone]
  have hrhs : 1 + 1 - (CFC.sqrt L + CFC.sqrt L + CFC.sqrt L + CFC.sqrt L) + (L + L) =
      cfc (fun x => 1 + 1 - (Real.sqrt x + Real.sqrt x + Real.sqrt x + Real.sqrt x) + (x + x)) L := by
    rw [cfc_add (hf := hc _) (hg := hc _), cfc_sub (a := L) (hf := hc _) (hg := hc _),
      cfc_add (a := L) (hf := hc _) (hg := hc _), cfc_add (a := L) (hf := hc _) (hg := hc _),
      cfc_add (a := L) (hf := hc _) (hg := hc _), cfc_add (a := L) (hf := hc _) (hg := hc _),
      cfc_add (a := L) (hf := hc _) (hg := hc _), ← hone, ← hR, cfc_id' ℝ L]
  rw [hlhs, hrhs]
  exact cfc_mono (fun x hx => scalar x (spectrum_nonneg_of_nonneg hL hx)) (hc _) (hc _)


lemma main (P L : M) (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hPL : P ≤ L) :
    1 - cfc (fun x : ℝ => (Real.sqrt x)⁻¹) L * P * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) L ≤
      ((1 - P) + (1 - P)) + ((L - P) + (L - P) + (L - P) + (L - P)) := by
  have hL : 0 ≤ L := hP0.trans hPL
  set Y := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) L with hYdef
  have hY : IsSelfAdjoint Y := cfc_predicate _ L
  set S := L - P with hSdef
  have hS : 0 ≤ S := sub_nonneg.2 hPL
  set R := CFC.sqrt L
  have hPR : P ≤ R := (le_sqrt_self hP0 hP1).trans (CFC.sqrt_le_sqrt P L hPL)
  have h1 : 1 - Y * P * Y = (1 - Y * L * Y) + Y * S * Y := by rw [hSdef]; noncomm_ring
  have h2 : Y * S * Y ≤ (S + S) + ((Y - 1) * S * (Y - 1) + (Y - 1) * S * (Y - 1)) := by
    have := star_left_conjugate_nonneg hS (Y - 1 - 1)
    rw [star_sub, star_sub, star_one, hY.star_eq] at this
    rw [← sub_nonneg]
    convert this using 1
    noncomm_ring
  have h3 : (Y - 1) * S * (Y - 1) ≤ (Y - 1) * L * (Y - 1) := by
    have := star_left_conjugate_nonneg hP0 (Y - 1)
    rw [star_sub, star_one, hY.star_eq] at this
    rw [← sub_nonneg]
    convert this using 1
    rw [hSdef]; noncomm_ring
  have h4 := stepD L hL
  calc 1 - Y * P * Y = (1 - Y * L * Y) + Y * S * Y := h1
    _ ≤ (1 - Y * L * Y) + ((S + S) + ((Y - 1) * S * (Y - 1) + (Y - 1) * S * (Y - 1))) := by
        gcongr
    _ ≤ (1 - Y * L * Y) + ((S + S) + ((Y - 1) * L * (Y - 1) + (Y - 1) * L * (Y - 1))) := by
        gcongr
    _ = ((1 - Y * L * Y) + ((Y - 1) * L * (Y - 1) + (Y - 1) * L * (Y - 1))) + (S + S) := by abel
    _ ≤ (1 + 1 - (R + R + R + R) + (L + L)) + (S + S) := by gcongr
    _ ≤ (1 + 1 - (P + P + P + P) + (L + L)) + (S + S) := by gcongr
    _ = ((1 - P) + (1 - P)) + (S + S + S + S) := by rw [hSdef]; abel

end X4HN

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P38

theorem solution
    (J : Type) [Fintype J] [DecidableEq J] [Nonempty J]
    (Pi Lambda : Matrix J J ℂ) (hPi : IsEffect Pi)
    (hLambda : (Lambda - Pi).PosSemidef) :
    ((2 : ℂ) • (1 - Pi) + (4 : ℂ) • (Lambda - Pi) -
      (1 - QAlgorithms.Papers.Independent.Next46.P39.inverseSqrt Lambda * Pi * QAlgorithms.Papers.Independent.Next46.P39.inverseSqrt Lambda)).PosSemidef := by
  obtain ⟨h0, h1⟩ := hPi
  have hP0 : 0 ≤ Pi := h0.nonneg
  have hP1 : Pi ≤ 1 := sub_nonneg.1 h1.nonneg
  have hPL : Pi ≤ Lambda := sub_nonneg.1 hLambda.nonneg
  have := Matrix.le_iff.1 (X4HN.main Pi Lambda hP0 hP1 hPL)
  have e : (2 : ℂ) • (1 - Pi) + (4 : ℂ) • (Lambda - Pi) -
      (1 - QAlgorithms.Papers.Independent.Next46.P39.inverseSqrt Lambda * Pi *
        QAlgorithms.Papers.Independent.Next46.P39.inverseSqrt Lambda) =
      ((1 - Pi) + (1 - Pi)) + ((Lambda - Pi) + (Lambda - Pi) + (Lambda - Pi) + (Lambda - Pi)) -
      (1 - cfc (fun x : ℝ => (Real.sqrt x)⁻¹) Lambda * Pi * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) Lambda) := by
    rw [show (4 : ℂ) = 1 + 1 + 1 + 1 by norm_num, two_smul, add_smul, add_smul, add_smul, one_smul]
    rfl
  rw [e]
  exact this

