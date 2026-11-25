-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mulVec_one_sub_idempotent_of_split_sum_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:03:47.261682+00:00
-- url     : https://prove2.me/submissions/66ee0d17-5754-41ff-a7b7-4188afab9cc7

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsIbp
import Theorems.Thm_ReciprocityTheory_AnForm_A_integration_by_parts_complex
import Theorems.Thm_ReciprocityTheory_AnForm_A_vanish_outside_tsupport
import Theorems.Thm_ReciprocityTheory_AnForm_A_dz_of_eventually_zero
import Theorems.Thm_ReciprocityTheory_AnForm_A_dzb_of_eventually_zero
import Theorems.Thm_ReciprocityTheory_AnForm_A_gradDensSymm_thm
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_eq_hessMat
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_cons_eq
import Theorems.Thm_ReciprocityTheory_AnForm_A_mixedDisc_cons_eq_sum
import Theorems.Thm_ReciprocityTheory_AnForm_A_monge_ampere_density_cofactor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : PartsStatement := by
  intro n φ v w U ⟨hU, hv, hvc, hKU, hw, hφ⟩
  have hK : IsCompact (tsupport v) := hvc
  have hout : ∀ y ∉ tsupport v, _ := fun y hy => vanish_outside_tsupport (v := v) (y := y) hy
  obtain ⟨hX1, hY1, hI1⟩ := integration_by_parts_complex φ v w U (tsupport v) hU hK hKU hv hw hφ (fun y hy j k => ⟨
      (hout y hy).1.mono fun x hx => by simp only at hx ⊢; rw [hx, zero_mul],
      by rw [dz_of_eventually_zero (hout y hy).1, zero_mul],
      by simp only [(hout y hy).1.self_of_nhds, zero_mul]⟩)
  obtain ⟨hX2, hY2, hI2⟩ := integration_by_parts_complex φ w v U (tsupport v) hU hK hKU hw hv hφ (fun y hy j k => ⟨
      ((hout y hy).2.1 k).mono fun x hx => by simp only at hx ⊢; rw [hx, mul_zero],
      by simp only [((hout y hy).2.1 k).self_of_nhds, mul_zero],
      by rw [dz_of_eventually_zero ((hout y hy).2.1 k), mul_zero]⟩)
  set c : ℝ := ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) with hc
  have hvz : ∀ y ∉ U, v y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport fun h => hy (hKU h)
  have e1 : ∀ y, v y * maDens (Fin.cons w φ) y =
      c * (cplx v y * ∑ j, ∑ k, hessCof φ y j k * dz j (dzb k (cplx w)) y).re := by
    intro y
    by_cases hy : y ∈ U
    · rw [monge_ampere_density_cofactor n φ w U hU (hw.of_le (by norm_num)) y hy]
      simp only [cplx, Complex.re_ofReal_mul]; ring
    · simp [cplx, hvz y hy]
  have e2 : ∀ y, w y * maDens (Fin.cons v φ) y =
      c * (cplx w y * ∑ j, ∑ k, hessCof φ y j k * dz j (dzb k (cplx v)) y).re := by
    intro y
    by_cases hy : y ∈ U
    · rw [monge_ampere_density_cofactor n φ v U hU (hv.of_le (by norm_num)) y hy]
      simp only [cplx, Complex.re_ofReal_mul]; ring
    · have hyK : y ∉ tsupport v := fun h => hy (hKU h)
      have h1 : maDens (Fin.cons v φ) y = 0 := by
        rw [maDens_cons_eq, mixedDisc_cons_eq_sum, hessC_eq_hessMat, (hout y hyK).2.2]; simp
      have h2 : ∀ j k, dz j (dzb k (cplx v)) y = 0 :=
        fun j k => dz_of_eventually_zero ((hout y hyK).2.1 k)
      simp [h1, h2]
  have e3 : ∀ y, gradDens φ v w y =
      c * (∑ j, ∑ k, dz j (cplx v) y * dzb k (cplx w) y * hessCof φ y j k).re := by
    intro y; simp only [gradDens, mixedDisc_cons_eq_sum]; rfl
  have e4 : ∀ y, gradDens φ w v y =
      c * (∑ j, ∑ k, dz j (cplx w) y * dzb k (cplx v) y * hessCof φ y j k).re := by
    intro y; simp only [gradDens, mixedDisc_cons_eq_sum]; rfl
  have hgz : ∀ y ∉ U, gradDens φ v w y = 0 := by
    intro y hy
    rw [e3]
    simp [dz_of_eventually_zero ((hout y fun h => hy (hKU h)).1)]
  have hsym : ∀ y, gradDens φ v w y = gradDens φ w v y := by
    intro y
    by_cases hy : y ∈ U
    · exact gradDensSymm_thm n φ v w U hU (fun i => (hφ i).of_le (by norm_num)) y hy
    · rw [hgz y hy, e4]
      simp [dzb_of_eventually_zero ((hout y fun h => hy (hKU h)).1)]
  have i1 : Integrable (fun y => v y * maDens (Fin.cons w φ) y) := by
    simp only [e1]; exact hY1.re.const_mul c
  have i2 : Integrable (fun y => w y * maDens (Fin.cons v φ) y) := by
    simp only [e2]; exact hY2.re.const_mul c
  have i3 : Integrable (gradDens φ v w) := by
    have : gradDens φ v w = fun y => c * (∑ j, ∑ k, dz j (cplx v) y * dzb k (cplx w) y *
        hessCof φ y j k).re := funext e3
    rw [this]; exact hX1.re.const_mul c
  have g1 : ∫ y, gradDens φ v w y = c * (∫ y, ∑ j, ∑ k, dz j (cplx v) y * dzb k (cplx w) y *
      hessCof φ y j k).re := by
    simp only [e3]; rw [integral_const_mul]; congr 1; exact integral_re hX1
  have g2 : ∫ y, gradDens φ w v y = c * (∫ y, ∑ j, ∑ k, dz j (cplx w) y * dzb k (cplx v) y *
      hessCof φ y j k).re := by
    simp only [e4]; rw [integral_const_mul]; congr 1; exact integral_re hX2
  have s1 : maInt (Fin.cons w φ) v U = c * (∫ y, cplx v y * ∑ j, ∑ k, hessCof φ y j k *
      dz j (dzb k (cplx w)) y).re := by
    unfold maInt
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by simp [hvz y hy]]
    simp only [e1]; rw [integral_const_mul]; congr 1; exact integral_re hY1
  have s3 : maInt (Fin.cons v φ) w U = c * (∫ y, cplx w y * ∑ j, ∑ k, hessCof φ y j k *
      dz j (dzb k (cplx v)) y).re := by
    unfold maInt
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      rw [e2]
      have hyK : y ∉ tsupport v := fun h => hy (hKU h)
      simp [dz_of_eventually_zero ((hout y hyK).2.1 _)]]
    simp only [e2]; rw [integral_const_mul]; congr 1; exact integral_re hY2
  have s2 : gradInt φ v w U = ∫ y, gradDens φ v w y := by
    unfold gradInt
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hgz
  have r1 := congrArg Complex.re hI1
  have r2 := congrArg Complex.re hI2
  simp only [Complex.add_re, Complex.zero_re] at r1 r2
  have hs : ∫ y, gradDens φ v w y = ∫ y, gradDens φ w v y := by
    congr 1; exact funext hsym
  refine ⟨i1.integrableOn, i2.integrableOn, i3.integrableOn, ?_, ?_⟩
  · rw [s1, s2, g1]; linear_combination c * r1
  · rw [s3, s1]
    rw [g1, g2] at hs
    linear_combination c * r2 - c * r1 + hs
end ReciprocityTheory.AnForm.A
