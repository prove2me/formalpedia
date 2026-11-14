-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P52.valence_projection_gives_cluster
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T04:17:57.289908+00:00
-- url     : https://prove2.me/submissions/69a2bd0d-6b63-4ba6-8eab-ba3da86ecb60

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_graphClusterState_isState
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_valenceProjection_coordinates
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52
noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Intakenext100.P52 QAlgorithms.Papers.Independent.Information100.P21 QAlgorithms.Papers.Independent.Gap20.P01
open scoped Matrix ComplexConjugate

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Intakenext100.P52
noncomputable section

open scoped Matrix ComplexConjugate



open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Lemma 3, PDF p.17: rectangular grids, including nontrivial 1D rows.
Every site is incident to a bond, since the source's bond-only resource does
not specify a degree-zero local state. Nonzero norm is a conclusion.
The exact coefficient is (sqrt(2))^V / 2^E, so normalization is well-defined. -/
theorem solution (r c : ℕ)
    (hincident : ∀ v : RectangularSites r c, ∃ e ∈ gridEdges r c, e.1 = v ∨ e.2 = v) :
    let E := gridEdges r c
    let v := applyRect (valenceProjection E) (bondGrid E)
    let factor : ℝ := (Real.sqrt 2) ^ (r*c) / (2 : ℝ) ^ E.card
    v = (factor : ℂ) • graphClusterState E ∧ 0 < factor ∧ ‖v‖ = factor ∧
    v ≠ 0 ∧ ((factor : ℂ)⁻¹) • v = graphClusterState E := by
  dsimp only
  let E := gridEdges r c
  let factor : ℝ := (Real.sqrt 2) ^ (r*c) / (2 : ℝ) ^ E.card
  have hf : 0 < factor := div_pos (pow_pos (Real.sqrt_pos.mpr (by norm_num)) _)
    (pow_pos (by norm_num) _)
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hc : (1 / 2 : ℂ)^E.card = (factor : ℂ) * (((Real.sqrt 2)⁻¹ : ℂ) ^ (r*c)) := by
    dsimp only [factor]
    push_cast
    rw [div_eq_mul_inv]
    calc
      _ = ((2 : ℂ)^E.card)⁻¹ := by simp [div_eq_mul_inv, inv_pow]
      _ = ((((Real.sqrt 2 : ℝ) : ℂ)^(r*c)) *
          (((Real.sqrt 2 : ℝ) : ℂ)⁻¹)^(r*c)) * ((2 : ℂ)^E.card)⁻¹ := by
        rw [← mul_pow, mul_inv_cancel₀ hs, one_pow, one_mul]
      _ = _ := by ring
  have hv : applyRect (valenceProjection E) (bondGrid E) =
      (factor : ℂ) • graphClusterState E := by
    ext x
    rw [valenceProjection_coordinates]
    simp only [PiLp.smul_apply, graphClusterState, PiLp.toLp_apply, smul_eq_mul,
      Fintype.card_prod, Fintype.card_fin]
    rw [← mul_assoc, ← hc]
  have hn : ‖applyRect (valenceProjection E) (bondGrid E)‖ = factor := by
    rw [hv, norm_smul, show ‖graphClusterState E‖ = 1 from graphClusterState_isState E,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hf]
  refine ⟨hv, hf, hn, ?_, ?_⟩
  · intro hz
    rw [hz, norm_zero] at hn
    exact hf.ne' hn.symm
  · change ((factor : ℂ)⁻¹) • applyRect (valenceProjection E) (bondGrid E) = _
    rw [hv, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hf.ne'), one_smul]
