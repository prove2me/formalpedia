-- Prove2me | solution 1 for UpperHalfPlane.denom_eq_of_smul_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/bf0ec17f-58c8-512c-b934-cc9e68eb8935

import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UpperHalfPlane_denom_eq_of_smul_eq_self

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem solution
    (g : GL (Fin 2) ℝ) (hg : Matrix.GeneralLinearGroup.det g = 1) (τ₀ : ℍ) (hfix : g • τ₀ = τ₀) :
    ‖denom g τ₀‖ = 1 ∧
    (∀ τ : ℍ, (((g • τ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) * denom g τ = ((τ : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) * denom g τ₀) ∧
    (∀ τ : ℍ, (((g • τ : ℍ) : ℂ) - (τ₀ : ℂ)) * denom g τ * denom g τ₀ = (τ : ℂ) - (τ₀ : ℂ)) ∧
    (denom g τ₀ = 1 → g = 1) ∧
    (∀ h : GL (Fin 2) ℝ, Matrix.GeneralLinearGroup.det h = 1 → h • τ₀ = τ₀ → denom (g * h) τ₀ = denom g τ₀ * denom h τ₀) := by
  have hdetpos : 0 < ((Matrix.GeneralLinearGroup.det g) : ℝ) := by rw [hg]; simp

  set a : ℂ := ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) with ha
  set b : ℂ := ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) with hb
  set c : ℂ := ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) with hc
  set d : ℂ := ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) with hd
  have hdet1 : a * d - b * c = 1 := by
    have := congrArg (fun u : ℝˣ => ((u : ℝ) : ℂ)) hg
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Units.val_one, Complex.ofReal_one,
      Complex.ofReal_sub, Complex.ofReal_mul] at this
    rw [ha, hb, hc, hd]; linear_combination this
  set z₀ : ℂ := (τ₀ : ℂ) with hz₀
  have hnum : ∀ z : ℂ, num g z = a * z + b := fun z => by simp [num, ha, hb]
  have hden : ∀ z : ℂ, denom g z = c * z + d := fun z => by simp [denom, hc, hd]
  have hd0 : denom g τ₀ ≠ 0 := denom_ne_zero g τ₀

  have hE : a * z₀ + b = z₀ * (c * z₀ + d) := by
    have h1 := coe_smul_of_det_pos hdetpos τ₀
    rw [hfix] at h1
    rw [← hnum, ← hden]
    rw [eq_div_iff hd0] at h1
    exact h1.symm
  have hconj_a : (starRingEnd ℂ) a = a := by rw [ha]; exact Complex.conj_ofReal _
  have hconj_b : (starRingEnd ℂ) b = b := by rw [hb]; exact Complex.conj_ofReal _
  have hconj_c : (starRingEnd ℂ) c = c := by rw [hc]; exact Complex.conj_ofReal _
  have hconj_d : (starRingEnd ℂ) d = d := by rw [hd]; exact Complex.conj_ofReal _
  set w₀ : ℂ := (starRingEnd ℂ) z₀ with hw₀
  have hEbar : a * w₀ + b = w₀ * (c * w₀ + d) := by
    have := congrArg (starRingEnd ℂ) hE
    simp only [map_add, map_mul, hconj_a, hconj_b, hconj_c, hconj_d] at this
    rw [hw₀]; exact this

  set ε : ℂ := denom g τ₀ with hε
  have hε' : ε = c * z₀ + d := by rw [hε, hden]
  have hnormSq : Complex.normSq ε = 1 := by
    have him := im_smul_eq_div_normSq g τ₀
    rw [hfix, hg, Units.val_one, abs_one, one_mul] at him
    have hpos : 0 < Complex.normSq (denom g τ₀) := Complex.normSq_pos.2 hd0
    have hτ : 0 < τ₀.im := τ₀.im_pos
    rw [hε]
    field_simp at him
    nlinarith [him, hpos, hτ]
  have hnorm : ‖ε‖ = 1 := by
    rw [Complex.norm_def, hnormSq, Real.sqrt_one]
  have hεconj : ε * (starRingEnd ℂ) ε = 1 := by
    rw [Complex.mul_conj, hnormSq]; simp
  have hconjε : (starRingEnd ℂ) ε = c * w₀ + d := by
    rw [hε', map_add, map_mul, hconj_c, hconj_d, hw₀]

  have hkey1 : (a - c * w₀) * (starRingEnd ℂ) ε = 1 := by
    rw [hconjε]; linear_combination hdet1 + c * hEbar
  have hkey1' : a - c * w₀ = ε := by
    have : (a - c * w₀) * (starRingEnd ℂ) ε = ε * (starRingEnd ℂ) ε := by rw [hkey1, hεconj]
    exact mul_right_cancel₀ (by rw [hconjε, ← hconjε]; intro h; rw [h, mul_zero] at hεconj; exact zero_ne_one hεconj) this
  have hkey2 : (a - c * z₀) * ε = 1 := by
    rw [hε']; linear_combination hdet1 + c * hE
  refine ⟨hnorm, ?_, ?_, ?_, ?_⟩
  · intro τ
    have h1 := coe_smul_of_det_pos hdetpos τ
    have hdτ : denom g τ ≠ 0 := denom_ne_zero g τ
    rw [h1, sub_mul, div_mul_cancel₀ _ hdτ, hnum, hden]
    linear_combination ((τ : ℂ) - w₀) * hkey1' + hEbar
  · intro τ
    have h1 := coe_smul_of_det_pos hdetpos τ
    have hdτ : denom g τ ≠ 0 := denom_ne_zero g τ
    rw [h1, sub_mul, div_mul_cancel₀ _ hdτ, hnum, hden]
    linear_combination ((τ : ℂ) - z₀) * hkey2 + ε * hE
  · intro h1

    have hc0 : ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) = 0 := by
      have := congrArg Complex.im (hε'.symm.trans h1)
      simp only [Complex.add_im, Complex.mul_im, Complex.one_im] at this
      rw [hc, hd, hz₀] at this
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, UpperHalfPlane.coe_im,
        UpperHalfPlane.coe_re] at this
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h τ₀.im_pos.ne'
    have hd1 : ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) = 1 := by
      have := congrArg Complex.re (hε'.symm.trans h1)
      simp only [Complex.add_re, Complex.mul_re, Complex.one_re] at this
      rw [hc, hd, hc0] at this
      simpa using this
    have ha1 : ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0) = 1 := by
      have := hdet1
      rw [ha, hb, hc, hd, hc0, hd1] at this
      have : (((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) : ℂ) = 1 := by simpa using this
      exact_mod_cast this
    have hb0 : ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1) = 0 := by
      have := hE
      rw [ha, hb, hc, hd, hc0, hd1, ha1] at this
      have : (((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ) : ℂ) = 0 := by
        simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, zero_add, mul_one] at this
        linear_combination this
      exact_mod_cast this
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha1, hb0, hc0, hd1]
  · intro h hh hhfix
    have hhpos : 0 < ((Matrix.GeneralLinearGroup.det h) : ℝ) := by rw [hh]; simp
    have := denom_cocycle' g h τ₀
    rw [this]
    have hσ : ∀ z : ℂ, σ h z = z := fun z => by
      have hh' : 0 < (h : Matrix (Fin 2) (Fin 2) ℝ).det := by
        rwa [Matrix.GeneralLinearGroup.val_det_apply] at hhpos
      simp [σ, hh']
    rw [hσ]
    have : smulAux h τ₀ = h • τ₀ := rfl
    rw [this, hhfix]

end S_UpperHalfPlane_denom_eq_of_smul_eq_self
end P2MW
export P2MW.S_UpperHalfPlane_denom_eq_of_smul_eq_self (solution)
