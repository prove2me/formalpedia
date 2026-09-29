-- Prove2me | solution 1 for UpperHalfPlane.cayley_smul_eq_mul_cayley
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b7622c7a-0a55-5109-b483-c21715f1f009

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UpperHalfPlane_cayley_smul_eq_mul_cayley

open UpperHalfPlane
open scoped MatrixGroups

theorem solution (γ : SL(2, ℤ)) (τ₀ : ℍ) (h : γ • τ₀ = τ₀) (τ : ℍ) :
    ((↑(γ • τ) : ℂ) - τ₀) / ((↑(γ • τ) : ℂ) - (starRingEnd ℂ) τ₀)
      = (((γ 1 0 : ℤ) : ℂ) * (starRingEnd ℂ) τ₀ + ((γ 1 1 : ℤ) : ℂ))
        / (((γ 1 0 : ℤ) : ℂ) * τ₀ + ((γ 1 1 : ℤ) : ℂ))
        * (((τ : ℂ) - τ₀) / ((τ : ℂ) - (starRingEnd ℂ) τ₀)) := by

  have hcoe : ∀ w : ℍ, ((γ • w : ℍ) : ℂ)
      = (((γ 0 0 : ℤ) : ℂ) * w + ((γ 0 1 : ℤ) : ℂ)) / (((γ 1 0 : ℤ) : ℂ) * w + ((γ 1 1 : ℤ) : ℂ)) := by
    intro w
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [algebraMap_int_eq, Int.coe_castRingHom, Complex.ofReal_intCast]

  have hden : ∀ w : ℍ, ((γ 1 0 : ℤ) : ℂ) * w + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := fun w ↦ by
    rw [← ModularGroup.denom_apply]
    exact UpperHalfPlane.denom_ne_zero _ w

  set a : ℂ := ((γ 0 0 : ℤ) : ℂ) with ha
  set b : ℂ := ((γ 0 1 : ℤ) : ℂ) with hb
  set c : ℂ := ((γ 1 0 : ℤ) : ℂ) with hc
  set d : ℂ := ((γ 1 1 : ℤ) : ℂ) with hd
  set z₀ : ℂ := (τ₀ : ℂ) with hz₀
  have hcz : c * (τ : ℂ) + d ≠ 0 := hden τ
  have hcz₀ : c * z₀ + d ≠ 0 := hden τ₀

  have hca : (starRingEnd ℂ) a = a := by rw [ha, map_intCast]
  have hcb : (starRingEnd ℂ) b = b := by rw [hb, map_intCast]
  have hcc : (starRingEnd ℂ) c = c := by rw [hc, map_intCast]
  have hcd : (starRingEnd ℂ) d = d := by rw [hd, map_intCast]
  have hcz₀' : c * (starRingEnd ℂ) z₀ + d ≠ 0 := by
    have : c * (starRingEnd ℂ) z₀ + d = (starRingEnd ℂ) (c * z₀ + d) := by
      rw [map_add, map_mul, hcc, hcd]
    rw [this, map_ne_zero]
    exact hcz₀

  have him : ∀ w : ℍ, (w : ℂ) - (starRingEnd ℂ) z₀ ≠ 0 := by
    intro w h0
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.conj_im, hz₀, UpperHalfPlane.coe_im, Complex.zero_im] at this
    linarith [w.im_pos, τ₀.im_pos]
  have hz₀z₀ : (starRingEnd ℂ) z₀ - z₀ ≠ 0 := fun h0 ↦ him τ₀ (by rw [← neg_sub, h0, neg_zero])

  have h1 : a * z₀ + b = z₀ * (c * z₀ + d) := by
    have h' := congrArg (fun w : ℍ ↦ (w : ℂ)) h
    simp only [hcoe] at h'
    rwa [div_eq_iff hcz₀] at h'
  have h2 : a * (starRingEnd ℂ) z₀ + b = (starRingEnd ℂ) z₀ * (c * (starRingEnd ℂ) z₀ + d) := by
    have h' := congrArg (starRingEnd ℂ) h1
    simp only [map_add, map_mul, hca, hcb, hcc, hcd] at h'
    exact h'

  have hA : a = c * (z₀ + (starRingEnd ℂ) z₀) + d := by
    have key : ((starRingEnd ℂ) z₀ - z₀) * (a - (c * (z₀ + (starRingEnd ℂ) z₀) + d)) = 0 := by
      linear_combination h2 - h1
    rcases mul_eq_zero.1 key with h0 | h0
    · exact absurd h0 hz₀z₀
    · exact sub_eq_zero.1 h0
  have hB : b = z₀ * (c * z₀ + d) - a * z₀ := by linear_combination h1

  have key : ∀ p q u w : ℂ, q ≠ 0 → (p / q - u) / (p / q - w) = (p - u * q) / (p - w * q) := by
    intro p q u w hq
    have e1 : p / q - u = (p - u * q) / q := by field_simp
    have e2 : p / q - w = (p - w * q) / q := by field_simp
    rw [e1, e2, div_div_div_cancel_right₀ hq]
  rw [hcoe τ, key _ _ _ _ hcz]

  have en : a * (τ : ℂ) + b - z₀ * (c * (τ : ℂ) + d) = ((τ : ℂ) - z₀) * (c * (starRingEnd ℂ) z₀ + d) := by
    rw [hB, hA]; ring
  have ed : a * (τ : ℂ) + b - (starRingEnd ℂ) z₀ * (c * (τ : ℂ) + d)
      = ((τ : ℂ) - (starRingEnd ℂ) z₀) * (c * z₀ + d) := by
    rw [hB, hA]; ring
  rw [en, ed, div_mul_div_comm]
  ring

end S_UpperHalfPlane_cayley_smul_eq_mul_cayley
end P2MW
export P2MW.S_UpperHalfPlane_cayley_smul_eq_mul_cayley (solution)
