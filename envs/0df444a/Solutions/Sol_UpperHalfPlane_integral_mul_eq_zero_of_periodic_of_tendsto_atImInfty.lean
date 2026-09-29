-- Prove2me | solution 1 for UpperHalfPlane.integral_mul_eq_zero_of_periodic_of_tendsto_atImInfty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/3952a263-7215-5da3-bf97-87cbe4974bec

import Mathlib
import Theorems.Thm_UpperHalfPlane_intervalIntegral_eq_zero_of_periodic_of_tendsto_atImInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UpperHalfPlane_integral_mul_eq_zero_of_periodic_of_tendsto_atImInfty

open UpperHalfPlane Complex Filter MeasureTheory Set
open scoped Topology

namespace StripUnfolding

theorem vadd_ofComplex {x y : ℝ} (hy : 0 < y) :
    (1 : ℝ) +ᵥ ofComplex ((x : ℂ) + y * Complex.I) = ofComplex (((x + 1 : ℝ) : ℂ) + y * Complex.I) := by
  have h1 : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy
  have h2 : 0 < (((x + 1 : ℝ) : ℂ) + y * Complex.I).im := by simpa using hy
  apply UpperHalfPlane.ext
  rw [coe_vadd, ofComplex_apply_of_im_pos h1, ofComplex_apply_of_im_pos h2, coe_mk, coe_mk]
  push_cast
  ring

theorem section_eq_zero (ω : ℍ → ℂ) (Y : ℝ) (hY : 0 ≤ Y)
    (hper : ∀ τ : ℍ, ω ((1 : ℝ) +ᵥ τ) = ω τ)
    (hcusp : Tendsto ω atImInfty (𝓝 0))
    (hhol : ∀ τ : ℍ, Y < τ.im → ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = g z)
    (p ρ : ℝ → ℝ) (hp : Function.support p ⊆ Ioo (-1) 1)
    (hp1 : ∀ x ∈ Icc (0 : ℝ) 1, p (x - 1) + p x = 1)
    (hρ : Function.support ρ ⊆ Ioi Y) (y : ℝ)
    (hyi : Integrable fun x : ℝ => ω (ofComplex (x + y * Complex.I)) * (p x * ρ y : ℝ)) :
    ∫ x : ℝ, ω (ofComplex (x + y * Complex.I)) * (p x * ρ y : ℝ) = 0 := by
  by_cases hρy : ρ y = 0
  · simp [hρy]
  have hy : Y < y := hρ hρy
  have hy0 : 0 < y := hY.trans_lt hy
  set W : ℝ → ℂ := fun x => ω (ofComplex (x + y * Complex.I)) with hW
  set g : ℝ → ℂ := fun x => (p x : ℂ) * W x with hg
  have hρC : (ρ y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρy
  have hgi : Integrable g := by
    refine (hyi.const_mul ((ρ y : ℂ)⁻¹)).congr (ae_of_all _ fun x => ?_)
    simp only [hg, hW]
    push_cast
    field_simp
  have hWper : ∀ x : ℝ, W (x + 1) = W x := by
    intro x
    simp only [hW]
    rw [← hper (ofComplex (x + y * Complex.I)), vadd_ofComplex hy0]
  have hshift : ∀ x : ℝ, g (x - 1) = (p (x - 1) : ℂ) * W x := by
    intro x
    simp only [hg]
    rw [← hWper (x - 1), sub_add_cancel]
  have hsupp : Function.support g ⊆ Ioc (-1 : ℝ) 1 := by
    intro x hx
    have hx' : p x ≠ 0 := fun h0 => hx (by simp [hg, h0])
    exact Ioo_subset_Ioc_self (hp hx')
  have hfold : ∫ x, g x = ∫ x in (0 : ℝ)..1, W x := by
    rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupp,
      ← intervalIntegral.integral_add_adjacent_intervals (b := 0) hgi.intervalIntegrable
        hgi.intervalIntegrable]
    have h1 : ∫ x in (-1 : ℝ)..0, g x = ∫ x in (0 : ℝ)..1, g (x - 1) := by
      rw [intervalIntegral.integral_comp_sub_right g 1]
      norm_num
    rw [h1, ← intervalIntegral.integral_add (hgi.comp_sub_right 1).intervalIntegrable
      hgi.intervalIntegrable]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    show g (x - 1) + g x = W x
    rw [hshift]
    simp only [hg]
    rw [← add_mul, ← Complex.ofReal_add, hp1 x hx, Complex.ofReal_one, one_mul]
  calc ∫ x : ℝ, W x * ((p x * ρ y : ℝ) : ℂ) = (ρ y : ℂ) * ∫ x, g x := by
        rw [← integral_const_mul]
        congr 1 with x
        simp only [hg]
        push_cast
        ring
    _ = 0 := by
        rw [hfold, UpperHalfPlane.intervalIntegral_eq_zero_of_periodic_of_tendsto_atImInfty ω Y hY
          hper hcusp hhol y hy, mul_zero]

end StripUnfolding

open StripUnfolding in
theorem solution
    (ω : ℍ → ℂ) (Y : ℝ) (hY : 0 ≤ Y)
    (hper : ∀ τ : ℍ, ω ((1 : ℝ) +ᵥ τ) = ω τ)
    (hcusp : Tendsto ω atImInfty (𝓝 0))
    (hhol : ∀ τ : ℍ, Y < τ.im → ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = g z)
    (p ρ : ℝ → ℝ) (hp : Function.support p ⊆ Ioo (-1) 1)
    (hp1 : ∀ x ∈ Icc (0 : ℝ) 1, p (x - 1) + p x = 1)
    (hρ : Function.support ρ ⊆ Ioi Y)
    (hint : Integrable fun z : ℂ => ω (ofComplex z) * (p z.re * ρ z.im : ℝ)) :
    ∫ z : ℂ, ω (ofComplex z) * (p z.re * ρ z.im : ℝ) = 0 := by
  have hmp : MeasurePreserving (⇑Complex.measurableEquivRealProd.symm) volume volume :=
    Complex.volume_preserving_equiv_real_prod.symm _
  have hme := Complex.measurableEquivRealProd.symm.measurableEmbedding
  set f : ℂ → ℂ := fun z => ω (ofComplex z) * (p z.re * ρ z.im : ℝ) with hf
  have hint' : Integrable (fun q : ℝ × ℝ => f (Complex.measurableEquivRealProd.symm q))
      (volume.prod volume) := (hmp.integrable_comp_emb hme).2 hint
  have hfq : ∀ q : ℝ × ℝ, f (Complex.measurableEquivRealProd.symm q) =
      ω (ofComplex (q.1 + q.2 * Complex.I)) * ((p q.1 * ρ q.2 : ℝ) : ℂ) := by
    intro q
    simp only [hf, Complex.measurableEquivRealProd_symm_apply, Complex.mk_eq_add_mul_I]
    congr 3 <;> simp
  have hint'' : Integrable (fun q : ℝ × ℝ => ω (ofComplex (q.1 + q.2 * Complex.I)) * ((p q.1 * ρ q.2 : ℝ) : ℂ))
      (volume.prod volume) := hint'.congr (ae_of_all _ hfq)
  calc ∫ z, f z = ∫ q : ℝ × ℝ, f (Complex.measurableEquivRealProd.symm q) :=
        (hmp.integral_comp hme f).symm
    _ = ∫ q : ℝ × ℝ, ω (ofComplex (q.1 + q.2 * Complex.I)) * ((p q.1 * ρ q.2 : ℝ) : ℂ)
          ∂(volume.prod volume) := integral_congr_ae (ae_of_all _ hfq)
    _ = ∫ y : ℝ, ∫ x : ℝ, ω (ofComplex (x + y * Complex.I)) * ((p x * ρ y : ℝ) : ℂ) :=
        integral_prod_symm _ hint''
    _ = 0 := integral_eq_zero_of_ae (hint''.prod_left_ae.mono fun y hy =>
        section_eq_zero ω Y hY hper hcusp hhol p ρ hp hp1 hρ y hy)

end S_UpperHalfPlane_integral_mul_eq_zero_of_periodic_of_tendsto_atImInfty
end P2MW
export P2MW.S_UpperHalfPlane_integral_mul_eq_zero_of_periodic_of_tendsto_atImInfty (solution)
