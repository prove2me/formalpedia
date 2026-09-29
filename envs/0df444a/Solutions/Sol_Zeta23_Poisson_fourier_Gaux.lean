-- Prove2me | solution 1 for Zeta23.Poisson.fourier_Gaux
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:47:50.45891+00:00
-- url     : https://prove2.me/submissions/22e7d177-2978-4da4-a9a1-fc5025a4b74e

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Poisson
import Definitions.Def_Zeta23_Taper_Basic
import Theorems.Thm_Zeta23_Poisson_gInt_eq_zero_of_not_mem

-- from Zeta23.Poisson.PaperFT
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The paper's Fourier convention and the bound [eq:hfbound].

Reference: the paper, §2.1 [subsec:weil].
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

/-! `Zeta23.paperFT (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ u, f u * cexp (I * z * u)` is defined in
`Zeta23/Defs.lean`: the paper's convention [subsec:weil] "h_f(z) := f̂(z) = ∫ f(u) e^{izu} du",
sign `+i`, no `2π`, complex argument.  This file supplies the dictionary to Mathlib's `𝓕`
(`∫ f(v) e^{-2πi v w} dv`) and the decay bound [eq:hfbound]. -/

theorem paperFT_def (f : ℝ → ℂ) (z : ℂ) : paperFT f z = ∫ u : ℝ, f u * cexp (I * z * u) := rfl

/-! Mathlib's `integral_const_mul` / `integral_mul_const` are stated for a general `RCLike L`,
and their instance path (RCLike-derived `NormedAddCommGroup ℂ`) does not match the
directly-synthesized `Complex.instNormedAddCommGroup` under `rw`'s reducible unification.
These ℂ-specialized restatements (same proofs) rewrite reliably. -/

theorem integral_const_mul_C (r : ℂ) (f : ℝ → ℂ) : (∫ a, r * f a) = r * ∫ a, f a :=
  integral_const_mul r f

theorem integral_mul_const_C (r : ℂ) (f : ℝ → ℂ) : (∫ a, f a * r) = (∫ a, f a) * r :=
  integral_mul_const r f



/-! ### [eq:hfbound]

"`|h_f(x+iy)| ≤ e^{|y|Λ_f} min(‖f‖₁, ‖f''‖₁ |x+iy|⁻²)`, `supp f ⊂ [−Λ_f, Λ_f]`, by two integrations
by parts (`h_f(z) = (iz)⁻² ∫ f''(u) e^{izu} du` and `|e^{izu}| = e^{−yu} ≤ e^{|y|Λ_f}` on
`supp f`)."  We prove the two bounds separately, in multiplied-out form. -/










end Zeta23
end

-- from Zeta23.Poisson
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
[lem:poisson] "Poisson summation for the Gabor system", the paper §2.2:

  "For all τ, τ' ∈ ℝ,
     K_∞(τ,τ') := Σ_{k∈ℤ} φ̂(τ−τ_k) φ̂(τ'−τ_k) = L·Φ(τ−τ'),   in particular   Σ_{k∈ℤ} φ̂(τ−τ_k)² = aL²."

Here τ_k := T + k h, h := 2π/L [eq:fk], Φ := (φ²)^ [eq:PhigA], a := L⁻¹∫φ² [eq:abdef], and
φ̂(s) = ∫ φ(u) e^{isu} du is the paper's Fourier convention (`Zeta23.paperFT`).  Only the
real-argument identity is proved (that is all [prop:block](ii) uses; the complex continuation
mentioned in [rem:pairblock] is not used by the proof).

Proof route (the paper's, rearranged so that Fourier inversion is not needed): with
  G(ξ) := L · ∫ φ(u) φ(Lξ−u) e^{i(τu + τ'(Lξ−u) − TLξ)} du      (= L e^{−iTLξ}(φ_τ ∗ φ_{τ'})(Lξ)),
G is continuous with support in [−1,1] and G(k) = 0 for k ∈ ℤ∖{0} (because φ(u) = 0 for
|u| ≥ L/2), G(0) = L ∫ φ(u)φ(−u)e^{i(τ−τ')u} du = L Φ(τ−τ') (φ even), and a Fubini computation
gives 𝓕G(w) = φ̂(τ−τ_w) φ̂(τ'−τ_w) for Mathlib's 𝓕 and every real w (τ_w := T + w·2π/L).
Mathlib's Poisson summation `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`
(Σ_k G(k) = Σ_n 𝓕G(n)) then gives the claim; summability of n ↦ φ̂(τ−τ_n)φ̂(τ'−τ_n) comes from
the decay |φ̂(r)| ≪ (1+r²)⁻¹, i.e. [eq:hfbound]/[eq:psidef].
-/

open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform

namespace Zeta23

namespace Poisson

/-! #### A decay-to-`IsBigO` lemma -/


/-! #### The auxiliary function `G` -/

variable (φ : ℝ → ℝ) (L T τ τ' : ℝ)



variable {φ L T τ τ'}


theorem gInt_continuous (hφc : Continuous φ) :
    Continuous (Function.uncurry (gInt φ L T τ τ')) := by
  unfold gInt Function.uncurry
  fun_prop

theorem gInt_hasCompactSupport (hL : 0 < L) (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) :
    HasCompactSupport (Function.uncurry (gInt φ L T τ τ')) := by
  refine HasCompactSupport.of_support_subset_isCompact
    ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod (isCompact_Icc (a := -(L / 2)) (b := L / 2))) ?_
  rintro ⟨ξ, u⟩ hne
  rw [Function.mem_support, Function.uncurry_apply_pair] at hne
  by_contra hmem
  apply hne (gInt_eq_zero_of_not_mem hL hsupp _)
  rintro ⟨h1, h2⟩
  apply hmem
  rw [mem_prod, mem_Icc, mem_Icc]
  exact ⟨⟨by linarith [neg_abs_le ξ], by linarith [le_abs_self ξ]⟩,
    ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩⟩





/-- The exponent bookkeeping: for `L ≠ 0`,
`e^{i(τu + τ'(Lξ−u) − TLξ)} · e^{−2πiξw} = e^{iαu} · e^{iβ(Lξ−u)}` with
`α = τ − (T + w·2π/L)`, `β = τ' − (T + w·2π/L)`. -/
theorem cexp_bookkeeping (hL : L ≠ 0) (ξ u w : ℝ) :
    cexp (I * (τ * u + τ' * (L * ξ - u) - T * L * ξ)) * cexp (↑(-2 * π * ξ * w) * I)
      = cexp (I * ↑(τ - (T + w * (2 * π / L))) * u)
        * cexp (I * ↑(τ' - (T + w * (2 * π / L))) * ↑(L * ξ - u)) := by
  have hL' : (L : ℂ) ≠ 0 := ofReal_ne_zero.mpr hL
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring


/-! #### The abstract identity -/


end Poisson

namespace Taper

variable {ϱ : ℝ → ℝ} {L w : ℝ}




end Taper

namespace Params

variable {P : Params} {T : ℝ}


variable (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
include hP hwL




end Params

end Zeta23
open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform
open Zeta23
open Poisson
variable (φ : ℝ → ℝ) (L T τ τ' : ℝ)
variable {φ L T τ τ'}

theorem solution (hL : 0 < L) (hφc : Continuous φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) (w : ℝ) :
    𝓕 (Gaux φ L T τ τ') w
      = paperFT (fun u => (φ u : ℂ)) ((τ - (T + w * (2 * π / L)) : ℝ) : ℂ)
        * paperFT (fun u => (φ u : ℂ)) ((τ' - (T + w * (2 * π / L)) : ℝ) : ℂ) := by
  set α : ℝ := τ - (T + w * (2 * π / L)) with hα
  set β : ℝ := τ' - (T + w * (2 * π / L)) with hβ
  -- the integrand after multiplying in the character
  set J : ℝ → ℝ → ℂ := fun ξ u => cexp (↑(-2 * π * ξ * w) * I) * gInt φ L T τ τ' ξ u with hJ
  have hJint : Integrable (Function.uncurry J) (volume.prod volume) := by
    have hc : Continuous (Function.uncurry J) := by
      have := gInt_continuous (L := L) (T := T) (τ := τ) (τ' := τ') hφc
      simp only [hJ]
      apply Continuous.mul _ this
      fun_prop
    apply hc.integrable_of_hasCompactSupport
    apply (gInt_hasCompactSupport (T := T) (τ := τ) (τ' := τ') hL hsupp).mono
    intro p hp
    rw [Function.mem_support] at hp ⊢
    intro h0
    apply hp
    simp only [hJ, Function.uncurry] at h0 ⊢
    rw [show p = (p.1, p.2) from rfl] at h0
    simp only at h0
    rw [h0, mul_zero]
  -- Step 1: unfold 𝓕 and move the character inside
  rw [Real.fourier_real_eq_integral_exp_smul]
  have step1 : (fun ξ : ℝ => cexp (↑(-2 * π * ξ * w) * I) • Gaux φ L T τ τ' ξ)
      = fun ξ => ∫ u, J ξ u := by
    funext ξ
    rw [smul_eq_mul, Gaux, hJ]
    beta_reduce
    rw [integral_const_mul_C]
  rw [step1]
  -- Step 2: swap the integrals
  rw [integral_integral_swap hJint]
  -- Step 3: compute the inner integral
  have step3 : ∀ u : ℝ, ∫ ξ, J ξ u
      = (φ u : ℂ) * cexp (I * α * u) * paperFT (fun v => (φ v : ℂ)) β := by
    intro u
    -- F0 v := φ(v) e^{iβv};  the ξ-integrand is φ(u)e^{iαu} · L · F0(Lξ − u)
    set F0 : ℝ → ℂ := fun v => (φ v : ℂ) * cexp (I * β * (v : ℂ)) with hF0
    have hpt : ∀ ξ : ℝ, J ξ u = (φ u : ℂ) * cexp (I * α * u)
        * ((L : ℂ) * ((fun y : ℝ => F0 (y - u)) (L * ξ))) := by
      intro ξ
      simp only [hJ, gInt, hF0]
      have := cexp_bookkeeping (T := T) (τ := τ) (τ' := τ') hL.ne' ξ u w
      rw [← hα, ← hβ] at this
      calc cexp (↑(-2 * π * ξ * w) * I) * (↑L * (↑(φ u) * ↑(φ (L * ξ - u))
              * cexp (I * (↑τ * ↑u + ↑τ' * (↑L * ↑ξ - ↑u) - ↑T * ↑L * ↑ξ))))
          = ↑L * ↑(φ u) * ↑(φ (L * ξ - u)) * (cexp (I * (↑τ * ↑u + ↑τ' * (↑L * ↑ξ - ↑u)
              - ↑T * ↑L * ↑ξ)) * cexp (↑(-2 * π * ξ * w) * I)) := by ring
        _ = ↑L * ↑(φ u) * ↑(φ (L * ξ - u)) * (cexp (I * ↑α * ↑u) * cexp (I * ↑β * ↑(L * ξ - u))) := by
              rw [this]
        _ = _ := by push_cast; ring
    have hint : ∫ ξ, J ξ u = ∫ ξ, (φ u : ℂ) * cexp (I * α * u)
        * ((L : ℂ) * ((fun y : ℝ => F0 (y - u)) (L * ξ))) := by
      congr 1 with ξ; exact hpt ξ
    rw [hint, integral_const_mul_C, integral_const_mul_C,
      Measure.integral_comp_mul_left (fun y : ℝ => F0 (y - u)) L,
      integral_sub_right_eq_self F0 u, paperFT_def, abs_of_pos (inv_pos.mpr hL)]
    congr 1
    rw [← Complex.coe_smul, smul_eq_mul, ← mul_assoc, ofReal_inv,
      mul_inv_cancel₀ (ofReal_ne_zero.mpr hL.ne'), one_mul]
  simp_rw [step3]
  -- Step 4: pull the constant out of the outer integral
  rw [integral_mul_const_C, paperFT_def, paperFT_def]
