-- Prove2me | solution 1 for Zeta23.MV.norm_B_le_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:19:47.270997+00:00
-- url     : https://prove2.me/submissions/c7e8d516-42c2-4c3c-87a4-1df75328de97

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_MV
import Theorems.Thm_Zeta23_MV_N2_polar

-- from Zeta23.MV
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/MV.lean — the Montgomery–Vaughan weighted Hilbert inequality: literature (diagonal, y = x)
form ⇒ the bilinear (x, z) form H-MV of Zeta23/Hypotheses.lean.

Purpose (trust reduction): Zeta23.MVHilbert C — what [prop:PP]/[prop:cross] consume —
is the BILINEAR inequality |Σ_{r≠s} x_r z̄_s/(λ_r−λ_s)| ≤ C (Σ|x_r|²/δ_r)^{1/2} (Σ|z_r|²/δ_r)^{1/2}.
The published theorem is the case z = x.  The paper, [lem:MV] and its proof,
verbatim: "Lemma (Montgomery–Vaughan). Let λ_1,…,λ_R be distinct real numbers and
δ_r := min_{s≠r}|λ_r−λ_s|. Then for all complex x_r, z_r,
  |Σ_{r≠s} x_r z̄_s/(λ_r−λ_s)| ≤ (3π/2)(Σ_r |x_r|²/δ_r)^{1/2}(Σ_r |z_r|²/δ_r)^{1/2}.
Proof. For z = x this is the weighted ("generalised") Hilbert inequality of Montgomery and Vaughan
[MV74, Theorem 2]; see also [Mon94, Chapter 7]. Any absolute constant in place of 3π/2 would
suffice below. In general, let H be the Hermitian matrix with entries i/(λ_r−λ_s) off the
diagonal and 0 on it, and Δ := diag(δ_r^{1/2}). The case z = x says |y*(ΔHΔ)y| ≤ (3π/2)‖y‖₂² for
all y, i.e. ‖ΔHΔ‖ ≤ 3π/2 since ΔHΔ is Hermitian; hence
|x*Hz| = |(Δ⁻¹x)*(ΔHΔ)(Δ⁻¹z)| ≤ (3π/2)‖Δ⁻¹x‖₂‖Δ⁻¹z‖₂."

Literature statement transcribed (H. L. Montgomery and R. C. Vaughan, "Hilbert's inequality",
J. London Math. Soc. (2) 8 (1974), 73–82, Theorem 2 = the "generalised" weighted form, their
(1.8)): if λ_1,…,λ_R are distinct reals, δ_r := min_{s≠r}|λ_r − λ_s|, then for all complex x_r,
  |Σ_{r≠s} x_r x̄_s / (λ_r − λ_s)| ≤ (3π/2) Σ_r |x_r|²/δ_r.
(The constant 3π/2 was later improved — Preissmann 1984 — but the paper says any absolute
constant suffices, and the headline result only needs ∃ C, so C is kept abstract: MVDiag C.)
As in Zeta23.MVHilbert we allow any admissible δ (δ_r > 0, δ_r ≤ |λ_r − λ_s| for s ≠ r); the right
side is antitone in δ, so this is equivalent to the min-gap δ of the literature.

We derive the bilinear form with constant 2C (not C) by POLARIZATION of the sesquilinear form plus
the scaling x ↦ t x, z ↦ z/t — an elementary route that avoids operator norms; the factor 2 is
immaterial (∃ C).  Result: Zeta23.MVHilbert_of_diag : 0 ≤ C → MVDiag C → MVHilbert (2 * C), and
Zeta23.exists_MVHilbert_of_diag for the ∃-forms used by PaperInputs.MV.
-/

noncomputable section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Zeta23


namespace MV

variable {ι : Type} [Fintype ι] [DecidableEq ι]





/-- Polarization, termwise (sesquilinear, two index slots):
4 a b̄' = (a+b)(a'+b')^* − (a−b)(a'−b')^* + i(a+ib)(a'+ib')^* − i(a−ib)(a'−ib')^*. -/
lemma polar_term (a b a' b' : ℂ) :
    a * conj b' = (1 / 4 : ℂ) * ((a + b) * conj (a' + b') - (a - b) * conj (a' - b')
      + I * ((a + I * b) * conj (a' + I * b')) - I * ((a - I * b) * conj (a' - I * b'))) := by
  simp only [map_add, map_sub, map_mul, Complex.conj_I]
  have hI : I * I = -1 := Complex.I_mul_I
  linear_combination ((1/2 : ℂ) * a * conj b' - (1/2 : ℂ) * b * conj a') * hI

/-- Polarization of B. -/
lemma B_polar (freq : ι → ℝ) (x z : ι → ℂ) :
    B freq x z = (1 / 4 : ℂ) * (B freq (x + z) (x + z) - B freq (x - z) (x - z)
      + I * B freq (x + I • z) (x + I • z) - I * B freq (x - I • z) (x - I • z)) := by
  unfold B
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sum, ← sum_sub_distrib,
    ← sum_add_distrib]
  refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
  rw [polar_term (x r) (z r) (x s) (z s)]
  ring










end MV



end Zeta23
end
open Finset Complex
open scoped BigOperators ComplexConjugate
open Zeta23
open MV
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem solution {C : ℝ} (_hC : 0 ≤ C) {freq δ : ι → ℝ}
    (hdiag : ∀ y : ι → ℂ, ‖B freq y y‖ ≤ C * N2 δ y) (x z : ι → ℂ) :
    ‖B freq x z‖ ≤ C * (N2 δ x + N2 δ z) := by
  rw [B_polar]
  have h4 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
  calc ‖(1 / 4 : ℂ) * (B freq (x + z) (x + z) - B freq (x - z) (x - z)
        + I * B freq (x + I • z) (x + I • z) - I * B freq (x - I • z) (x - I • z))‖
      ≤ (1 / 4) * (‖B freq (x + z) (x + z)‖ + ‖B freq (x - z) (x - z)‖
        + ‖B freq (x + I • z) (x + I • z)‖ + ‖B freq (x - I • z) (x - I • z)‖) := by
        rw [norm_mul, h4]
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        · refine (norm_add_le _ _).trans ?_
          gcongr
          · exact norm_sub_le _ _
          · rw [norm_mul, Complex.norm_I, one_mul]
        · rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ (1 / 4) * (C * N2 δ (x + z) + C * N2 δ (x - z) + C * N2 δ (x + I • z)
        + C * N2 δ (x - I • z)) := by gcongr <;> exact hdiag _
    _ = C * (N2 δ x + N2 δ z) := by
        have := N2_polar δ x z
        linear_combination (C / 4) * this
