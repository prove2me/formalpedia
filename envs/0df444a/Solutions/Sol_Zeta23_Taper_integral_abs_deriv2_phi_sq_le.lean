-- Prove2me | solution 1 for Zeta23.Taper.integral_abs_deriv2_phi_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T02:14:38.085799+00:00
-- url     : https://prove2.me/submissions/ca22a438-9b1e-4c0f-bcaf-8df123fa9199

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Taper_Basic
import Theorems.Thm_Zeta23_Taper_abs_deriv_phi_le
import Theorems.Thm_Zeta23_Taper_integral_abs_deriv2_phi
import Theorems.Thm_Zeta23_Taper_integral_abs_deriv_phi
import Theorems.Thm_Zeta23_Taper_phi_contDiff
import Theorems.Thm_Zeta23_Taper_phi_support_subset

-- from Zeta23.Taper.Basic
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Basic.lean.  Definitions of the test family
[subsec:family] for generic parameters (ϱ : ℝ → ℝ) (L w : ℝ), and the basic facts of the sentence
after [eq:phidef].  Bodies are literally those of Zeta23/Defs.lean so that
P.phi T = Taper.phi P.ϱ (P.L T) P.w etc. are rfl (bridges in Zeta23/Taper.lean).

Sub-file map (umbrella = Zeta23/Taper.lean):
  Basic   — defs, support/plateau/evenness/C³
  Norms   — [eq:phinorms], [eq:abdef], c_ϱ, C₁, smoothstep
  Strip   — [eq:hfbound] specialized to φ
  Decay   — [eq:gbounds], [eq:psidef], [eq:psiints]
  Fourier — φ̂, Φ real/even/continuous, [eq:PhigA] facts, Plancherel, [eq:Phi2FT]
  Zeta23/Taper.lean — umbrella + the consumer-facing `Params` layer
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

theorem TaperProfile.nonneg {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) (x : ℝ) : 0 ≤ ϱ x := by
  rw [← hϱ.eq_zero 0 le_rfl]
  rcases le_total 0 x with h | h
  · exact hϱ.monotone h
  · rw [hϱ.eq_zero x h, hϱ.eq_zero 0 le_rfl]

theorem TaperProfile.le_one {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) (x : ℝ) : ϱ x ≤ 1 := by
  rw [← hϱ.eq_one 1 le_rfl]
  rcases le_total x 1 with h | h
  · exact hϱ.monotone h
  · rw [hϱ.eq_one x h, hϱ.eq_one 1 le_rfl]


namespace Taper

/-! ### Constants depending only on ϱ  [eq:phinorms] -/




theorem cRho_eq (ϱ : ℝ → ℝ) : cRho ϱ = 4 * supDeriv ϱ + 4 * l1Deriv2 ϱ := rfl


/-! ### The taper φ [eq:phidef], a, b [eq:abdef], Φ, g, A_φ [eq:PhigA], ψ [eq:psidef] -/

variable (ϱ : ℝ → ℝ) (L w : ℝ)











/-! ### Basic properties of φ (the sentence after [eq:phidef]):
"`φ ∈ C_c³(ℝ)` is even, `0 ≤ φ ≤ 1`, `supp φ = [−L/2, L/2]`, `φ = 1` on `[−L/2+w, L/2−w]`" -/

section Basic
variable {ϱ L w}


theorem phi_nonneg (hϱ : TaperProfile ϱ) (u : ℝ) : 0 ≤ phi ϱ L w u := hϱ.nonneg _

theorem phi_le_one (hϱ : TaperProfile ϱ) (u : ℝ) : phi ϱ L w u ≤ 1 := hϱ.le_one _




theorem phi_hasCompactSupport (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    HasCompactSupport (phi ϱ L w) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (phi_support_subset hϱ hw)





end Basic



end Taper

end Zeta23
end

-- from Zeta23.Taper.Norms
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

namespace Taper


/-! ### [eq:phinorms] -/

section Norms
variable {ϱ : ℝ → ℝ} {L w : ℝ}





















lemma deriv_phi_contDiff (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 2 (deriv (phi ϱ L w)) :=
  (phi_contDiff hϱ hw hwL).deriv' (n := 2)









end Norms

/-! ### [eq:abdef]: "`1 − 2w/L ≤ b ≤ a ≤ 1`" -/

section AB
variable {ϱ : ℝ → ℝ} {L w : ℝ}







end AB


end Taper

end Zeta23
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
open Zeta23
open Taper
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem solution (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) :
    ∫ u, |deriv (deriv (fun u => phi ϱ L w u ^ 2)) u| ≤ cRho ϱ / w := by
  have hw0 : (0 : ℝ) < w := by linarith
  have hφ := phi_contDiff hϱ hw0 hwL
  have hφd : Differentiable ℝ (phi ϱ L w) := hφ.differentiable (by norm_num)
  have hφ'c : ContDiff ℝ 2 (deriv (phi ϱ L w)) := deriv_phi_contDiff hϱ hw0 hwL
  have hφ'd : Differentiable ℝ (deriv (phi ϱ L w)) := hφ'c.differentiable (by norm_num)
  have hφ'cont : Continuous (deriv (phi ϱ L w)) := hφ'c.continuous
  have hφ''cont : Continuous (deriv (deriv (phi ϱ L w))) := hφ'c.continuous_deriv (by norm_num)
  have hφcs := phi_hasCompactSupport hϱ (L := L) hw0
  have hφ'cs : HasCompactSupport (deriv (phi ϱ L w)) := hφcs.deriv
  have hφ''cs : HasCompactSupport (deriv (deriv (phi ϱ L w))) := hφ'cs.deriv
  have hsq1 : deriv (fun v => phi ϱ L w v ^ 2)
      = fun v => 2 * phi ϱ L w v * deriv (phi ϱ L w) v := by
    funext v
    have hd : HasDerivAt (phi ϱ L w) (deriv (phi ϱ L w) v) v := (hφd v).hasDerivAt
    have hpow : HasDerivAt (fun x => phi ϱ L w x ^ 2)
        ((2 : ℕ) * phi ϱ L w v ^ (2 - 1) * deriv (phi ϱ L w) v) v := hd.pow 2
    rw [hpow.deriv]
    norm_num
  have hid : ∀ u : ℝ, deriv (deriv (fun v => phi ϱ L w v ^ 2)) u
      = 2 * deriv (phi ϱ L w) u * deriv (phi ϱ L w) u
        + 2 * phi ϱ L w u * deriv (deriv (phi ϱ L w)) u := by
    intro u
    rw [hsq1]
    have h1 : HasDerivAt (fun v => 2 * phi ϱ L w v) (2 * deriv (phi ϱ L w) u) u :=
      (hφd u).hasDerivAt.const_mul 2
    have h2 : HasDerivAt (deriv (phi ϱ L w)) (deriv (deriv (phi ϱ L w)) u) u :=
      (hφ'd u).hasDerivAt
    have h3 : HasDerivAt (fun v => 2 * phi ϱ L w v * deriv (phi ϱ L w) v)
        (2 * deriv (phi ϱ L w) u * deriv (phi ϱ L w) u
          + 2 * phi ϱ L w u * deriv (deriv (phi ϱ L w)) u) u := by
      exact h1.mul h2
    rw [h3.deriv]
  have hint_absphi' : MeasureTheory.Integrable (fun u => |deriv (phi ϱ L w) u|) :=
    (hφ'cont.abs).integrable_of_hasCompactSupport
      (hφ'cs.comp_left (g := fun t => |t|) abs_zero)
  have hint_absphi'' : MeasureTheory.Integrable (fun u => |deriv (deriv (phi ϱ L w)) u|) :=
    (hφ''cont.abs).integrable_of_hasCompactSupport
      (hφ''cs.comp_left (g := fun t => |t|) abs_zero)
  have hφsqc : ContDiff ℝ 3 (fun v => phi ϱ L w v ^ 2) := hφ.pow 2
  have hφsq''cont : Continuous (deriv (deriv (fun v => phi ϱ L w v ^ 2))) :=
    (hφsqc.deriv' (n := 2)).continuous_deriv (by norm_num)
  have hφsqcs : HasCompactSupport (fun v => phi ϱ L w v ^ 2) :=
    hφcs.comp_left (g := fun t => t ^ 2) (by norm_num)
  have hφsq''cs : HasCompactSupport (deriv (deriv (fun v => phi ϱ L w v ^ 2))) :=
    hφsqcs.deriv.deriv
  have hint_lhs : MeasureTheory.Integrable
      (fun u => |deriv (deriv (fun v => phi ϱ L w v ^ 2)) u|) :=
    (hφsq''cont.abs).integrable_of_hasCompactSupport
      (hφsq''cs.comp_left (g := fun t => |t|) abs_zero)
  have hmaj : MeasureTheory.Integrable
      (fun u => 2 * (supDeriv ϱ / w) * |deriv (phi ϱ L w) u|
        + 2 * |deriv (deriv (phi ϱ L w)) u|) :=
    (hint_absphi'.const_mul _).add (hint_absphi''.const_mul 2)
  calc ∫ u, |deriv (deriv (fun u => phi ϱ L w u ^ 2)) u|
      ≤ ∫ u, (2 * (supDeriv ϱ / w) * |deriv (phi ϱ L w) u|
          + 2 * |deriv (deriv (phi ϱ L w)) u|) := by
        refine MeasureTheory.integral_mono hint_lhs hmaj fun u => ?_
        rw [hid u]
        have hsup := abs_deriv_phi_le hϱ hw0 hwL u
        have h1 : |2 * deriv (phi ϱ L w) u * deriv (phi ϱ L w) u|
            ≤ 2 * (supDeriv ϱ / w) * |deriv (phi ϱ L w) u| := by
          rw [abs_mul, abs_mul]
          rw [show |(2 : ℝ)| = 2 by norm_num]
          have habs0 : (0 : ℝ) ≤ |deriv (phi ϱ L w) u| := abs_nonneg _
          have := mul_le_mul_of_nonneg_right hsup habs0
          nlinarith
        have h2 : |2 * phi ϱ L w u * deriv (deriv (phi ϱ L w)) u|
            ≤ 2 * |deriv (deriv (phi ϱ L w)) u| := by
          rw [abs_mul, abs_mul]
          rw [show |(2 : ℝ)| = 2 by norm_num]
          have hφ01 : |phi ϱ L w u| ≤ 1 := by
            rw [abs_of_nonneg (phi_nonneg hϱ u)]
            exact phi_le_one hϱ u
          have habs0 : (0 : ℝ) ≤ |deriv (deriv (phi ϱ L w)) u| := abs_nonneg _
          nlinarith
        exact le_trans (abs_add_le _ _) (add_le_add h1 h2)
    _ = 2 * (supDeriv ϱ / w) * (∫ u, |deriv (phi ϱ L w) u|)
        + 2 * ∫ u, |deriv (deriv (phi ϱ L w)) u| := by
        rw [MeasureTheory.integral_add (hint_absphi'.const_mul _) (hint_absphi''.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ = 2 * (supDeriv ϱ / w) * 2 + 2 * (2 * l1Deriv2 ϱ / w) := by
        rw [integral_abs_deriv_phi hϱ hw0 hwL, integral_abs_deriv2_phi hϱ hw0 hwL]
    _ = cRho ϱ / w := by
        rw [cRho_eq]
        field_simp
        ring
