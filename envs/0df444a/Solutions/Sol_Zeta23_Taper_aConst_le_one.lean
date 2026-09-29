-- Prove2me | solution 1 for Zeta23.Taper.aConst_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T02:28:27.789903+00:00
-- url     : https://prove2.me/submissions/4d289e5f-4fd0-4dda-a0f7-304adf2da1ed

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






/-! ### The taper φ [eq:phidef], a, b [eq:abdef], Φ, g, A_φ [eq:PhigA], ψ [eq:psidef] -/

variable (ϱ : ℝ → ℝ) (L w : ℝ)











/-! ### Basic properties of φ (the sentence after [eq:phidef]):
"`φ ∈ C_c³(ℝ)` is even, `0 ≤ φ ≤ 1`, `supp φ = [−L/2, L/2]`, `φ = 1` on `[−L/2+w, L/2−w]`" -/

section Basic
variable {ϱ L w}


theorem phi_nonneg (hϱ : TaperProfile ϱ) (u : ℝ) : 0 ≤ phi ϱ L w u := hϱ.nonneg _

theorem phi_le_one (hϱ : TaperProfile ϱ) (u : ℝ) : phi ϱ L w u ≤ 1 := hϱ.le_one _

/-- `φ(u) = 0` for `|u| ≥ L/2`. -/
theorem phi_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : L / 2 ≤ |u|) :
    phi ϱ L w u = 0 := by
  unfold phi
  apply hϱ.eq_zero
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith



theorem phi_hasCompactSupport (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    HasCompactSupport (phi ϱ L w) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (phi_support_subset hϱ hw)



theorem phi_continuous (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (phi ϱ L w) :=
  (phi_contDiff hϱ hw hwL).continuous


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






























end Norms

/-! ### [eq:abdef]: "`1 − 2w/L ≤ b ≤ a ≤ 1`" -/

section AB
variable {ϱ : ℝ → ℝ} {L w : ℝ}

lemma L_pos (hw : 0 < w) (hwL : 2 * w ≤ L) : (0 : ℝ) < L := by linarith

lemma integrable_phi_pow (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    {n : ℕ} (hn : 0 < n) :
    Integrable (fun u => phi ϱ L w u ^ n) :=
  ((phi_continuous hϱ hw hwL).pow n).integrable_of_hasCompactSupport
    ((phi_hasCompactSupport hϱ hw).comp_left (g := (· ^ n)) (by simp [zero_pow hn.ne']))





end AB


end Taper

end Zeta23
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
open Zeta23
open Taper
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem solution (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    aConst ϱ L w ≤ 1 := by
  have hL := L_pos hw hwL
  unfold aConst
  have hsupp : ∀ u ∉ Icc (-(L / 2)) (L / 2), phi ϱ L w u ^ 2 = 0 := by
    intro u hu
    have : phi ϱ L w u = 0 := by
      apply phi_eq_zero hϱ hw
      rw [mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with h | h
      · calc L / 2 ≤ -u := by linarith
          _ ≤ |u| := neg_le_abs u
      · calc L / 2 ≤ u := by linarith
          _ ≤ |u| := le_abs_self u
    rw [this]
    ring
  have heq : ∫ u : ℝ, phi ϱ L w u ^ 2 = ∫ u in Icc (-(L / 2)) (L / 2), phi ϱ L w u ^ 2 :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
  have hle : ∫ u in Icc (-(L / 2)) (L / 2), phi ϱ L w u ^ 2
      ≤ ∫ u in Icc (-(L / 2)) (L / 2), (1 : ℝ) := by
    refine MeasureTheory.setIntegral_mono_on
      ((integrable_phi_pow hϱ hw hwL (by norm_num)).integrableOn)
      (MeasureTheory.integrableOn_const (by simp)) measurableSet_Icc fun u _ => ?_
    have h0 := phi_nonneg hϱ (L := L) (w := w) u
    have h1 := phi_le_one hϱ (L := L) (w := w) u
    nlinarith
  have hvol : ∫ u in Icc (-(L / 2)) (L / 2), (1 : ℝ) = L := by
    rw [MeasureTheory.setIntegral_const]
    rw [MeasureTheory.measureReal_def, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by linarith)]
    rw [smul_eq_mul, mul_one]
    ring
  calc L⁻¹ * ∫ u : ℝ, phi ϱ L w u ^ 2 ≤ L⁻¹ * L := by
        rw [heq]
        exact mul_le_mul_of_nonneg_left (le_trans hle (le_of_eq hvol)) (by positivity)
    _ = 1 := inv_mul_cancel₀ hL.ne'
