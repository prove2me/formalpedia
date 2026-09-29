-- Prove2me | solution 1 for Zeta23.Taper.integral_phi_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T02:27:43.799939+00:00
-- url     : https://prove2.me/submissions/9282ce16-5377-49af-9439-970f377d7624

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Star.Basic
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
import Mathlib.MeasureTheory.Integral.Bochner.Set
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



theorem phi_le_one (hϱ : TaperProfile ϱ) (u : ℝ) : phi ϱ L w u ≤ 1 := hϱ.le_one _




theorem phi_hasCompactSupport (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    HasCompactSupport (phi ϱ L w) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (phi_support_subset hϱ hw)



theorem phi_continuous (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (phi ϱ L w) :=
  (phi_contDiff hϱ hw hwL).continuous

theorem phi_integrable (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Integrable (phi ϱ L w) :=
  (phi_continuous hϱ hw hwL).integrable_of_hasCompactSupport (phi_hasCompactSupport hϱ hw)

end Basic



end Taper

end Zeta23
end

-- from Zeta23.Taper.Strip
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Strip.lean.
[eq:hfbound] specialized to `f = φ`, `Λ_f = L/2` (as consumed by [prop:tail]):
"`|φ̂(r − iy)| ≤ e^{L/4} ‖φ''‖₁ |r − iy|⁻²`" for `|y| ≤ 1/2`.
All three statements are proved here from the general-`f` bounds in Zeta23/Poisson/PaperFT.lean,
and are consumed via `Zeta23.Params.norm_phiHat_*`.
Reference: the paper, §2.1 [eq:hfbound], §4 [prop:tail].
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

namespace Taper

section HfPhi
variable {ϱ : ℝ → ℝ} {L w : ℝ}









end HfPhi

end Taper

end Zeta23
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
open Zeta23
open Taper
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem solution (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, phi ϱ L w u ≤ L := by
  have hL : 0 ≤ L := by linarith
  have hle : ∀ u, phi ϱ L w u ≤ (Icc (-(L / 2)) (L / 2)).indicator (fun _ => (1 : ℝ)) u := by
    intro u
    by_cases hu : u ∈ Icc (-(L / 2)) (L / 2)
    · rw [indicator_of_mem hu]; exact phi_le_one hϱ u
    · rw [indicator_of_notMem hu]
      have : u ∉ Function.support (phi ϱ L w) := fun h => hu (phi_support_subset hϱ hw h)
      rw [Function.notMem_support] at this
      rw [this]
  calc ∫ u, phi ϱ L w u ≤ ∫ u, (Icc (-(L / 2)) (L / 2)).indicator (fun _ => (1 : ℝ)) u := by
        apply integral_mono (phi_integrable hϱ hw hwL) _ hle
        exact (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
    _ = L := by
        rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_one]
        ring
