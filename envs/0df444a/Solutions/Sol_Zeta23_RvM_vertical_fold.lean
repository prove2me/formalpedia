-- Prove2me | solution 1 for Zeta23.RvM.vertical_fold
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:32:03.456585+00:00
-- url     : https://prove2.me/submissions/9ad90a9b-bf04-427b-9468-4715712ece76

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Definitions.Def_Zeta23_Analytic_RectangleLogDeriv
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_RvM_Defs
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect
import Definitions.Def_Extra_Zeta23_Analytic_RectangleLogDeriv
import Theorems.Thm_Zeta23_WeilEF_differentiableAt_GammaR
import Theorems.Thm_Zeta23_WeilEF_logDeriv_completedZeta_one_sub
import Theorems.Thm_Zeta23_conj_riemannZeta_conj

-- from Zeta23.FromPNTPlus.ZetaConj
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ZetaConj.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open scoped Complex ComplexConjugate

theorem deriv_conj_conj' (f : ℂ → ℂ) (p : ℂ) :
    deriv (fun z ↦ conj (f (conj z))) (conj p) = conj (deriv f p) := by
  trans deriv (conj ∘ f ∘ conj) (conj p)
  · rfl
  simp

/- v4.30 port: Mathlib c5ea003 predates `riemannZeta_conj`, so we restore the local proof
from the v4.30-era PrimeNumberTheoremAnd/ZetaConj.lean (commit f55e855). -/


-- `riemannZeta_conj` is now provided by Mathlib.

theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  simp [← deriv_conj_conj', Zeta23_conj_riemannZeta_conj]

theorem logDerivZeta_conj (s : ℂ) :
    (deriv riemannZeta / riemannZeta) (conj s) = conj ((deriv riemannZeta / riemannZeta) s) := by
  simp [deriv_riemannZeta_conj, riemannZeta_conj]

theorem logDerivZeta_conj' (s : ℂ) :
    (logDeriv riemannZeta) (conj s) = conj (logDeriv riemannZeta s) := logDerivZeta_conj s

set_option backward.isDefEq.respectTransparency false in
theorem intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    ∫ (x : ℝ) in a..b, conj (f x) = conj (∫ (x : ℝ) in a..b, f x) := by
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_conj, ← RCLike.conj_smul,
    ← intervalIntegral.intervalIntegral_eq_integral_uIoc]
end

-- from Zeta23.WeilEF.XiLogDeriv
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/XiLogDeriv.lean
The completed zeta function Λ = completedRiemannZeta: log-derivative decomposition, functional equation
for logDeriv, zeros in the strip = nontrivial zeros of ζ with equal analytic order.

Mathlib normalization (verified): for s ≠ 0, riemannZeta s = completedRiemannZeta s / Gammaℝ s
(riemannZeta_def_of_ne_zero) and Gammaℝ s ≠ 0 for 0 < Re s (Gammaℝ_ne_zero_of_re_pos); hence on the
open right half-plane Λ = Γℝ · ζ on the nose (completedZeta_eventuallyEq_mul) — no pole bookkeeping is
needed for the three statements below (Λ's poles at 0, 1 are excluded by hypothesis).
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Filter Topology



/-- On the right half-plane, Λ = Γℝ · ζ (as germs). -/
lemma completedZeta_eventuallyEq_mul {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta =ᶠ[𝓝 s] fun u => Gammaℝ u * riemannZeta u := by
  have hopen : IsOpen {u : ℂ | 0 < u.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with u hu
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hu
  have hΓ := Gammaℝ_ne_zero_of_re_pos hu
  rw [riemannZeta_def_of_ne_zero hu0]
  field_simp


/-- On the right half-plane away from 1 and from the zeros of ζ:  Λ'/Λ = Γℝ'/Γℝ + ζ'/ζ. -/
theorem logDeriv_completedZeta (s : ℂ) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) (hstrip : 0 < s.re) :
    logDeriv completedRiemannZeta s = logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s := by
  have hev := completedZeta_eventuallyEq_mul hstrip
  have heq : logDeriv completedRiemannZeta s = logDeriv (fun u => Gammaℝ u * riemannZeta u) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [heq]
  exact logDeriv_mul s (Gammaℝ_ne_zero_of_re_pos hstrip) hζ (differentiableAt_GammaR hstrip)
    (differentiableAt_riemannZeta hs1)



end WeilEF
end Zeta23
end
end

-- from Zeta23.RvM.Fold
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/Fold.lean — the symmetry fold of the argument-principle rectangle onto its right half
(used for MainTerm.lean's N_eq_halfContour_completedZeta).

With F := Λ'/Λ (Λ = completedRiemannZeta), A_T := ∫_{1/2}^{2} F(σ+iT)dσ, B := ∫_{T₁}^{T₂} F(2+it)dt:
the functional equation Λ(1−w) = Λ(w) and the reflection Λ(w̄) = conj Λ(w) give F(1−s̄) = −conj F(s)
on the right half-path, hence ∫_{−1}^{1/2}F(σ+iT)dσ = −conj A_T, ∫_{T₁}^{T₂}F(−1+it)dt = −conj B, and
    ∮_{∂([−1,2]×[T₁,T₂])} F = (A_{T₁} − conj A_{T₁}) − (A_{T₂} − conj A_{T₂}) + I(B + conj B)
                           = 2i·Im(A_{T₁} + B·i − A_{T₂}) = 2i·Im(halfContour F T₁ T₂).
Combined with Zeta23.RvM.rectangleIntegral'_logDeriv_completedZeta_eq_Ncount (CountByIntegral.lean):
    N(T₁,T₂) = (1/π)·Im(halfContour (logDeriv Λ) T₁ T₂)   for good heights 1 ≤ T₁ < T₂.
The conj-symmetry lemmas for Gammaℝ and Λ'/Λ (section ConjSymmetry) live here rather than in
MainTerm.lean so that both files can use them.
-/

open Complex MeasureTheory Set intervalIntegral

noncomputable section

namespace Zeta23.RvM

section ConjSymmetry

/-- (x : ℂ)^(conj w) = conj ((x : ℂ)^w) for real x > 0. -/
lemma cpow_ofReal_conj {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (x : ℂ) ^ (starRingEnd ℂ w) = starRingEnd ℂ ((x : ℂ) ^ w) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [cpow_def_of_ne_zero hx0, cpow_def_of_ne_zero hx0, ← Complex.exp_conj, map_mul,
    ← Complex.ofReal_log hx.le, Complex.conj_ofReal]

/-- Γℝ(s̄) = conj Γℝ(s). -/
lemma Gammaℝ_conj (s : ℂ) : Complex.Gammaℝ (starRingEnd ℂ s) = starRingEnd ℂ (Complex.Gammaℝ s) := by
  have h1 : -(starRingEnd ℂ s) / 2 = starRingEnd ℂ (-s / 2) := by
    simp [map_div₀, map_neg, map_ofNat]
  have h2 : starRingEnd ℂ s / 2 = starRingEnd ℂ (s / 2) := by
    simp [map_div₀, map_ofNat]
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, h1, h2, cpow_ofReal_conj Real.pi_pos,
    Complex.Gamma_conj, map_mul]

lemma deriv_Gammaℝ_conj (s : ℂ) :
    deriv Complex.Gammaℝ (starRingEnd ℂ s) = starRingEnd ℂ (deriv Complex.Gammaℝ s) := by
  have h : ∀ z : ℂ, starRingEnd ℂ (Complex.Gammaℝ (starRingEnd ℂ z)) = Complex.Gammaℝ z := by
    intro z
    rw [Gammaℝ_conj, Complex.conj_conj]
  simp [← deriv_conj_conj' Complex.Gammaℝ, h]

lemma logDeriv_Gammaℝ_conj (s : ℂ) :
    logDeriv Complex.Gammaℝ (starRingEnd ℂ s) = starRingEnd ℂ (logDeriv Complex.Gammaℝ s) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_Gammaℝ_conj, Gammaℝ_conj, ← map_div₀]

/-- Conjugation symmetry of Λ'/Λ at points with Re > 0 where ζ ≠ 0. -/
lemma logDeriv_completedZeta_conj {s : ℂ} (hre : 0 < s.re) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hζs : riemannZeta s ≠ 0) :
    logDeriv completedRiemannZeta (starRingEnd ℂ s)
      = starRingEnd ℂ (logDeriv completedRiemannZeta s) := by
  have hcre : 0 < (starRingEnd ℂ s).re := by rwa [Complex.conj_re]
  have hc0 : starRingEnd ℂ s ≠ 0 := (map_ne_zero _).mpr hs0
  have hc1 : starRingEnd ℂ s ≠ 1 := fun h => hs1 (by rw [← Complex.conj_conj s, h, map_one])
  have hζc : riemannZeta (starRingEnd ℂ s) ≠ 0 := by
    rw [_root_.riemannZeta_conj]
    exact (map_ne_zero _).mpr hζs
  rw [Zeta23.WeilEF.logDeriv_completedZeta _ hc1 hζc hcre,
    Zeta23.WeilEF.logDeriv_completedZeta _ hs1 hζs hre, map_add, logDeriv_Gammaℝ_conj,
    logDerivZeta_conj']

/-- The fold symmetry: Λ'/Λ(1 − s̄) = −conj(Λ'/Λ(s)) (Re s > 0, s ≠ 1, ζ(s) ≠ 0). -/
lemma logDeriv_completedZeta_one_sub_conj {s : ℂ} (hre : 0 < s.re) (hs1 : s ≠ 1)
    (hζs : riemannZeta s ≠ 0) :
    logDeriv completedRiemannZeta (1 - starRingEnd ℂ s)
      = -starRingEnd ℂ (logDeriv completedRiemannZeta s) := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hre
  have hc0 : starRingEnd ℂ s ≠ 0 := (map_ne_zero _).mpr hs0
  have hc1 : starRingEnd ℂ s ≠ 1 := fun h => hs1 (by rw [← Complex.conj_conj s, h, map_one])
  rw [Zeta23.WeilEF.logDeriv_completedZeta_one_sub _ hc0 hc1,
    logDeriv_completedZeta_conj hre hs0 hs1 hζs]

end ConjSymmetry







end Zeta23.RvM
end
open Complex MeasureTheory Set intervalIntegral
open Zeta23
open Zeta23.RvM

theorem solution {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (h12 : T₁ ≤ T₂) :
    ∫ t in T₁..T₂, logDeriv completedRiemannZeta (-1 + t * I)
      = -starRingEnd ℂ (∫ t in T₁..T₂, logDeriv completedRiemannZeta (2 + t * I)) := by
  rw [← intervalIntegral_conj, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le h12] at ht
  have ht1 : 1 ≤ t := le_trans h1 ht.1
  have hs1 : (2 : ℂ) + t * I ≠ 1 := by
    intro hh; have := congrArg Complex.re hh; simp at this
  have hζ : riemannZeta (2 + t * I) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
  have key := logDeriv_completedZeta_one_sub_conj (s := 2 + t * I) (by simp) hs1 hζ
  have e : (1 : ℂ) - starRingEnd ℂ (2 + t * I) = -1 + t * I := by
    simp [Complex.ext_iff]; norm_num
  show logDeriv completedRiemannZeta (-1 + t * I)
    = -starRingEnd ℂ (logDeriv completedRiemannZeta (2 + t * I))
  rw [← e, key]
