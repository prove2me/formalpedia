-- Prove2me | solution 1 for Zeta23.PrimeSide.mumu_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T03:13:48.464096+00:00
-- url     : https://prove2.me/submissions/716970ec-7887-4afc-abd3-7f5d048644f3

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
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
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideB_PPKernel
import Theorems.Thm_Zeta23_PrimeSide_abs_inner_sub_le
import Theorems.Thm_Zeta23_PrimeSide_integrable_sq_mul_inner
import Theorems.Thm_Zeta23_PrimeSide_sqIntegral_shear

-- from Zeta23.PrimeSideA.MuMu
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/PrimeSideA/MuMu.lean

[prop:mumu] (paper §5.4): 𝓜[μ,μ] = 2πbL ∫_T^{2T} μ² + O(l² log L).

Paper proof, as implemented here:
  * shear τ = τ' + x (`sqIntegral_shear`):
      𝓜[μ,μ] = ∫_ℝ Φ(x)² (∫_{I∩(I−x)} μ(x+τ')μ(τ') dτ') dx;
  * Lipschitz step "μ(τ)=μ(τ')+O(|τ−τ'|/T)" (via `mu_increment_bound`'s (K|r|+10r²)/t):
      |∫_{Ix}(μ(x+τ')−μ(τ'))μ(τ')| ≤ l(K|x| + 10x²)   (window length ≤ T, τ' ≥ T);
  * completing ∫_{Ix} to ∫_I ("∫_{I−τ'}Φ² = 2πbL − tails"):
      |∫_{I∖Ix} μ²| ≤ l²·|x|   (vol(I∖Ix) = min(|x|,T));
  * ∫Φ²|x| ≤ 8 + 8log(cϱL/4w) ≪ log L  [eq:psiints]  and  ∫Φ²x² ≤ 8 + 2(cϱ/w)² = O(1).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Real Set
open scoped BigOperators

namespace Zeta23
namespace PrimeSide

variable {cϱ : ℝ}

section Core

variable {p : Setting} {F : LocalFun}



end Core

/-! ## [prop:mumu] -/

variable (cϱ lam : ℝ)


end PrimeSide
end Zeta23
end
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open scoped BigOperators
open Zeta23
open PrimeSide
variable {cϱ : ℝ}
variable {p : Setting} {F : LocalFun}

theorem solution (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p F) (hT2 : 2 ≤ p.T)
    (hμl : ∀ τ ∈ Icc p.T (2 * p.T), |Zeta23.mu τ| ≤ p.l)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hKinc : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ,
      |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (K * |r| + 10 * r ^ 2) / t) :
    |Mform F.Phi p.T Zeta23.mu Zeta23.mu
        - 2 * π * F.b * p.L * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ ^ 2|
      ≤ (1 + K) * p.l ^ 2 * (∫ x, F.Phi x ^ 2 * |x|)
        + 10 * p.l * ∫ x, F.Phi x ^ 2 * x ^ 2 := by
  have hμc : Continuous Zeta23.mu := hΓ.smooth.continuous
  have hΦc : Continuous F.Phi := hF.Phi_contDiff.continuous
  have hGc : Continuous fun q : ℝ × ℝ => Zeta23.mu q.1 * Zeta23.mu q.2 := by fun_prop
  set c : ℝ := ∫ τ' in Icc p.T (2 * p.T), Zeta23.mu τ' ^ 2 with hc
  have hc' : ∫ τ in p.T..(2 * p.T), Zeta23.mu τ ^ 2 = c := by
    rw [intervalIntegral.integral_of_le (by linarith), hc, integral_Icc_eq_integral_Ioc]
  have hshear : Mform F.Phi p.T Zeta23.mu Zeta23.mu
      = ∫ x, F.Phi x ^ 2 * ∫ τ' in Ix p.T x, Zeta23.mu (x + τ') * Zeta23.mu τ' := by
    unfold Mform
    simp only [mul_assoc]
    exact sqIntegral_shear hΦc hGc
  have hfInt : Integrable (fun x => F.Phi x ^ 2 * ∫ τ' in Ix p.T x,
      Zeta23.mu (x + τ') * Zeta23.mu τ') := integrable_sq_mul_inner hΦc hGc
  have hgInt : Integrable (fun x => F.Phi x ^ 2 * c) := hF.Phi_sq_integrable.mul_const c
  have hmain : 2 * π * F.b * p.L * c = ∫ x, F.Phi x ^ 2 * c := by
    rw [integral_mul_const c (fun x => F.Phi x ^ 2), hF.Phi_sq_integral]
  rw [hc', hshear, hmain, ← integral_sub hfInt hgInt]
  have hpt : ∀ x : ℝ, |F.Phi x ^ 2 * (∫ τ' in Ix p.T x, Zeta23.mu (x + τ') * Zeta23.mu τ')
      - F.Phi x ^ 2 * c|
      ≤ (1 + K) * p.l ^ 2 * (F.Phi x ^ 2 * |x|) + 10 * p.l * (F.Phi x ^ 2 * x ^ 2) := by
    intro x
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg (F.Phi x))]
    have hinner := abs_inner_sub_le hΓ hF hT2 hμl hK0 hKinc x
    rw [← hc] at hinner
    calc F.Phi x ^ 2 * |(∫ τ' in Ix p.T x, Zeta23.mu (x + τ') * Zeta23.mu τ') - c|
        ≤ F.Phi x ^ 2 * ((1 + K) * p.l ^ 2 * |x| + 10 * p.l * x ^ 2) := by
          gcongr
      _ = (1 + K) * p.l ^ 2 * (F.Phi x ^ 2 * |x|) + 10 * p.l * (F.Phi x ^ 2 * x ^ 2) := by ring
  calc |∫ x, (F.Phi x ^ 2 * (∫ τ' in Ix p.T x, Zeta23.mu (x + τ') * Zeta23.mu τ')
        - F.Phi x ^ 2 * c)|
      ≤ ∫ x, |F.Phi x ^ 2 * (∫ τ' in Ix p.T x, Zeta23.mu (x + τ') * Zeta23.mu τ')
        - F.Phi x ^ 2 * c| := by
        rw [← Real.norm_eq_abs]
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        simp_rw [Real.norm_eq_abs]
    _ ≤ ∫ x, ((1 + K) * p.l ^ 2 * (F.Phi x ^ 2 * |x|) + 10 * p.l * (F.Phi x ^ 2 * x ^ 2)) :=
        integral_mono (hfInt.sub hgInt).abs
          ((hF.Phi_sq_mul_abs_integrable.const_mul _).add
            (hF.Phi_sq_mul_sq_integrable.const_mul _)) hpt
    _ = (1 + K) * p.l ^ 2 * (∫ x, F.Phi x ^ 2 * |x|)
        + 10 * p.l * ∫ x, F.Phi x ^ 2 * x ^ 2 := by
        rw [integral_add (hF.Phi_sq_mul_abs_integrable.const_mul _)
          (hF.Phi_sq_mul_sq_integrable.const_mul _),
          integral_const_mul, integral_const_mul]
