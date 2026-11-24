-- Prove2me | solution 1 for PaleyWeil.exists_normalized_linear_factors
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T17:30:48.131927+00:00
-- url     : https://prove2.me/submissions/457b4009-8b35-46c3-848b-d851fee109d8

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.ProperSpace

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial

section


/-!
A finite polynomial with constant coefficient one has an exact logarithmic
derivative given by the power sums of its reciprocal roots. A uniform
exponential bound on those power sums bounds each reciprocal root. This is
the sharpness amplification step; it uses no character-sum assumption.
-/

open Polynomial Finset
open scoped PowerSeries

namespace PaleyWeil

noncomputable section

private theorem linear_factor_normalization {r : ℂ} (hr : r ≠ 0) :
    (X - C r : ℂ[X]) = C (-r) * (1 - C r⁻¹ * X) := by
  rw [mul_sub, mul_one, ← mul_assoc, ← C_mul]
  simp only [neg_mul, mul_inv_cancel₀ hr, C_neg, C_1]
  ring


























end
end PaleyWeil

end

/-!
A finite polynomial with constant coefficient one has an exact logarithmic
derivative given by the power sums of its reciprocal roots. A uniform
exponential bound on those power sums bounds each reciprocal root. This is
the sharpness amplification step; it uses no character-sum assumption.
-/
open Polynomial Finset
open scoped PowerSeries
open PaleyWeil

theorem solution (P : ℂ[X]) (h0 : P.coeff 0 = 1) :
    ∃ l : List ℂ, l.length ≤ P.natDegree ∧
      P = (l.map fun w ↦ (1 - C w * X : ℂ[X])).prod := by
  classical
  have hP : P ≠ 0 := by intro h; simp [h] at h0
  have hsplit := IsAlgClosed.splits P
  have hr : ∀ r ∈ P.roots, r ≠ (0 : ℂ) := by
    intro r hr hz
    subst r
    have hz := (mem_roots hP).mp hr
    apply one_ne_zero (α := ℂ)
    simpa only [IsRoot.def, ← coeff_zero_eq_eval_zero, h0] using hz
  have hfac : (P.roots.map fun r ↦ (X - C r : ℂ[X])).prod =
      C ((P.roots.map fun r ↦ -r).prod) *
        (P.roots.map fun r ↦ (1 - C r⁻¹ * X : ℂ[X])).prod := by
    calc
      _ = (P.roots.map fun r ↦ C (-r) * (1 - C r⁻¹ * X : ℂ[X])).prod := by
        congr 1
        exact Multiset.map_congr rfl (fun r hr' ↦ linear_factor_normalization (hr r hr'))
      _ = _ := by
        rw [Multiset.prod_map_mul]
        congr 1
        rw [map_multiset_prod, Multiset.map_map]
        rfl
  have hc : P.leadingCoeff * (P.roots.map fun r ↦ -r).prod = 1 := by
    simpa only [← coeff_zero_eq_eval_zero, h0, zero_sub] using
      (hsplit.eval_eq_prod_roots 0).symm
  refine ⟨P.roots.toList.map Inv.inv, ?_, ?_⟩
  · simpa only [List.length_map, Multiset.length_toList] using P.card_roots'
  · calc
      P = C P.leadingCoeff * (P.roots.map fun r ↦ (X - C r : ℂ[X])).prod :=
        hsplit.eq_prod_roots
      _ = (P.roots.map fun r ↦ (1 - C r⁻¹ * X : ℂ[X])).prod := by
        rw [hfac, ← mul_assoc, ← C_mul, hc, C_1, one_mul]
      _ = _ := by
        conv_lhs => rw [← P.roots.coe_toList]
        simp only [Multiset.map_coe, Multiset.prod_coe, List.map_map, Function.comp_def]
