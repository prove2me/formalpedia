-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.normalizedGaussianRight_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:55:44.138371+00:00
-- url     : https://prove2.me/submissions/6386da09-460c-460e-a290-ee5ef54a94f7

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_qBinom_cast_real_eq_gammaR

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p a j : ℕ} (hp : 2 ≤ p) (hj : j ≤ a) :
    normalizedGaussianRight p a j =
      (p : ℝ)⁻¹ ^ (j * j) * gammaR (p : ℝ) (2 * a) *
        (gammaR (p : ℝ) (a + j))⁻¹ * (gammaR (p : ℝ) (a - j))⁻¹ := by
  rw [normalizedGaussianRight, if_pos hj,
    qBinom_cast_real_eq_gammaR hp (by omega : a + j ≤ 2 * a)]
  have hsub : 2 * a - (a + j) = a - j := by omega
  rw [hsub]
  have hexp : a * a = j * j + (a + j) * (a - j) := by
    have := Nat.sub_add_cancel hj
    nlinarith
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hscale : (p : ℝ)⁻¹ ^ (a * a) *
      (p : ℝ) ^ ((a + j) * (a - j)) = (p : ℝ)⁻¹ ^ (j * j) := by
    rw [hexp, pow_add]
    simp [inv_pow, hp0]
  rw [div_eq_mul_inv, mul_inv]
  calc
    (p : ℝ)⁻¹ ^ (a * a) *
          ((p : ℝ) ^ ((a + j) * (a - j)) * gammaR (p : ℝ) (2 * a) *
            ((gammaR (p : ℝ) (a + j))⁻¹ *
              (gammaR (p : ℝ) (a - j))⁻¹)) =
        ((p : ℝ)⁻¹ ^ (a * a) *
          (p : ℝ) ^ ((a + j) * (a - j))) * gammaR (p : ℝ) (2 * a) *
            (gammaR (p : ℝ) (a + j))⁻¹ *
              (gammaR (p : ℝ) (a - j))⁻¹ := by ring
    _ = (p : ℝ)⁻¹ ^ (j * j) * gammaR (p : ℝ) (2 * a) *
        (gammaR (p : ℝ) (a + j))⁻¹ *
          (gammaR (p : ℝ) (a - j))⁻¹ := by rw [hscale]
end SharpIntermediateSubgroupBounds
