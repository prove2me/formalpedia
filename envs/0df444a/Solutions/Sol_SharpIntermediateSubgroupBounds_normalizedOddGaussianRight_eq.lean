-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.normalizedOddGaussianRight_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:55:44.629706+00:00
-- url     : https://prove2.me/submissions/9d813740-9c49-48a0-a964-a9a09aa33ef4

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
    normalizedOddGaussianRight p a j =
      (p : ℝ)⁻¹ ^ (j * (j + 1)) * gammaR (p : ℝ) (2 * a + 1) *
        (gammaR (p : ℝ) (a + 1 + j))⁻¹ *
          (gammaR (p : ℝ) (a - j))⁻¹ := by
  rw [normalizedOddGaussianRight, if_pos hj,
    qBinom_cast_real_eq_gammaR hp (by omega : a + 1 + j ≤ 2 * a + 1)]
  have hsub : 2 * a + 1 - (a + 1 + j) = a - j := by omega
  rw [hsub]
  have hexp : a * (a + 1) = j * (j + 1) + (a + 1 + j) * (a - j) := by
    have := Nat.sub_add_cancel hj
    nlinarith
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hscale : (p : ℝ)⁻¹ ^ (a * (a + 1)) *
      (p : ℝ) ^ ((a + 1 + j) * (a - j)) =
        (p : ℝ)⁻¹ ^ (j * (j + 1)) := by
    rw [hexp, pow_add]
    simp [inv_pow, hp0]
  rw [div_eq_mul_inv, mul_inv]
  calc
    (p : ℝ)⁻¹ ^ (a * (a + 1)) *
          ((p : ℝ) ^ ((a + 1 + j) * (a - j)) *
            gammaR (p : ℝ) (2 * a + 1) *
              ((gammaR (p : ℝ) (a + 1 + j))⁻¹ *
                (gammaR (p : ℝ) (a - j))⁻¹)) =
        ((p : ℝ)⁻¹ ^ (a * (a + 1)) *
          (p : ℝ) ^ ((a + 1 + j) * (a - j))) *
            gammaR (p : ℝ) (2 * a + 1) *
              (gammaR (p : ℝ) (a + 1 + j))⁻¹ *
                (gammaR (p : ℝ) (a - j))⁻¹ := by ring
    _ = (p : ℝ)⁻¹ ^ (j * (j + 1)) * gammaR (p : ℝ) (2 * a + 1) *
        (gammaR (p : ℝ) (a + 1 + j))⁻¹ *
          (gammaR (p : ℝ) (a - j))⁻¹ := by rw [hscale]
end SharpIntermediateSubgroupBounds
