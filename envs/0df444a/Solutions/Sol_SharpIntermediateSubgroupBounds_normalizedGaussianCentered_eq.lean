-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.normalizedGaussianCentered_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:03:57.378031+00:00
-- url     : https://prove2.me/submissions/68cb1467-d02e-4ba2-88d0-b889428909f1

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_normalizedGaussianRight_eq

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p a : ℕ} {j : ℤ} (hp : 2 ≤ p)
    (hj : j.natAbs ≤ a) :
    normalizedGaussianCentered p a j =
      (p : ℝ)⁻¹ ^ (j.natAbs * j.natAbs) * gammaR (p : ℝ) (2 * a) *
        (gammaR (p : ℝ) (a + j.natAbs))⁻¹ *
          (gammaR (p : ℝ) (a - j.natAbs))⁻¹ := by
  exact normalizedGaussianRight_eq hp hj
end SharpIntermediateSubgroupBounds
