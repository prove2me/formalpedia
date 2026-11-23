-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.nu_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:03.959102+00:00
-- url     : https://prove2.me/submissions/745de796-adb4-4832-8e8b-3850d79c15cc

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsBoundedBasis
import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (b : Fin d → E) (c w : Fin d → ℝ) (N : ℝ) (j : Fin d) :
    nu b (fun l => c l - N * w l) j = nu b c j - N * nu b w j := by
  simp only [nu, sub_mul, Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]
end ReciprocityTheory.ReducedBases.T2
