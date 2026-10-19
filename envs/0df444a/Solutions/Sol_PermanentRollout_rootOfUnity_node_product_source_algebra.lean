-- Prove2me | solution 1 for PermanentRollout.rootOfUnity_node_product_source_algebra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/d8646a7a-581f-4d38-b065-7a627a0f9b26

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_rootOfUnity_node_product_algebra

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {R : Type*} [CommRing R] [Algebra ℂ R]
    {d : ℕ} (hd : 0 < d) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ d) (x y : R) :
    (∏ j ∈ Finset.range d,
      (x + algebraMap ℂ R (2 * ζ ^ j) * y)) =
      x ^ d +
        algebraMap ℂ R (((-1 : ℂ) ^ (d + 1)) * (2 : ℂ) ^ d) * y ^ d := by
  rw [rootOfUnity_node_product_algebra hd hζ x y]
  have hneg : algebraMap ℂ R (-2) = -(algebraMap ℂ R 2) := by
    norm_num
  rw [hneg, neg_mul, neg_pow, mul_pow,
    map_mul, map_pow, map_pow, pow_succ]
  norm_num
  ring
end PermanentRollout
