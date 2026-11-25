-- Prove2me | solution 1 for SZ.digitSum_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:01:26.442829+00:00
-- url     : https://prove2.me/submissions/d7649a13-fdb0-4ca6-9cea-3408e82a3909

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {m : ℕ} {d d' : ℕ → ℤ} {k : ℕ} (h : ∀ j, j < k → d j = d' j) :
    digitSum m d k = digitSum m d' k := by
  unfold digitSum
  exact Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.mp hj)]
end SZ
