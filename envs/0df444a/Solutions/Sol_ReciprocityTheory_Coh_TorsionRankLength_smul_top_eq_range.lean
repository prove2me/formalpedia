-- Prove2me | solution 1 for ReciprocityTheory.Coh.TorsionRankLength.smul_top_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:48:41.752184+00:00
-- url     : https://prove2.me/submissions/458bebfd-3df7-4ebe-81c5-31e824f4c24d

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_RankLenA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.TorsionRankLength
universe u
open Module Submodule Function
open scoped Pointwise TensorProduct
variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
namespace ReciprocityTheory.Coh.TorsionRankLength
theorem _root_.solution (r : R) :
    (r • ⊤ : Submodule R M) = LinearMap.range (r • LinearMap.id : M →ₗ[R] M) := by
  ext x
  rw [Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_range]
  simp
end ReciprocityTheory.Coh.TorsionRankLength
