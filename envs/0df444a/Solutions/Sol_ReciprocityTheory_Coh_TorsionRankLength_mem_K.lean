-- Prove2me | solution 1 for ReciprocityTheory.Coh.TorsionRankLength.mem_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:48:37.409181+00:00
-- url     : https://prove2.me/submissions/a2c1d458-0b31-4af0-b4a0-6d7a8a1d83f9

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
theorem _root_.solution {r : R} {x : M} : x ∈ K M r ↔ r • x = 0 := by
  simp [K]
end ReciprocityTheory.Coh.TorsionRankLength
