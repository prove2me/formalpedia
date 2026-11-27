-- Prove2me | solution 1 for ReciprocityTheory.Coh.Cx.d_eq_zero_of_mem_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:27:55.162482+00:00
-- url     : https://prove2.me/submissions/68185a6d-55be-49b4-9319-dd159f0a1fb3

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
universe u
open ReciprocityTheory.Coh.Cx
variable {R : Type u} [CommRing R] {A B C : Cx R}
namespace ReciprocityTheory.Coh.Cx
theorem _root_.solution {n : ℕ} {x : A.X n} (h : x ∈ A.B n) : A.d n x = 0 := by
  cases n with
  | zero =>
    change x ∈ (⊥ : Submodule R (A.X 0)) at h
    rw [(Submodule.mem_bot R).1 h, map_zero]
  | succ n =>
    change x ∈ LinearMap.range (A.d n) at h
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 h
    exact A.dd n y
end ReciprocityTheory.Coh.Cx
