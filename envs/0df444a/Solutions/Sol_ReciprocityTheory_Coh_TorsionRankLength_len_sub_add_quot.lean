-- Prove2me | solution 1 for ReciprocityTheory.Coh.TorsionRankLength.len_sub_add_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:33.244407+00:00
-- url     : https://prove2.me/submissions/b00b6822-672c-4425-8307-eaa666fe85b9

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
theorem _root_.solution (N : Submodule R M) :
    Module.length R M = Module.length R N + Module.length R (M ⧸ N) :=
  Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
    (LinearMap.exact_subtype_mkQ N)
end ReciprocityTheory.Coh.TorsionRankLength
