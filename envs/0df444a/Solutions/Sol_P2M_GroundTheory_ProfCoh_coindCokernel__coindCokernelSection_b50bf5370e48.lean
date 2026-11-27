-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_coindCokernel__coindCokernelSection_b50bf5370e48
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:13:05.627192+00:00
-- url     : https://prove2.me/submissions/81ad8eff-8e41-4551-b2b4-f69b4315cb48

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules
import Theorems.Thm_GroundTheory_ProfCoh_mem_coindEmbeddingRange
import Theorems.Thm_GroundTheory_ProfCoh_coindCokernelSection_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory Filter Topology
universe u
variable (k G : Type u) [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Type u) [AddCommGroup X] [Module k X]
variable {k G}
namespace GroundTheory.ProfCoh
theorem _root_.solution (A : Rep.{u} k G) [IsDiscreteRep A]
    (c : LocallyConstant G A ⧸ coindEmbeddingRange A) :
    (coindCokernelπ A).hom (coindCokernelSection A c) = c := by
  induction c using Submodule.Quotient.induction_on with
  | H f =>
    rw [coindCokernelSection_mk]
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.mk_sub,
      (Submodule.Quotient.mk_eq_zero _).2
        ((mem_coindEmbeddingRange A _).2 ⟨coindEval k G A f, rfl⟩), sub_zero]
end GroundTheory.ProfCoh
