-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_tateCohomologyZeroIso_hom_homology__94582ad74da4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:12:41.008802+00:00
-- url     : https://prove2.me/submissions/eec068ca-73e6-4a4c-b59c-3811aaf15e63

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ModuleHomologyData
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Theorems.Thm_P2M_GroundTheory_GroupCoh_homologyFunctorIso__moduleLeftHomologyData_apply_b9da34f1dace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Representation groupCohomology groupHomology
universe u
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (M : Rep.{u} R G) (z : (tateComplex M).cycles 0)
    (x : M.ρ.invariants) (hx : (cochainsIso₀ M).inv.hom x = ((tateComplex M).iCycles 0).hom z) :
    ((tateCohomologyZeroIso R G).app M).hom.hom (((tateComplex M).homologyπ 0).hom z) =
      Submodule.Quotient.mk x :=
  homologyFunctorIso'_moduleLeftHomologyData_apply (tateComplex M) (-1) 0 1 (by simp) (by simp)
    M.ρ.invariants (tateZeroι M) (tateZeroι_injective M) (tateZeroι_range M)
    (normRangeInvariants M) (tateZero_mem_iff M) z x hx
end GroundTheory.GroupCoh
