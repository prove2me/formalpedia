-- Prove2me | solution 1 for ReciprocityTheory.Coh.LowDeg.hEquiv_cls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:55:16.762338+00:00
-- url     : https://prove2.me/submissions/b6196ba0-bf3b-471c-9c8a-b8d579667c38

import Definitions.Def_ReciprocityTheory_GroupCohomology_ContinuousContractNth
import Definitions.Def_ReciprocityTheory_GroupCohomology_ComapZeroCoboundariesEqBot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
open ReciprocityTheory.Coh.LowDeg
variable (M : TRep R G)
namespace ReciprocityTheory.Coh.LowDeg
theorem _root_.solution (n : ℕ) (x : M.coch.X n) (hx : M.coch.d n x = 0) :
    hEquiv M n (M.coch.cls n x hx) =
      Submodule.Quotient.mk ⟨x.1, x.2, LinearMap.mem_ker.2 (dn_eq_zero M hx)⟩ := rfl
end ReciprocityTheory.Coh.LowDeg
