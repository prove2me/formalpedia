-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationRestrictionInvariants.mem_oneCoboundaries_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:59.830431+00:00
-- url     : https://prove2.me/submissions/ce2acb95-1de3-4304-b70b-f4fc87eb0381

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InnerHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_oneCochain_apply_fin_one
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_memB
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_zeroDifferential_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants
open ReciprocityTheory.Gal Cx Function
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.InflationRestrictionInvariants
theorem _root_.solution (M : TRep R G) (x : M.coch.X 1) :
    x ∈ M.coch.B 1 ↔ ∃ m, ∀ a, x.1 (e1 a) = M.rho a m - m := by
  rw [memB]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1 ![], fun a => zeroDifferential_val M y a⟩
  · rintro ⟨m, hm⟩
    refine ⟨const0 M m, Subtype.ext (funext fun g => ?_)⟩
    rw [oneCochain_apply_fin_one M x g, hm, oneCochain_apply_fin_one M (M.coch.d 0 (const0 M m)) g, zeroDifferential_val]
    rfl
end ReciprocityTheory.Coh.InflationRestrictionInvariants
