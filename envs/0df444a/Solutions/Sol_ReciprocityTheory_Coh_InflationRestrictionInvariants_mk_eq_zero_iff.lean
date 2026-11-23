-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationRestrictionInvariants.mk_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:27.441261+00:00
-- url     : https://prove2.me/submissions/f76513f7-2bbf-44a4-a650-31ec8a4a53d6

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InnerHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes

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
theorem _root_.solution {A : Cx R} {n : ℕ} (z : A.Z n) :
    (Submodule.Quotient.mk z : A.H n) = 0 ↔ z.1 ∈ A.B n := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rfl
end ReciprocityTheory.Coh.InflationRestrictionInvariants
