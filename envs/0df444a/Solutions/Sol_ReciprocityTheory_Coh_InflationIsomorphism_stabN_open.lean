-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationIsomorphism.stabN_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:46:03.947026+00:00
-- url     : https://prove2.me/submissions/ce3b9c2d-7747-454f-97e8-3f6bf332da8d

import Definitions.Def_ReciprocityTheory_GroupCohomology_CardLenStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfIsoA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function Topology
noncomputable section
universe u
open ReciprocityTheory.Coh.InflationIsomorphism
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.InflationIsomorphism
theorem _root_.solution (A : TRep R G) [DiscreteTopology A.V] (N : Subgroup G) (a : A.V) :
    IsOpen (stabN A N a : Set N) := by
  have hc : Continuous fun n : N => A.rho (n : G) a :=
    A.cont.comp (f := fun n : N => ((n : G), a)) (continuous_subtype_val.prodMk continuous_const)
  exact (isOpen_discrete {a}).preimage hc
end ReciprocityTheory.Coh.InflationIsomorphism
