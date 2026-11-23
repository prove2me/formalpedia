-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationIsomorphism.invPair_u
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:13.962108+00:00
-- url     : https://prove2.me/submissions/4e57ade3-0209-4059-95ab-88dc46b0e3f0

import Definitions.Def_ReciprocityTheory_GroupCohomology_InfIsoA
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfIsoB

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
variable {N : Subgroup G} [N.Normal]
namespace ReciprocityTheory.Coh.InflationIsomorphism
theorem _root_.solution {A B : TRep R G} {QA : TRep R (G ⧸ N)} {PA : Pair QA A} {QB : TRep R (G ⧸ N)}
    {PB : Pair QB B} [DiscreteTopology A.V] (hA : IsInvRep A N QA PA) (hB : IsInvRep B N QB PB)
    (a : A.V →ₗ[R] B.V) (ha : ∀ g m, a (A.rho g m) = B.rho g (a m)) (q : QA.V) :
    PB.u ((invPair hA hB a ha).u q) = a (PA.u q) := invLin_spec hA hB a ha q
end ReciprocityTheory.Coh.InflationIsomorphism
