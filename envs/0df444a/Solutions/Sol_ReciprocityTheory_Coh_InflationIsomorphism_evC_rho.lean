-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationIsomorphism.evC_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:46:25.965582+00:00
-- url     : https://prove2.me/submissions/54604c63-0396-4c7c-99d0-defcf898de2a

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
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [LocallyCompactSpace G] {N : Subgroup G} [N.Normal]
namespace ReciprocityTheory.Coh.InflationIsomorphism
theorem _root_.solution (M : TRep R G) [DiscreteTopology M.V] {QC : TRep R (G ⧸ N)} {PC : Pair QC (CG M)}
    (hC : IsInvRep (CG M) N QC PC) (q : QC.V) (g : G) :
    (evC M hC).u (QC.rho (g : G ⧸ N) q) = (PC.u q).1 g := by
  show (PC.u (QC.rho (g : G ⧸ N) q)).1 1 = _
  rw [inv_equiv hC]
  show (PC.u q).1 (1 * g) = _
  rw [one_mul]
end ReciprocityTheory.Coh.InflationIsomorphism
