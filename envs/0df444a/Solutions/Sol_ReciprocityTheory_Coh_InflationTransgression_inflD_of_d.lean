-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTransgression.inflD_of_d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:04.125906+00:00
-- url     : https://prove2.me/submissions/4e48a99b-3e88-45e2-a41b-b24d5d01d01a

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionA
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionB
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_inflation_hom_degree_two_apply
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_oneDifferential_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationTransgression
open ReciprocityTheory.Gal ReciprocityTheory.Coh Cx Function InflationRestrictionInvariants
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)
  (hP : IsInvRep M N Q P)
include hP
namespace ReciprocityTheory.Coh.InflationTransgression
theorem _root_.solution (y : M.coch.X 1) (z : Q.coch.X 2) (h : M.coch.d 1 y = P.hom.f 2 z) :
    InflD M N (D1 M fun g => y.1 (e1 g)) := by
  have key : ∀ a b, D1 M (fun g => y.1 (e1 g)) a b = P.u (z.1 ![(a : G ⧸ N), b]) := by
    intro a b
    show M.rho a (y.1 (e1 b)) - y.1 (e1 (a * b)) + y.1 (e1 a) = _
    rw [← oneDifferential_val, h, inflation_hom_degree_two_apply M N Q P hP z a b]
  refine ⟨fun a b n => ?_, fun a b n => ?_, fun a b n => ?_⟩
  · rw [key, key, QuotientGroup.mk_mul_of_mem b n.2]
  · rw [key, key, QuotientGroup.mk_mul_of_mem a n.2]
  · rw [key]
    exact (hP.2.2 _).1 ⟨_, rfl⟩ n n.2
end ReciprocityTheory.Coh.InflationTransgression
