-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationRestrictionInvariants.inf_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:14.094862+00:00
-- url     : https://prove2.me/submissions/9e5c1baa-b172-4760-af5f-7720c4c65903

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InnerHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_memZ
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_H_mk
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_mk_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_mem_oneCoboundaries_iff
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_cocycle_one

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
theorem _root_.solution (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)
    (hP : IsInvRep M N Q P) : Injective (P.hom.H 1) := by
  obtain ⟨hφ, hemb, hrg⟩ := hP
  have hφa : ∀ a, P.φ a = (a : G ⧸ N) := fun a => by rw [hφ]; rfl
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro h hh
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  rw [H_mk, mk_eq_zero_iff, mem_oneCoboundaries_iff] at hh
  obtain ⟨m, hm⟩ := hh
  have hm' : ∀ a, P.u (z.1.1 (e1 (P.φ a))) = M.rho a m - m := hm
  have hz1 := cocycle_one Q z.1 ((memZ _).1 z.2)
  have hmN : ∀ g ∈ N, M.rho g m = m := fun g hg => by
    have := hm' g
    rw [hφa, (QuotientGroup.eq_one_iff g).2 hg, hz1, map_zero] at this
    exact (sub_eq_zero.1 this.symm)
  obtain ⟨q, rfl⟩ := (hrg m).2 hmN
  rw [mk_eq_zero_iff, mem_oneCoboundaries_iff]
  refine ⟨q, fun γ => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective γ
  apply hemb.injective
  rw [← hφa, hm' a, map_sub, P.equiv]
end ReciprocityTheory.Coh.InflationRestrictionInvariants
