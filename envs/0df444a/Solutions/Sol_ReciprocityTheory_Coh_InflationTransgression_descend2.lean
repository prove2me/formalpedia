-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTransgression.descend2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:48:03.038865+00:00
-- url     : https://prove2.me/submissions/892911e4-7b40-4774-b7cd-4bdc5c971ada

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionA
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionB

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
theorem _root_.solution (D : G → G → M.V) (hD : Continuous fun p : G × G => D p.1 p.2) (hI : InflD M N D) :
    ∃ z : Q.coch.X 2, ∀ a b : G, P.u (z.1 ![(a : G ⧸ N), b]) = D a b := by
  have hout : ∀ a b : G, D (Quotient.out (a : G ⧸ N)) (Quotient.out (b : G ⧸ N)) = D a b := by
    intro a b
    obtain ⟨h1, e1'⟩ := QuotientGroup.mk_out_eq_mul N a
    obtain ⟨h2, e2'⟩ := QuotientGroup.mk_out_eq_mul N b
    rw [e1', e2', hI.left, hI.right]
  let Dq : (G ⧸ N) × (G ⧸ N) → M.V := fun x => D x.1.out x.2.out
  have hq : Topology.IsQuotientMap (Prod.map (QuotientGroup.mk : G → G ⧸ N) (QuotientGroup.mk : G → G ⧸ N)) :=
    (QuotientGroup.isOpenMap_coe.prodMap QuotientGroup.isOpenMap_coe).isQuotientMap
      (continuous_quot_mk.prodMap continuous_quot_mk)
      (QuotientGroup.mk_surjective.prodMap QuotientGroup.mk_surjective)
  have hDq : Continuous Dq := by
    rw [hq.continuous_iff]
    have e : Dq ∘ Prod.map (QuotientGroup.mk : G → G ⧸ N) (QuotientGroup.mk : G → G ⧸ N) =
        fun p : G × G => D p.1 p.2 := funext fun p => hout p.1 p.2
    rw [e]
    exact hD
  have hmem : ∀ x, Dq x ∈ LinearMap.range P.u := fun x =>
    (hP.2.2 (Dq x)).2 fun g hg => hI.inv _ _ ⟨g, hg⟩
  let z0 : (G ⧸ N) × (G ⧸ N) → Q.V := fun x =>
    (LinearEquiv.ofInjective P.u hP.2.1.injective).symm ⟨Dq x, hmem x⟩
  have hz0u : ∀ x, P.u (z0 x) = Dq x := by
    intro x
    have := (LinearEquiv.ofInjective P.u hP.2.1.injective).apply_symm_apply ⟨Dq x, hmem x⟩
    exact congrArg Subtype.val this
  have hz0 : Continuous z0 := by
    rw [hP.2.1.continuous_iff]
    have e : (P.u ∘ z0) = Dq := funext hz0u
    rw [e]
    exact hDq
  refine ⟨⟨fun g => z0 (g 0, g 1), hz0.comp ((continuous_apply 0).prodMk (continuous_apply 1))⟩, fun a b => ?_⟩
  show P.u (z0 ((a : G ⧸ N), (b : G ⧸ N))) = D a b
  rw [hz0u]
  exact hout a b
end ReciprocityTheory.Coh.InflationTransgression
