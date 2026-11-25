-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationIsomorphism.deg0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:46:20.016618+00:00
-- url     : https://prove2.me/submissions/bad9dec7-29e7-47e8-930c-09333677b4f4

import Definitions.Def_ReciprocityTheory_GroupCohomology_InfIsoA
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfIsoB
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_mk_525460e2150b
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_Z_apply
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_comp_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_H
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_add
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_d
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_neg
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_smul
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_sub
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_zero
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_H_mk
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_mk_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_oneCochain_apply_fin_one
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_zeroDifferential_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.H_cls
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.Z_apply
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.comp_f
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_H
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_f
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_add
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_d
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_eq_zero_iff
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_neg
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_smul
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_sub
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function Topology
noncomputable section
universe u
open ReciprocityTheory.Coh.InflationIsomorphism
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {N : Subgroup G} [N.Normal]
namespace ReciprocityTheory.Coh.InflationIsomorphism
theorem _root_.solution (A : TRep R G) (Q : TRep R (G ⧸ N)) (P : Pair Q A) (hP : IsInvRep A N Q P) :
    Bijective (P.hom.H 0) := by
  have hsub : ∀ {X : Type u} (f f' : Fin 0 → X), f = f' := fun f f' => Subsingleton.elim _ _
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [InflationRestrictionInvariants.H_mk, InflationRestrictionInvariants.mk_eq_zero_iff] at hz
    have h0 : P.hom.f 0 x = 0 := hz
    have hx0 : x = 0 := by
      refine Subtype.ext (funext fun f => ?_)
      have : P.u (x.1 fun i => P.φ (![] i)) = 0 := congrArg (fun y : A.coch.X 0 => y.1 ![]) h0
      apply hP.2.1.injective
      refine (show P.u (x.1 f) = P.u 0 from ?_)
      rw [map_zero, hsub f (fun i => P.φ (![] i))]
      exact this
    rw [InflationRestrictionInvariants.mk_eq_zero_iff]
    subst hx0
    exact Submodule.zero_mem _
  · intro z
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hy' : A.coch.d 0 y = 0 := hy
    have hinvG : ∀ a, A.rho a (y.1 ![]) = y.1 ![] := fun a => by
      have := congrArg (fun w : A.coch.X 1 => w.1 (InflationRestrictionInvariants.e1 a)) hy'
      simp only [InflationRestrictionInvariants.zeroDifferential_val] at this
      exact sub_eq_zero.1 this
    obtain ⟨q, hq⟩ := (hP.2.2 (y.1 ![])).2 fun g _ => hinvG g
    have hdq : Q.coch.d 0 (InflationRestrictionInvariants.const0 Q q) = 0 := by
      refine Subtype.ext (funext fun g => ?_)
      rw [InflationRestrictionInvariants.oneCochain_apply_fin_one, InflationRestrictionInvariants.zeroDifferential_val]
      show Q.rho (g 0) q - q = 0
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (g 0)
      rw [← ha, sub_eq_zero]
      apply hP.2.1.injective
      rw [inv_equiv hP, hq, hinvG]
    refine ⟨Submodule.Quotient.mk ⟨InflationRestrictionInvariants.const0 Q q, hdq⟩, ?_⟩
    rw [InflationRestrictionInvariants.H_mk]
    congr 1
    refine Subtype.ext (Subtype.ext (funext fun f => ?_))
    show P.u q = y.1 f
    rw [hq, hsub f ![]]
end ReciprocityTheory.Coh.InflationIsomorphism
