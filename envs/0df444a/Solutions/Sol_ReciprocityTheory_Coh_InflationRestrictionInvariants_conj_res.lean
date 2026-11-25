-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationRestrictionInvariants.conj_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:00:29.88214+00:00
-- url     : https://prove2.me/submissions/9f273295-8807-48fc-9735-239e50e0397f

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InnerHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_H_mk
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
import Theorems.Thm_ReciprocityTheory_Coh_inner_holds
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
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants
open ReciprocityTheory.Gal Cx Function
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.InflationRestrictionInvariants
theorem _root_.solution (M : TRep R G) (N : Subgroup G) (s : G) (c : Pair (M.resSub N) (M.resSub N))
    (hc : ∀ g, (c.φ g : G) = s⁻¹ * g * s) (hu : ∀ m, c.u m = M.rho s m) (n : ℕ) (x : M.H n) :
    c.hom.H n ((Pair.res M N.subtype continuous_subtype_val).hom.H n x) =
      (Pair.res M N.subtype continuous_subtype_val).hom.H n x := by
  have hinner := inner_holds R G M (conjPair M s) s (fun g => rfl) (fun m => rfl) n
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  calc c.hom.H n ((Pair.res M N.subtype continuous_subtype_val).hom.H n (Submodule.Quotient.mk z))
      = (Pair.res M N.subtype continuous_subtype_val).hom.H n
          ((conjPair M s).hom.H n (Submodule.Quotient.mk z)) := by
        rw [H_mk, H_mk, H_mk, H_mk]
        congr 1
        apply Subtype.ext; apply Subtype.ext; funext g
        show c.u (z.1.1 fun i => ((c.φ (g i)) : G)) = M.rho s (z.1.1 fun i => s⁻¹ * (g i : G) * s)
        simp only [hc]; exact hu _
    _ = _ := by rw [hinner, LinearMap.id_apply]
end ReciprocityTheory.Coh.InflationRestrictionInvariants
