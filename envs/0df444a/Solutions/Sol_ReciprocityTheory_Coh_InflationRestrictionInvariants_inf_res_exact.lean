-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationRestrictionInvariants.inf_res_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:01:35.109134+00:00
-- url     : https://prove2.me/submissions/d444c656-16ab-4afb-954c-2e826fbf1f6d

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InnerHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_oneCochain_apply_fin_one
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_memZ
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_memB
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_H_mk
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_mk_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_wach_d1_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_zeroDifferential_val
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_mem_oneCoboundaries_iff
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_cocycle_one
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
theorem _root_.solution (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)
    (hP : IsInvRep M N Q P) :
    Exact (P.hom.H 1) ((Pair.res M N.subtype continuous_subtype_val).hom.H 1) := by
  obtain ⟨hφ, hemb, hrg⟩ := hP
  have hφa : ∀ a, P.φ a = (a : G ⧸ N) := fun a => by rw [hφ]; rfl
  intro y
  constructor
  · intro hy
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [H_mk, mk_eq_zero_iff, mem_oneCoboundaries_iff] at hy
    obtain ⟨m0, hm0⟩ := hy
    obtain ⟨m, hm'⟩ : ∃ m : M.V, ∀ n : N, z.1.1 (e1 (n : G)) = M.rho n m - m := ⟨m0, hm0⟩
    obtain ⟨x', hx'⟩ : ∃ x' : M.coch.X 1, x' = z.1 - M.coch.d 0 (const0 M m) := ⟨_, rfl⟩
    have hx'v : ∀ a, x'.1 (e1 a) = z.1.1 (e1 a) - (M.rho a m - m) := fun a => by
      rw [hx']
      show z.1.1 (e1 a) - (M.coch.d 0 (const0 M m)).1 (e1 a) = _
      rw [zeroDifferential_val]; rfl
    have hx'c : M.coch.d 1 x' = 0 := by
      rw [hx', map_sub, (memZ _).1 z.2, M.coch.dd, sub_zero]
    have hcoc := (wach_d1_eq_zero_iff M x').1 hx'c
    have hN : ∀ n ∈ N, x'.1 (e1 n) = 0 := fun n hn => by rw [hx'v, hm' ⟨n, hn⟩, sub_self]
    have hconst : ∀ a n, n ∈ N → x'.1 (e1 (a * n)) = x'.1 (e1 a) := fun a n hn => by
      rw [hcoc, hN n hn, map_zero, add_zero]
    have hinv : ∀ a, ∀ n ∈ N, M.rho n (x'.1 (e1 a)) = x'.1 (e1 a) := fun a n hn => by
      have h1 := hcoc n a
      rw [hN n hn, zero_add] at h1
      rw [← h1]
      have : n * a = a * (a⁻¹ * n * a) := by group
      rw [this, hconst a _ (Subgroup.Normal.conj_mem' ‹_› n hn a)]
    have hmem : ∀ a, ∃ q, P.u q = x'.1 (e1 a) := fun a => (hrg _).2 (hinv a)
    choose F0 hF0 using hmem
    have hF0c : ∀ a b : G, (a : G ⧸ N) = b → F0 a = F0 b := fun a b hab => hemb.injective (by
      have hb : b = a * (a⁻¹ * b) := by group
      rw [hF0, hF0, hb, hconst a _ (QuotientGroup.eq.1 hab)])
    let F : G ⧸ N → Q.V := fun γ => F0 γ.out
    have hF : ∀ a : G, F a = F0 a := fun a => hF0c _ _ (QuotientGroup.out_eq' _)
    have hFc : Continuous F := by
      rw [hemb.continuous_iff, (QuotientGroup.isQuotientMap_mk N).continuous_iff]
      have : (P.u ∘ F) ∘ (QuotientGroup.mk : G → G ⧸ N) = fun a => x'.1 (e1 a) :=
        funext fun a => by simp only [comp_apply, hF, hF0]
      rw [this]
      exact (show Continuous x'.1 from x'.2).comp (continuous_pi fun _ => continuous_id)
    let w : Q.coch.X 1 := ⟨fun g => F (g 0), hFc.comp (continuous_apply 0)⟩
    have hw : Q.coch.d 1 w = 0 := by
      rw [wach_d1_eq_zero_iff]
      intro γ δ
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective γ
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective δ
      apply hemb.injective
      show P.u (F (↑a * ↑b)) = P.u (F ↑a + Q.rho ↑a (F ↑b))
      rw [← QuotientGroup.mk_mul, hF, hF, hF, map_add, ← hφa, P.equiv, hF0, hF0, hF0, hcoc]
    refine ⟨Submodule.Quotient.mk ⟨w, (memZ _).2 hw⟩, ?_⟩
    rw [H_mk, Submodule.Quotient.eq, Submodule.mem_comap]
    have hwx : P.hom.f 1 w = x' := Subtype.ext (funext fun g => by
      rw [oneCochain_apply_fin_one M _ g, oneCochain_apply_fin_one M x' g]
      show P.u (F (P.φ (g 0))) = x'.1 (e1 (g 0))
      rw [hφa, hF, hF0])
    show P.hom.f 1 w - z.1 ∈ M.coch.B 1
    rw [hwx, hx', memB]
    exact ⟨-const0 M m, by rw [map_neg]; abel⟩
  · rintro ⟨y0, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y0
    rw [H_mk, H_mk, mk_eq_zero_iff]
    have h0 : ((Pair.res M N.subtype continuous_subtype_val).hom.Z 1 (P.hom.Z 1 z)).1 = 0 :=
      Subtype.ext (funext fun g => by
        show P.u (z.1.1 (fun i => P.φ (g i).1)) = 0
        have : (fun i => P.φ (g i).1) = e1 1 :=
          funext fun i => by rw [hφa, (QuotientGroup.eq_one_iff _).2 (g i).2]
        rw [this, cocycle_one Q z.1 ((memZ _).1 z.2), map_zero])
    rw [h0]
    exact Submodule.zero_mem _
end ReciprocityTheory.Coh.InflationRestrictionInvariants
