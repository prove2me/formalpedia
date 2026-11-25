-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationIsomorphism.inv_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:01:56.131044+00:00
-- url     : https://prove2.me/submissions/9904b7eb-6d83-494c-b867-7d477c364e38

import Definitions.Def_ReciprocityTheory_GroupCohomology_CardLenStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfIsoA
import Theorems.Thm_ReciprocityTheory_Coh_InflationIsomorphism_stabN_open
import Theorems.Thm_ReciprocityTheory_Coh_InflationIsomorphism_finite_quot_of_open
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
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function Topology
noncomputable section
universe u
open ReciprocityTheory.Coh.InflationIsomorphism
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.InflationIsomorphism
theorem _root_.solution [CompactSpace G] (N : Subgroup G) (hN : IsClosed (N : Set G))
    (hW : ∀ W : Subgroup N, IsOpen (W : Set N) → IsUnit (W.index : R))
    (A B : TRep R G) [DiscreteTopology A.V] (p : A.V →ₗ[R] B.V)
    (hp : ∀ g a, p (A.rho g a) = B.rho g (p a)) (hs : Surjective p) (b : B.V)
    (hb : ∀ g ∈ N, B.rho g b = b) : ∃ a, (∀ g ∈ N, A.rho g a = a) ∧ p a = b := by
  have : CompactSpace N := isCompact_iff_compactSpace.1 hN.isCompact
  obtain ⟨a₀, rfl⟩ := hs b
  set W := stabN A N a₀
  have hWo := stabN_open A N a₀
  have : Finite (N ⧸ W) := finite_quot_of_open W hWo
  have : Fintype (N ⧸ W) := Fintype.ofFinite _
  obtain ⟨v, hv⟩ := hW W hWo
  set s : A.V := ∑ c : N ⧸ W, A.rho ((c.out : N) : G) a₀ with hs_def
  have key : ∀ (x : N), A.rho ((x : N) : G) a₀ = A.rho (((QuotientGroup.mk x : N ⧸ W).out : N) : G) a₀ := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul W x
    rw [hh, Subgroup.coe_mul, map_mul, Module.End.mul_apply, show A.rho ((h : N) : G) a₀ = a₀ from h.2]
  have hinv : ∀ g ∈ N, A.rho g s = s := by
    intro g hg
    rw [hs_def, map_sum]
    have e : ∀ c : N ⧸ W, A.rho g (A.rho ((c.out : N) : G) a₀) =
        A.rho ((((⟨g, hg⟩ : N) • c).out : N) : G) a₀ := by
      intro c
      rw [← Module.End.mul_apply, ← map_mul]
      have := key (⟨g, hg⟩ * c.out)
      rw [Subgroup.coe_mul] at this
      rw [this]
      congr 4
      conv_rhs => rw [← QuotientGroup.out_eq' c]
      rfl
    simp only [e]
    exact Fintype.sum_equiv (MulAction.toPerm (⟨g, hg⟩ : N)) _ _ (fun _ => rfl)
  refine ⟨((v⁻¹ : Rˣ) : R) • s, fun g hg => by rw [map_smul, hinv g hg], ?_⟩
  rw [map_smul, hs_def, map_sum]
  simp only [hp, fun c : N ⧸ W => hb _ c.out.2]
  have hcard : (Finset.univ : Finset (N ⧸ W)).card = W.index := by
    rw [Subgroup.index, Nat.card_eq_fintype_card, Finset.card_univ]
  rw [Finset.sum_const, hcard, ← Nat.cast_smul_eq_nsmul R, ← hv, smul_smul, Units.inv_mul, one_smul]
end ReciprocityTheory.Coh.InflationIsomorphism
