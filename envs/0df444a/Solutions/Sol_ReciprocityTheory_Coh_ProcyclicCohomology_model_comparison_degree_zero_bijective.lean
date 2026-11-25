-- Prove2me | solution 1 for ReciprocityTheory.Coh.ProcyclicCohomology.model_comparison_degree_zero_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:32:45.911685+00:00
-- url     : https://prove2.me/submissions/9609f1b0-cd23-43f0-b5ed-08275335658e

import Definitions.Def_ReciprocityTheory_GroupCohomology_MemZpowersQuot
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_GroupCohomology_ModelComparisonDegreeZeroBijective
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_cocycle_eq_of_apply
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_exists_cocycle
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
open ReciprocityTheory.Coh.ProcyclicCohomology
open ReciprocityTheory.Gal Function
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.ProcyclicCohomology
theorem _root_.solution [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] {s : G}
    (hc : ∀ a b : G, a * b = b * a) (hs : Dense (Subgroup.zpowers s : Set G))
    (hidx : ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k)
    (htor : ∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) :
    ∃ e : H1 M.rho ≃ₗ[R] M.V ⧸ LinearMap.range (M.rho s - LinearMap.id),
      ∀ c : Z1 M.rho, e (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c.1 s) := by
  set P := LinearMap.range (M.rho s - LinearMap.id)
  let f : Z1 M.rho →ₗ[R] M.V ⧸ P := P.mkQ ∘ₗ ((LinearMap.proj s) ∘ₗ (Z1 M.rho).subtype)
  have hf : ∀ c : Z1 M.rho, f c = Submodule.Quotient.mk (c.1 s) := fun c => rfl
  have hker : (B1 M.rho).comap (Z1 M.rho).subtype ≤ LinearMap.ker f := by
    intro c hc'
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hc'
    rw [LinearMap.mem_ker, hf, Submodule.Quotient.mk_eq_zero]
    exact ⟨m, by simpa using (hm s).symm⟩
  let φ := ((B1 M.rho).comap (Z1 M.rho).subtype).liftQ f hker
  have hφ : ∀ c : Z1 M.rho, φ (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c.1 s) :=
    fun c => rfl
  have hinj : Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hφ, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨m, hm⟩ := hx
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
    refine ⟨m, cocycle_eq_of_apply M hs c.1 c.2 m ?_⟩
    rw [← hm]; simp
  have hsurj : Surjective φ := by
    intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨c, hcZ, hcs⟩ := exists_cocycle M hc hs hidx m (htor m)
    exact ⟨Submodule.Quotient.mk ⟨c, hcZ⟩, by rw [hφ]; simp [hcs]⟩
  exact ⟨LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun c => hφ c⟩
end ReciprocityTheory.Coh.ProcyclicCohomology
