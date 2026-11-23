-- Prove2me | solution 1 for ReciprocityTheory.Coh.ProcyclicCohomology.cocycle_eq_of_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:31.392615+00:00
-- url     : https://prove2.me/submissions/09b18a31-221d-45a3-8757-e7c010c46a5b

import Definitions.Def_ReciprocityTheory_GroupCohomology_MemZpowersQuot
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_GroupCohomology_ModelComparisonDegreeZeroBijective
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
open ReciprocityTheory.Gal Topology
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.ProcyclicCohomology
theorem _root_.solution (M : TRep R G) [DiscreteTopology M.V] {s : G}
    (hs : Dense (Subgroup.zpowers s : Set G)) (c : G → M.V) (hc : c ∈ Z1 M.rho) (m : M.V)
    (hm : c s = M.rho s m - m) (g : G) : c g = M.rho g m - m := by
  have hcont : Continuous fun a : G => M.rho a m :=
    M.cont.comp (f := fun a : G => (a, m)) (continuous_id.prodMk continuous_const)
  have hcl : IsClosed {a : G | c a = M.rho a m - m} :=
    isClosed_eq hc.1 (hcont.sub continuous_const)
  have step : ∀ a : G, c (a * s) - (M.rho (a * s) m - m) = c a - (M.rho a m - m) := by
    intro a
    rw [hc.2, hm, map_mul, Module.End.mul_apply]
    simp only [map_sub]; abel
  have hz : ∀ i : ℤ, c (s ^ i) = M.rho (s ^ i) m - m := by
    have h0 : c (s ^ (0 : ℤ)) - (M.rho (s ^ (0 : ℤ)) m - m) = 0 := by
      have e := hc.2 1 1
      simp only [mul_one, map_one, Module.End.one_apply] at e
      simp only [zpow_zero, map_one, Module.End.one_apply, sub_self, sub_zero]
      exact (add_eq_left.1 e.symm)
    intro i
    have : c (s ^ i) - (M.rho (s ^ i) m - m) = 0 := by
      induction i using Int.induction_on with
      | zero => exact h0
      | succ i ih => rw [zpow_add_one, step, ih]
      | pred i ih => rw [← ih, ← step, zpow_sub_one, inv_mul_cancel_right]
    exact sub_eq_zero.1 this
  have hsub : (Subgroup.zpowers s : Set G) ⊆ {a : G | c a = M.rho a m - m} := by
    intro x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact hz i
  have h := hcl.closure_subset_iff.2 hsub
  rw [hs.closure_eq] at h
  exact h (Set.mem_univ g)
end ReciprocityTheory.Coh.ProcyclicCohomology
