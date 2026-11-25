-- Prove2me | solution 1 for ReciprocityTheory.Coh.ProcyclicCohomology.exists_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:19:16.1308+00:00
-- url     : https://prove2.me/submissions/06d193f1-e1d7-45c9-8e0c-799a74803b66

import Definitions.Def_ReciprocityTheory_GroupCohomology_MemZpowersQuot
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_GroupCohomology_ModelComparisonDegreeZeroBijective
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_stab_isOpen
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_rho_comm
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_psum_add
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
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_desc_continuous
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_desc_eq
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_exists_pow
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_index_pos
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_per_mul
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_zpow_mem_iff
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
theorem _root_.solution [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] {s : G}
    (hc : ∀ a b : G, a * b = b * a) (hs : Dense (Subgroup.zpowers s : Set G))
    (hidx : ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k)
    (m : M.V) (hk : ∃ k : ℕ, 0 < k ∧ k • m = 0) : ∃ c ∈ Z1 M.rho, c s = m := by
  obtain ⟨k, hk0, hkm⟩ := hk
  set V := stab M m
  have hVo := stab_isOpen M m
  set a := V.index
  have ha : 0 < a := index_pos hc hVo
  have hsa : s ^ a ∈ V := by
    have := (zpow_mem_iff hc hs hVo (a : ℤ)).2 dvd_rfl
    simpa using this
  obtain ⟨W0, hW0o, hW0i⟩ := hidx (a * k) (Nat.mul_pos ha hk0)
  set W := V ⊓ W0
  have hWo : IsOpen (W : Set G) := hVo.inter hW0o
  have hWV : W ≤ V := inf_le_left
  have hdvd : a * k ∣ W.index := hW0i ▸ Subgroup.index_dvd_of_le inf_le_right

  have hfixV : ∀ v ∈ V, ∀ j, M.rho v (psum M s m j) = psum M s m j := by
    intro v hv j
    simp only [psum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rho_comm M hc]
    rw [show M.rho v m = m from hv]
  have hmul : ∀ t, psum M s m (a * t) = t • psum M s m a := by
    intro t
    induction t with
    | zero => simp [psum]
    | succ t ih =>
      rw [Nat.mul_succ, psum_add, ih, hfixV _ (by rw [pow_mul]; exact V.pow_mem hsa t), succ_nsmul]
  have hN : psum M s m (a * k) = 0 := by
    rw [hmul, psum, Finset.smul_sum]
    simp only [← map_nsmul, hkm, map_zero, Finset.sum_const_zero]
  have hperN : ∀ j, psum M s m (j + a * k) = psum M s m j := by
    intro j; rw [psum_add, hN, map_zero, add_zero]
  have hper : ∀ j, psum M s m (j + W.index) = psum M s m j := by
    obtain ⟨t, ht⟩ := hdvd
    intro j; rw [ht]; exact per_mul _ _ hperN j t
  have hex := exists_pow hc hs hWo
  refine ⟨desc W hex (psum M s m), ⟨desc_continuous hc hs hWo hex _ hper, fun g h => ?_⟩, ?_⟩
  · have hg := Classical.choose_spec (hex g)
    have hh := Classical.choose_spec (hex h)
    set i := Classical.choose (hex g)
    set j := Classical.choose (hex h)
    have hgh : (g * h)⁻¹ * s ^ (i + j) ∈ W := by
      have e : (g * h)⁻¹ * s ^ (i + j) = (g⁻¹ * s ^ i) * (h⁻¹ * s ^ j) := by
        calc (g * h)⁻¹ * s ^ (i + j) = h⁻¹ * (g⁻¹ * s ^ i) * s ^ j := by
              rw [mul_inv_rev, pow_add]; group
          _ = (g⁻¹ * s ^ i) * (h⁻¹ * s ^ j) := by rw [hc h⁻¹ (g⁻¹ * s ^ i), mul_assoc]
      rw [e]; exact W.mul_mem hg hh
    have e1 : desc W hex (psum M s m) (g * h) = psum M s m (i + j) := desc_eq hc hs hWo hex _ hper hgh
    have e2 : desc W hex (psum M s m) g = psum M s m i := rfl
    have e3 : desc W hex (psum M s m) h = psum M s m j := rfl
    rw [e1, e2, e3, psum_add]
    congr 1
    have hgeq : g = s ^ i * (g⁻¹ * s ^ i)⁻¹ := by group
    conv_rhs => rw [hgeq, map_mul, Module.End.mul_apply]
    rw [hfixV _ (hWV (W.inv_mem hg))]
  · have : desc W hex (psum M s m) s = psum M s m 1 :=
      desc_eq hc hs hWo hex _ hper (by simp)
    rw [this]; simp [psum]
end ReciprocityTheory.Coh.ProcyclicCohomology
