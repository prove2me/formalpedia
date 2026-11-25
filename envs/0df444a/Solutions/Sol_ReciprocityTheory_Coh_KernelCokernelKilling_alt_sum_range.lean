-- Prove2me | solution 1 for ReciprocityTheory.Coh.KernelCokernelKilling.alt_sum_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:48:24.417169+00:00
-- url     : https://prove2.me/submissions/328872a4-6dbf-4741-aecb-e86afa27995c

import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_ShiftA
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
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
open ReciprocityTheory.Coh.KernelCokernelKilling
variable {R : Type u} [CommRing R] {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Subsingleton H]
namespace ReciprocityTheory.Coh.KernelCokernelKilling
theorem _root_.solution (m : ℕ) :
    (1 + ∑ j ∈ Finset.range (2 * m + 1), (-1 : R) ^ (j + 1)) = 0 ∧
      (1 + ∑ j ∈ Finset.range (2 * m + 2), (-1 : R) ^ (j + 1)) = 1 := by
  have key : ∀ n : ℕ, ∑ j ∈ Finset.range n, (-1 : R) ^ (j + 1) = if Even n then 0 else -1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rcases Nat.even_or_odd n with h | h
      · have h' : ¬ Even (n + 1) := by
          rw [Nat.even_add_one]
          exact not_not.mpr h
        rw [if_pos h, if_neg h', pow_succ, h.neg_one_pow]
        ring
      · have h' : Even (n + 1) := by
          rw [Nat.even_add_one]
          exact Nat.not_even_iff_odd.mpr h
        rw [if_neg (Nat.not_even_iff_odd.mpr h), if_pos h', pow_succ, h.neg_one_pow]
        ring
  refine ⟨?_, ?_⟩
  · rw [key, if_neg (by rw [Nat.not_even_iff_odd]; exact ⟨m, rfl⟩)]
    ring
  · rw [key, if_pos ⟨m + 1, by ring⟩]
    ring
end ReciprocityTheory.Coh.KernelCokernelKilling
