-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kur_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:58:58.31773+00:00
-- url     : https://prove2.me/submissions/7ea8a02e-d905-48b5-a65c-846212d94bcf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorHensel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_sqrt_mem_Kur
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_mem_kurAlg
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
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_Tmap_mk
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_dHom_apply
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_kerMap_coe
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_degLK_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_dvd_qK_pow_sub_one
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
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.Tmap_mk
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.dHom_apply
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.kerMap_coe



set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) {d : ℕ} (hld : ¬ l ∣ d) {s : PadicAlgCl l}
    (hs : s ^ 2 = -(d : PadicAlgCl l)) {y : PadicAlgCl l}
    (hy : y ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l (IntermediateField.adjoin ℚ_[l] {s})) :
    algebraMap (PadicAlgCl l) ℂ_[l] y ∈ MaximalUnramifiedExtension l := by
  have hK : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {s}) := by
    first
    | exact IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral s)
    | exact IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic s).isIntegral

  have hq2 : 2 ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) := by
    by_contra hlt
    push_neg at hlt
    have h1 : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ 1 - 1 = 0 := by rw [pow_one]; omega
    have h2 : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ 2 - 1 = 0 := by
      have : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ 2 ≤ 1 := by
        calc ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left (by omega) 2
          _ = 1 := one_pow 2
      omega
    have e : ReciprocityTheory.DiscreteGroups.LocalClassField.Kn l (IntermediateField.adjoin ℚ_[l] {s}) 1 = ReciprocityTheory.DiscreteGroups.LocalClassField.Kn l (IntermediateField.adjoin ℚ_[l] {s}) 2 := by simp only [ReciprocityTheory.DiscreteGroups.LocalClassField.Kn, h1, h2]
    have d1 := ReciprocityTheory.DiscreteGroups.LocalClassField.degLK_Kn (p := l) (K := (IntermediateField.adjoin ℚ_[l] {s})) hK (n := 1) one_pos
    have d2 := ReciprocityTheory.DiscreteGroups.LocalClassField.degLK_Kn (p := l) (K := (IntermediateField.adjoin ℚ_[l] {s})) hK (n := 2) two_pos
    rw [e, d2] at d1
    omega

  have hlq : l ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) := by
    by_contra h
    obtain ⟨n, hn, hdvd⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_dvd_qK_pow_sub_one (p := l) (K := (IntermediateField.adjoin ℚ_[l] {s})) hK h
    have h1 : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ n := dvd_pow_self _ hn.ne'
    have hpos : 1 ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ n := Nat.one_le_pow _ _ (by omega)
    have h3 : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ n - (ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ n - 1) := by
      first
      | exact Nat.dvd_sub h1 hdvd
      | exact Nat.dvd_sub (by omega) h1 hdvd
    rw [Nat.sub_sub_self hpos] at h3
    have := Nat.le_of_dvd one_pos h3
    omega
  have hnd : ∀ k, 0 < k → ¬ l ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ k - 1 := by
    intro k hk h
    have h1 : l ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ k := hlq.trans (dvd_pow_self _ hk.ne')
    have hpos : 1 ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ k := Nat.one_le_pow _ _ (by omega)
    have h3 : l ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ k - (ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ k - 1) := by
      first
      | exact Nat.dvd_sub h1 h
      | exact Nat.dvd_sub (by omega) h1 h
    rw [Nat.sub_sub_self hpos] at h3
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h3)

  have hle : ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l (IntermediateField.adjoin ℚ_[l] {s}) ≤ kurAlg l := by
    refine iSup_le fun n => sup_le ?_ ?_
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [SetLike.mem_coe, mem_kurAlg]
      refine sqrt_mem_Kur hl hld ?_
      rw [← map_pow, hs, map_neg, map_natCast]
    · rw [IntermediateField.adjoin_le_iff]
      intro ζ hζ
      have hζ0 : ζ ^ (ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ (n + 1) - 1) = 1 := hζ
      rw [SetLike.mem_coe, mem_kurAlg]
      have hζ' : (algebraMap (PadicAlgCl l) ℂ_[l] ζ) ^ (ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ (n + 1) - 1) = 1 := by
        rw [← map_pow, hζ0, map_one]
      have hN : 0 < ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ (n + 1) - 1 := by
        have : 2 ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ (n + 1) := le_trans hq2 (Nat.le_self_pow (by omega) _)
        omega
      exact Subfield.le_topologicalClosure _
        (Subfield.subset_closure ⟨_, hN, hnd (n + 1) (Nat.succ_pos n), hζ'⟩)
  exact mem_kurAlg.1 (hle hy)
end ReciprocityTheory.ChartRestriction.L1
