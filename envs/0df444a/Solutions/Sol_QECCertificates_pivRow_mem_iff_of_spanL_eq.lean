-- Prove2me | solution 1 for QECCertificates.pivRow_mem_iff_of_spanL_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:46.574741+00:00
-- url     : https://prove2.me/submissions/cb009cf4-d79e-41f6-bd2d-7b5641976daa

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Theorems.Thm_QECCertificates_readOff_nil
public import Theorems.Thm_QECCertificates_readOff_eq_of_mem_spanL
public import Theorems.Thm_QECCertificates_ne_zero_of_piv_eq_one
public import Theorems.Thm_QECCertificates_leadIdx_eq_piv_of_isEchelon
public import Theorems.Thm_QECCertificates_exists_piv_eq_leadIdx_of_mem_spanL
public import Theorems.Thm_QECCertificates_IsReduced_pivot_inj
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
public import Theorems.Thm_QECCertificates_subset_spanL
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_kerL
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil


attribute [local simp] QECCertificates.readOff_nil

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D₁ D₂ : List (PivRow n)} (h₁ : IsEchelon D₁)
    (h₂ : IsEchelon D₂) (hspan : spanL (rowList D₁) = spanL (rowList D₂)) :
    ∀ x : PivRow n, x ∈ D₁ ↔ x ∈ D₂ := by
  have hPiv12 : ∀ ri ∈ D₁, ∃ rj ∈ D₂, rj.2 = ri.2 := by
    intro ri hri
    have hne : ri.1 ≠ 0 := ne_zero_of_piv_eq_one (h₁.1.1 ri hri)
    have hmem : ri.1 ∈ spanL (rowList D₂) :=
      hspan ▸ subset_spanL (List.mem_map_of_mem hri)
    obtain ⟨rj, hrj, hrj2⟩ := exists_piv_eq_leadIdx_of_mem_spanL h₂ hmem hne
    exact ⟨rj, hrj, by rw [hrj2, leadIdx_eq_piv_of_isEchelon h₁ hri (hne := hne)]⟩
  have hPiv21 : ∀ rj ∈ D₂, ∃ ri ∈ D₁, ri.2 = rj.2 := by
    intro rj hrj
    have hne : rj.1 ≠ 0 := ne_zero_of_piv_eq_one (h₂.1.1 rj hrj)
    have hmem : rj.1 ∈ spanL (rowList D₁) :=
      hspan ▸ subset_spanL (List.mem_map_of_mem hrj)
    obtain ⟨ri, hri, hri2⟩ := exists_piv_eq_leadIdx_of_mem_spanL h₁ hmem hne
    exact ⟨ri, hri, by rw [hri2, leadIdx_eq_piv_of_isEchelon h₂ hrj (hne := hne)]⟩
  have hPivSet : (D₁.map (·.2)).toFinset = (D₂.map (·.2)).toFinset := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro p hp
      rw [List.mem_toFinset, List.mem_map] at hp
      obtain ⟨ri, hri, rfl⟩ := hp
      obtain ⟨rj, hrj, hrj2⟩ := hPiv12 ri hri
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨rj, hrj, hrj2⟩)
    · intro p hp
      rw [List.mem_toFinset, List.mem_map] at hp
      obtain ⟨rj, hrj, rfl⟩ := hp
      obtain ⟨ri, hri, hri2⟩ := hPiv21 rj hrj
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨ri, hri, hri2⟩)
  have hRow : ∀ x ∈ D₁, ∃ rj ∈ D₂, x = rj := by
    intro x hx
    obtain ⟨rj, hrj, hrj2⟩ := hPiv12 x hx
    have hxmem : x.1 ∈ spanL (rowList D₂) := hspan ▸ subset_spanL (List.mem_map_of_mem hx)
    have hrow : x.1 = rj.1 := by
      rw [← readOff_eq_of_mem_spanL h₂.1 hxmem]
      simp only [readOff]
      refine (Finset.sum_eq_single (s := D₂.toFinset)
        (f := fun rk : PivRow n => (x.1 rk.2) • rk.1) rj ?_ ?_).trans ?_
      · intro rk hrk hne
        have hrkD : rk ∈ D₂ := List.mem_toFinset.mp hrk
        have hmemP : rk.2 ∈ (D₁.map (·.2)).toFinset := by
          rw [hPivSet]
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨rk, hrkD, rfl⟩)
        rw [List.mem_toFinset, List.mem_map] at hmemP
        obtain ⟨ri, hri, hri2⟩ := hmemP
        have hne' : ri ≠ x := by
          intro heq
          have hpiv : rk.2 = rj.2 := by rw [← hri2, heq, ← hrj2]
          exact hne (h₂.1.pivot_inj rk hrkD rj hrj hpiv)
        rw [← hri2, h₁.1.2 x hx ri hri hne'.symm, zero_smul]
      · intro hnot
        exact absurd (List.mem_toFinset.mpr hrj) hnot
      · rw [hrj2, h₁.1.1 x hx, one_smul]
    exact ⟨rj, hrj, Prod.ext hrow hrj2.symm⟩
  intro x
  constructor
  · intro hx
    obtain ⟨rj, hrj, rfl⟩ := hRow x hx
    exact hrj
  · intro hx
    obtain ⟨ri, hri, hri2⟩ := hPiv21 x hx
    have hxmem : x.1 ∈ spanL (rowList D₁) := hspan ▸ subset_spanL (List.mem_map_of_mem hx)
    have hrow : x.1 = ri.1 := by
      rw [← readOff_eq_of_mem_spanL h₁.1 hxmem]
      simp only [readOff]
      refine (Finset.sum_eq_single (s := D₁.toFinset)
        (f := fun rk : PivRow n => (x.1 rk.2) • rk.1) ri ?_ ?_).trans ?_
      · intro rk hrk hne
        have hrkD : rk ∈ D₁ := List.mem_toFinset.mp hrk
        have hmemP : rk.2 ∈ (D₂.map (·.2)).toFinset := by
          rw [← hPivSet]
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨rk, hrkD, rfl⟩)
        rw [List.mem_toFinset, List.mem_map] at hmemP
        obtain ⟨rj, hrj, hrj2⟩ := hmemP
        have hne' : rj ≠ x := by
          intro heq
          have hpiv : rk.2 = ri.2 := by rw [← hrj2, heq, ← hri2]
          exact hne (h₁.1.pivot_inj rk hrkD ri hri hpiv)
        rw [← hrj2, h₂.1.2 x hx rj hrj hne'.symm, zero_smul]
      · intro hnot
        exact absurd (List.mem_toFinset.mpr hri) hnot
      · rw [hri2, h₂.1.1 x hx, one_smul]
    have hxeq : x = ri := Prod.ext hrow hri2.symm
    rw [hxeq]
    exact hri
end QECCertificates
