-- Prove2me | solution 1 for QECCertificates.linearIndependent_get_of_echelon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:56:33.023705+00:00
-- url     : https://prove2.me/submissions/4a6d8bdf-ae35-4c9c-ae09-a66a3ff2e341

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_kerL
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (h1 : EchSelf D) (h2 : EchPair D) :
    LinearIndependent (ZMod 2) (fun i : Fin D.length => (D.get i).1) := by
  rw [linearIndependent_iff']
  intro s g hsum
  by_contra hcon
  push Not at hcon
  obtain ⟨i₀, hi₀, hne₀⟩ := hcon
  have ht : (s.filter (fun a => g a ≠ 0)).Nonempty :=
    ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, hne₀⟩⟩
  set j := (s.filter (fun a => g a ≠ 0)).min' ht with hj
  have hjmem : j ∈ s ∧ g j ≠ 0 := Finset.mem_filter.mp (Finset.min'_mem _ ht)
  have hmin : ∀ a ∈ s, g a ≠ 0 → j ≤ a := fun a ha hae =>
    Finset.min'_le _ a (Finset.mem_filter.mpr ⟨ha, hae⟩)
  have hcol := congrFun hsum ((D.get j).2)
  rw [Finset.sum_apply] at hcol
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcol
  have hcongr : ∑ a ∈ s, g a * ((D.get a).1 ((D.get j).2))
      = ∑ a ∈ s, g a * (if a = j then (1 : ZMod 2) else 0) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    by_cases haj : a = j
    · rw [haj, if_pos rfl, mul_one, h1 j, mul_one]
    · rcases lt_trichotomy j a with hlt | heq | hgt
      · rw [h2 j a hlt, if_neg haj, mul_zero]
      · exact absurd heq.symm haj
      · have hg0 : g a = 0 := by
          by_contra hg
          exact absurd (hmin a ha hg) (not_le.mpr hgt)
        rw [hg0]; simp
  rw [hcongr] at hcol
  have hcollapse : ∑ a ∈ s, g a * (if a = j then (1 : ZMod 2) else 0) = g j := by
    have hh := Finset.sum_eq_single (s := s)
      (f := fun a => g a * (if a = j then (1 : ZMod 2) else 0)) j
      (fun b _ hne => by rw [if_neg hne, mul_zero])
      (fun hnot => absurd hjmem.1 hnot)
    rwa [if_pos rfl, mul_one] at hh
  rw [hcollapse] at hcol
  exact hjmem.2 hcol
end QECCertificates
