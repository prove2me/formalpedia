-- Prove2me | solution 1 for QECCertificates.eq_zero_of_mem_spanL_of_piv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:54.199807+00:00
-- url     : https://prove2.me/submissions/ed27bf04-644c-41cb-9fc3-06649dedf4e4

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_range_get_eq_rowList
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
theorem _root_.solution {D : List (PivRow n)} (h1 : EchSelf D)
    (h2 : EchPair D) {w : Vec n} (hw : w ∈ spanL (rowList D))
    (h0 : ∀ i : Fin D.length, w (D.get i).2 = 0) : w = 0 := by
  have hspan : spanL (rowList D)
      = Submodule.span (ZMod 2) (Set.range fun i : Fin D.length => (D.get i).1) := by
    rw [spanL, range_get_eq_rowList D]
  have hw' : w ∈ Submodule.span (ZMod 2)
      (Set.range fun i : Fin D.length => (D.get i).1) := by
    rw [← hspan]
    exact hw
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)
    (v := fun i : Fin D.length => (D.get i).1) (x := w)).mp hw'
  by_contra hw0
  have hex : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (by rw [← hc]; exact Finset.sum_eq_zero fun i _ => by rw [h i, zero_smul])
  obtain ⟨i₀, hi₀⟩ := hex
  have ht : (Finset.univ.filter (fun a => c a ≠ 0)).Nonempty :=
    ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hi₀⟩⟩
  set j := (Finset.univ.filter (fun a => c a ≠ 0)).min' ht with hj
  have hjne : c j ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem _ ht)).2
  have hmin : ∀ a, c a ≠ 0 → j ≤ a := fun a ha =>
    Finset.min'_le _ a (Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩)
  have hcol := congrFun hc ((D.get j).2)
  rw [Finset.sum_apply] at hcol
  simp only [Pi.smul_apply, smul_eq_mul] at hcol
  have hcongr : ∑ i, c i * ((D.get i).1 ((D.get j).2))
      = ∑ i, c i * (if i = j then (1 : ZMod 2) else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hij : i = j
    · rw [hij, if_pos rfl, mul_one, h1 j, mul_one]
    · rcases lt_trichotomy i j with hlt | heq | hgt
      · -- Minimality kills earlier coefficients; the echelon condition controls later rows.
        have hc0 : c i = 0 := by
          by_contra hc'
          exact absurd (hmin i hc') (not_le.mpr hlt)
        rw [hc0]; simp
      · exact absurd heq hij
      · rw [h2 j i hgt, if_neg hij, mul_zero]
  rw [hcongr] at hcol
  have hcollapse : ∑ i, c i * (if i = j then (1 : ZMod 2) else 0) = c j := by
    have hh := Finset.sum_eq_single (s := Finset.univ)
      (f := fun i => c i * (if i = j then (1 : ZMod 2) else 0)) j
      (fun b _ hne => by rw [if_neg hne, mul_zero])
      (fun hnot => absurd (Finset.mem_univ j) hnot)
    rwa [if_pos rfl, mul_one] at hh
  rw [hcollapse] at hcol
  exact hjne (by rw [hcol, h0 j])
end QECCertificates
