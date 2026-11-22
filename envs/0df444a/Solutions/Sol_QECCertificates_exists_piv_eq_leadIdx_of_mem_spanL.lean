-- Prove2me | solution 1 for QECCertificates.exists_piv_eq_leadIdx_of_mem_spanL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:02.285853+00:00
-- url     : https://prove2.me/submissions/63f4f759-ed24-4498-8b69-2211815ee664

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Theorems.Thm_QECCertificates_readOff_nil
public import Theorems.Thm_QECCertificates_readOff_apply
public import Theorems.Thm_QECCertificates_readOff_eq_of_mem_spanL
public import Theorems.Thm_QECCertificates_leadIdx_le_of_ne_zero
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_leadIdx_spec
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


attribute [local simp] QECCertificates.readOff_nil

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (hD : IsEchelon D)
    {w : Vec n} (hw : w ∈ spanL (rowList D)) (hw0 : w ≠ 0) :
    ∃ ri ∈ D, ri.2 = leadIdx w hw0 := by
  have hwr : w = readOff D w := (readOff_eq_of_mem_spanL hD.1 hw).symm
  let S : Finset (PivRow n) := D.toFinset.filter (fun ri => w ri.2 ≠ 0)
  have hSne : S.Nonempty := by
    by_contra hemp
    have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hemp
    refine hw0 ?_
    rw [hwr]
    simp only [readOff]
    refine Finset.sum_eq_zero fun ri hri => ?_
    by_cases hc : w ri.2 = 0
    · rw [hc, zero_smul]
    · exfalso
      have hmemS : ri ∈ S := Finset.mem_filter.mpr ⟨hri, hc⟩
      rw [hSempty] at hmemS
      exact absurd hmemS (Finset.notMem_empty ri)
  obtain ⟨ri₀, hri₀S, hmin⟩ := Finset.exists_min_image S (fun ri => ri.2) hSne
  have hri₀D : ri₀ ∈ D := List.mem_toFinset.mp (Finset.mem_filter.mp hri₀S).1
  have hcoef : w ri₀.2 ≠ 0 := (Finset.mem_filter.mp hri₀S).2
  have hzero : ∀ i : Fin n, w i ≠ 0 → ri₀.2 ≤ i := by
    intro i hi
    by_contra hlt
    have hlt' : i < ri₀.2 := not_le.mp hlt
    refine hi ?_
    rw [hwr, readOff_apply]
    refine Finset.sum_eq_zero fun ri hri => ?_
    by_cases hc : w ri.2 = 0
    · rw [hc, zero_mul]
    · have hriS : ri ∈ S := Finset.mem_filter.mpr ⟨hri, hc⟩
      rw [hD.2 ri (List.mem_toFinset.mp hri) i
        (lt_of_lt_of_le hlt' (hmin ri hriS)), mul_zero]
  refine ⟨ri₀, hri₀D, ?_⟩
  have hlead : leadIdx w hw0 = ri₀.2 :=
    le_antisymm (leadIdx_le_of_ne_zero hw0 hcoef) (hzero (leadIdx w hw0) (leadIdx_spec w hw0))
  exact hlead.symm
end QECCertificates
