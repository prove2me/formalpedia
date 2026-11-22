-- Prove2me | solution 1 for QECCertificates.exists_ker_dot_ne_zero_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:39.018311+00:00
-- url     : https://prove2.me/submissions/92d477ca-5dc4-4759-a9a1-6bc866282b7c

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Theorems.Thm_QECCertificates_dot_eq_zero_of_mem_kerL_of_mem_spanL
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_add_same_right
public import Theorems.Thm_QECCertificates_add_reduceAgainst_mem
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
public import Theorems.Thm_QECCertificates_isReduced_rowReduce
public import Theorems.Thm_QECCertificates_kerL_eq_of_spanL_eq
public import Theorems.Thm_QECCertificates_kerVec_apply_free
public import Theorems.Thm_QECCertificates_kerVec_mem_kerL
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_readOff_nil
public import Theorems.Thm_QECCertificates_reduceAgainst_apply_piv
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
public import Theorems.Thm_QECCertificates_spanL_rowReduce
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.blockL_apply
attribute [local simp] QECCertificates.blockR_apply
attribute [local simp] QECCertificates.mem_kerL
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.readOff_nil
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2))
    {y : Vec k} (h : y ∉ spanL (matRowList M)) :
    ∃ z : Vec k, M *ᵥ z = 0 ∧ y ⬝ᵥ z ≠ 0 := by
  classical
  set D : List (PivRow k) := rowReduce (matRowList M) with hD
  set y' : Vec k := reduceAgainst D y with hy'
  have hDred : IsReduced D := by rw [hD]; exact isReduced_rowReduce _
  have hy'mem : y + y' ∈ spanL (matRowList M) := by
    rw [hy', hD, ← spanL_rowReduce (matRowList M)]
    exact add_reduceAgainst_mem _ _
  have hy'0 : y' ≠ 0 := by
    intro hzero
    exact h (by rw [hzero, add_zero] at hy'mem; exact hy'mem)
  obtain ⟨j, hj⟩ : ∃ j, y' j ≠ 0 := by
    by_contra hcon
    refine hy'0 (funext fun j => ?_)
    by_contra hc
    exact hcon ⟨j, hc⟩
  have hfree : IsFreeCol D j := by
    by_contra hnf
    have hex : ∃ ri ∈ D, ri.2 = j := by simpa [IsFreeCol] using hnf
    obtain ⟨ri, hri, hrj⟩ := hex
    have hzero := reduceAgainst_apply_piv hDred y ri hri
    rw [hrj] at hzero
    exact hj hzero
  have hker : kerVec D j ∈ kerL (matRowList M) := by
    have h1 : kerVec D j ∈ kerL (rowList D) := kerVec_mem_kerL hDred j
    have h2 : kerL (rowList D) = kerL (matRowList M) := by
      apply kerL_eq_of_spanL_eq
      rw [hD]
      exact spanL_rowReduce (matRowList M)
    rwa [h2] at h1
  refine ⟨kerVec D j, ?_, ?_⟩
  · funext i
    rw [Matrix.mulVec, dotProduct]
    exact (mem_kerL.mp hker) (fun b => M i b) (by
      rw [matRowList, List.mem_ofFn]; exact ⟨i, rfl⟩)
  · intro hzero
    have hsplit : y = y' + (y + y') := by rw [add_add_same_right]
    have hdot : y ⬝ᵥ kerVec D j
        = y' ⬝ᵥ kerVec D j + (y + y') ⬝ᵥ kerVec D j := by
      calc y ⬝ᵥ kerVec D j = (y' + (y + y')) ⬝ᵥ kerVec D j :=
            congrArg (fun u => u ⬝ᵥ kerVec D j) hsplit
        _ = y' ⬝ᵥ kerVec D j + (y + y') ⬝ᵥ kerVec D j := by rw [add_dotProduct]
    have hsecond : (y + y') ⬝ᵥ kerVec D j = 0 :=
      dot_eq_zero_of_mem_kerL_of_mem_spanL hker hy'mem
    have hfirst : y' ⬝ᵥ kerVec D j = y' j := by
      rw [dotProduct]
      refine (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin k)))
        (f := fun b => y' b * kerVec D j b) j ?_ ?_).trans ?_
      · intro b _ hb
        by_cases hbfree : IsFreeCol D b
        · rw [kerVec_apply_free hbfree, if_neg hb, mul_zero]
        · have hex : ∃ ri ∈ D, ri.2 = b := by simpa [IsFreeCol] using hbfree
          obtain ⟨ri, hri, hrb⟩ := hex
          rw [← hrb, hy', reduceAgainst_apply_piv hDred y ri hri, zero_mul]
      · intro hnot
        exact absurd (Finset.mem_univ j) hnot
      · rw [kerVec_apply_free hfree, if_pos rfl, mul_one]
    rw [hdot, hfirst, hsecond, add_zero] at hzero
    exact hj hzero
end QECCertificates
