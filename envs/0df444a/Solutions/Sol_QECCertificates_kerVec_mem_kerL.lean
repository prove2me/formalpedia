-- Prove2me | solution 1 for QECCertificates.kerVec_mem_kerL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:32.806968+00:00
-- url     : https://prove2.me/submissions/3f3f3641-cde7-4dc9-b2dc-0ea72017208b

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Theorems.Thm_QECCertificates_sum_mul_ite_self
public import Theorems.Thm_QECCertificates_sum_mul_ite_eq
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_kerVec_apply
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil


attribute [local simp] QECCertificates.mem_kerL

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (hD : IsReduced D) (j : Fin n) :
    kerVec D j ∈ kerL (rowList D) := by
  rw [mem_kerL]
  intro r hr
  obtain ⟨rk, hrk, rfl⟩ := List.mem_map.mp hr
  rw [dotProduct]
  have hexp : ∀ i : Fin n, kerVec D j i
      = (if i = j then 1 else 0) + ∑ ri ∈ D.toFinset, (if ri.2 = i then ri.1 j else 0) :=
    fun i => kerVec_apply D j i
  simp only [hexp]
  simp only [mul_add]
  rw [Finset.sum_add_distrib]
  have h1 : ∑ i, rk.1 i * (if i = j then (1 : ZMod 2) else 0) = rk.1 j :=
    sum_mul_ite_self rk.1 j
  have h2 : ∑ i, rk.1 i * (∑ ri ∈ D.toFinset, (if ri.2 = i then ri.1 j else 0)) = rk.1 j := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hinner : ∀ ri ∈ D.toFinset,
        ∑ i, rk.1 i * (if ri.2 = i then ri.1 j else 0) = rk.1 ri.2 * ri.1 j :=
      fun ri _ => sum_mul_ite_eq rk.1 ri.2 (ri.1 j)
    rw [Finset.sum_congr rfl hinner]
    have hsingle : ∑ b ∈ D.toFinset, rk.1 b.2 * b.1 j = rk.1 rk.2 * rk.1 j :=
      Finset.sum_eq_single (s := D.toFinset) (f := fun b => rk.1 b.2 * b.1 j) rk
        (fun b hb hne => by
          rw [hD.2 rk hrk b (List.mem_toFinset.mp hb) (fun h => hne h.symm), zero_mul])
        (fun hnot => absurd (List.mem_toFinset.mpr hrk) hnot)
    rw [hsingle, hD.1 rk hrk, one_mul]
  rw [h1, h2]
  exact CharTwo.add_self_eq_zero (rk.1 j)
end QECCertificates
