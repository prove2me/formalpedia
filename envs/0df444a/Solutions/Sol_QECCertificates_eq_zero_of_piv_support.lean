-- Prove2me | solution 1 for QECCertificates.eq_zero_of_piv_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:50.237288+00:00
-- url     : https://prove2.me/submissions/7867439b-1189-4f0b-bd27-234eedecc3f7

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Theorems.Thm_QECCertificates_sum_mul_ite_eq
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_eq_sum_of_piv_support
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
theorem _root_.solution {D : List (PivRow n)} (hD : IsReduced D) {z : Vec n}
    (hz : ∀ i, (∀ ri ∈ D, ri.2 ≠ i) → z i = 0) (hzker : ∀ ri ∈ D, ri.1 ⬝ᵥ z = 0) :
    z = 0 := by
  have hzsum := eq_sum_of_piv_support hD hz
  funext m
  by_cases hm : ∃ rk ∈ D, rk.2 = m
  · obtain ⟨rk, hrk, rfl⟩ := hm
    have hdot : rk.1 ⬝ᵥ z = z rk.2 := by
      rw [dotProduct]
      have step1 : ∑ i, rk.1 i * z i
          = ∑ i, rk.1 i * (∑ rl ∈ D.toFinset, (if rl.2 = i then z rl.2 else 0)) :=
        Finset.sum_congr rfl fun i _ => by rw [hzsum i]
      rw [step1]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      have hinner : ∀ rl ∈ D.toFinset,
          ∑ x, rk.1 x * (if rl.2 = x then z rl.2 else 0) = rk.1 rl.2 * z rl.2 :=
        fun rl _ => sum_mul_ite_eq rk.1 rl.2 (z rl.2)
      rw [Finset.sum_congr rfl hinner]
      have hsingle : ∑ b ∈ D.toFinset, rk.1 b.2 * z b.2 = rk.1 rk.2 * z rk.2 :=
        Finset.sum_eq_single (s := D.toFinset) (f := fun b => rk.1 b.2 * z b.2) rk
          (fun b hb hne => by
            rw [hD.2 rk hrk b (List.mem_toFinset.mp hb) (fun h => hne h.symm), zero_mul])
          (fun hnot => absurd (List.mem_toFinset.mpr hrk) hnot)
      rw [hsingle, hD.1 rk hrk, one_mul]
    rw [← hdot]
    exact hzker rk hrk
  · exact hz m (fun ri hri hcon => hm ⟨ri, hri, hcon⟩)
end QECCertificates
