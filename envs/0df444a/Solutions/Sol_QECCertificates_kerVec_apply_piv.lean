-- Prove2me | solution 1 for QECCertificates.kerVec_apply_piv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:24.258136+00:00
-- url     : https://prove2.me/submissions/f14cbf10-8609-4a52-a9e5-ea14a7ae7afb

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Theorems.Thm_QECCertificates_kerVec_apply
public import Theorems.Thm_QECCertificates_IsReduced_pivot_inj


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (hD : IsReduced D) {j : Fin n} {rk : PivRow n}
    (hrk : rk ∈ D) :
    kerVec D j rk.2 = (if rk.2 = j then 1 else 0) + rk.1 j := by
  rw [kerVec_apply]
  congr 1
  have hsingle : ∑ ri ∈ D.toFinset, (if ri.2 = rk.2 then ri.1 j else 0) = rk.1 j := by
    have h := Finset.sum_eq_single (s := D.toFinset)
      (f := fun ri => if ri.2 = rk.2 then ri.1 j else 0) rk
      (fun b hb hne => by
        rw [if_neg]
        intro hcon
        exact hne (hD.pivot_inj b (List.mem_toFinset.mp hb) rk hrk hcon))
      (fun hnot => absurd (List.mem_toFinset.mpr hrk) hnot)
    rwa [if_pos rfl] at h
  exact hsingle
end QECCertificates
