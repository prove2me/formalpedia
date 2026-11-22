-- Prove2me | solution 1 for QECCertificates.kerVec_apply_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:49:01.329475+00:00
-- url     : https://prove2.me/submissions/1031105d-54d8-4d9a-be2a-a89adb3bea96

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Theorems.Thm_QECCertificates_kerVec_apply

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} {j i : Fin n} (hi : IsFreeCol D i) :
    kerVec D j i = if i = j then 1 else 0 := by
  rw [kerVec_apply]
  have hsum : ∑ ri ∈ D.toFinset, (if ri.2 = i then ri.1 j else 0) = 0 := by
    refine Finset.sum_eq_zero fun ri hri => ?_
    rw [if_neg (hi ri (List.mem_toFinset.mp hri))]
  rw [hsum, add_zero]
end QECCertificates
