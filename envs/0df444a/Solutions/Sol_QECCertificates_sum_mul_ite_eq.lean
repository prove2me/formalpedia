-- Prove2me | solution 1 for QECCertificates.sum_mul_ite_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:35.932609+00:00
-- url     : https://prove2.me/submissions/7b24e7c4-8e3b-407b-a1b8-1a516e6d5e5f

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (u : Vec n) (a : Fin n) (c : ZMod 2) :
    ∑ i, u i * (if a = i then c else 0) = u a * c := by
  have h := Finset.sum_eq_single (s := Finset.univ)
    (f := fun i => u i * (if a = i then c else 0)) a
    (fun b _ hne => by rw [if_neg (fun h => hne h.symm), mul_zero])
    (fun hnot => absurd (Finset.mem_univ a) hnot)
  rw [h, if_pos rfl]
end QECCertificates
