-- Prove2me | solution 1 for QECCertificates.sum_mul_ite_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:57.153211+00:00
-- url     : https://prove2.me/submissions/53296e75-b54e-417f-a8af-a53a3a12c290

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
theorem _root_.solution (u : Vec n) (a : Fin n) :
    ∑ i, u i * (if i = a then (1 : ZMod 2) else 0) = u a := by
  have h := Finset.sum_eq_single (s := Finset.univ)
    (f := fun i => u i * (if i = a then (1 : ZMod 2) else 0)) a
    (fun b _ hne => by rw [if_neg (fun h => hne h), mul_zero])
    (fun hnot => absurd (Finset.mem_univ a) hnot)
  rw [h, if_pos rfl, mul_one]
end QECCertificates
