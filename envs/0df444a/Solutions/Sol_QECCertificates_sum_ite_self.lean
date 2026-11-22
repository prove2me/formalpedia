-- Prove2me | solution 1 for QECCertificates.sum_ite_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:15.304653+00:00
-- url     : https://prove2.me/submissions/b3ed75a3-ee88-4bc2-b227-c98352ac80fa

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
    ∑ i, (if i = a then u i else 0) = u a := by
  have h := Finset.sum_eq_single (s := Finset.univ)
    (f := fun i => if i = a then u i else 0) a
    (fun b _ hne => by rw [if_neg (fun h => hne h)])
    (fun hnot => absurd (Finset.mem_univ a) hnot)
  rw [h, if_pos rfl]
end QECCertificates
