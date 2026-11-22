-- Prove2me | solution 1 for QECCertificates.mem_kerL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:45:30.007138+00:00
-- url     : https://prove2.me/submissions/3877d63b-1c25-4077-a500-41b96fbd6760

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
theorem _root_.solution {L : List (Vec n)} {x : Vec n} :
    x ∈ kerL L ↔ ∀ r ∈ L, r ⬝ᵥ x = 0 := Iff.rfl
end QECCertificates
