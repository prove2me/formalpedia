-- Prove2me | solution 1 for QECCertificates.LinearMap.ker_eq_spanL_kerBasis_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:35.660202+00:00
-- url     : https://prove2.me/submissions/2ebcd5a9-e542-488c-bede-0dbbb68b2ba8

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Theorems.Thm_QECCertificates_kerL_rowReduce
public import Theorems.Thm_QECCertificates_LinearMap_ker_eq_kerL_ofFn

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
namespace LinearMap
theorem _root_.solution {m : ℕ}
    (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    LinearMap.ker M.toLin' = spanL (kerBasis (rowReduce (List.ofFn fun i => M i))) := by
  rw [LinearMap.ker_eq_kerL_ofFn, kerL_rowReduce]
end LinearMap
end QECCertificates
