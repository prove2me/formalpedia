-- Prove2me | solution 1 for QECCertificates.wtRec_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:45:40.569257+00:00
-- url     : https://prove2.me/submissions/dbe569f7-b8b7-4e19-8eb5-328c81fc8969

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (v : Vec (n + 1)) :
    wtRec (n + 1) v
      = wtRec n (fun i => v i.castSucc) + (if v (Fin.last n) = 0 then 0 else 1) := by
  rw [wtRec.eq_2]
end QECCertificates
