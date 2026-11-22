-- Prove2me | solution 1 for QECCertificates.LRAT.rowOf_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:18:20.829436+00:00
-- url     : https://prove2.me/submissions/852e978f-3348-4b6f-bc6a-e7e3ce822677

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution (n : ℕ) : rowOf n (List.range n) = fun _ : Fin n => 1 := by
  funext i
  rw [rowOf, if_pos (List.mem_range.mpr i.isLt)]
end QECCertificates.LRAT
