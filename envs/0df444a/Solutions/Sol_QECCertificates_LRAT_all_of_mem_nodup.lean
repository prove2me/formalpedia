-- Prove2me | solution 1 for QECCertificates.LRAT.all_of_mem_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:03.535876+00:00
-- url     : https://prove2.me/submissions/779254d7-3277-45ef-b7ae-4dc67cb269a1

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
theorem _root_.solution {L : List (List Nat)}
    (h : (L.all fun r => decide r.Nodup) = true) : ∀ r ∈ L, r.Nodup :=
  fun r hr => of_decide_eq_true (List.all_eq_true.mp h r hr)
end QECCertificates.LRAT
