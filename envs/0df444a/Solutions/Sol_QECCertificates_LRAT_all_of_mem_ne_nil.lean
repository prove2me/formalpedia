-- Prove2me | solution 1 for QECCertificates.LRAT.all_of_mem_ne_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:06.501617+00:00
-- url     : https://prove2.me/submissions/860c78f3-ecdb-4b04-aec7-25c239001933

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
    (h : (L.all fun r => decide (r ≠ [])) = true) : ∀ r ∈ L, r ≠ [] :=
  fun r hr => of_decide_eq_true (List.all_eq_true.mp h r hr)
end QECCertificates.LRAT
