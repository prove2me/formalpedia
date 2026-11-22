-- Prove2me | solution 1 for QECCertificates.IsReduced.tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:45:52.569645+00:00
-- url     : https://prove2.me/submissions/de46bea4-ac4b-496b-b66c-1e1e14f42678

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
open _root_.Matrix
variable {n : ℕ}
namespace QECCertificates
namespace IsReduced
theorem _root_.solution {r : PivRow n} {D : List (PivRow n)} (h : IsReduced (r :: D)) :
    IsReduced D :=
  ⟨fun ri hri => h.1 ri (List.mem_cons_of_mem r hri),
   fun ri hri rj hrj hne =>
      h.2 ri (List.mem_cons_of_mem r hri) rj (List.mem_cons_of_mem r hrj) hne⟩
end IsReduced
end QECCertificates
