-- Prove2me | solution 1 for QECCertificates.LRAT.mem_rowClauses
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:43.664504+00:00
-- url     : https://prove2.me/submissions/8e7b72bd-90c2-472d-b5c7-e057b1f9ad6f

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {s : Nat → Nat → Option Nat} {k i j x : Nat} {C : Clause}
    (h1 : 1 ≤ j) (h2 : j ≤ min i (k + 1)) (hC : C ∈ slotClauses s i j x) :
    C ∈ rowClauses s k i x := by
  refine List.mem_flatMap.mpr ⟨j - 1, List.mem_range.mpr (by omega), ?_⟩
  have : j - 1 + 1 = j := by omega
  rwa [this]
end QECCertificates.LRAT
