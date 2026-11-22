-- Prove2me | solution 1 for QECCertificates.LRAT.slotVar_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:58:57.183372+00:00
-- url     : https://prove2.me/submissions/ccc40bb3-6b68-4116-9115-e92504a0450c

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {c k i j : Nat} (h1 : 1 ≤ j) (h2 : j ≤ min i (k + 1)) :
    slotVar c k i j = some (c + slotBase k i + (j - 1)) := by
  rw [slotVar, if_pos ⟨h1, h2⟩]
end QECCertificates.LRAT
