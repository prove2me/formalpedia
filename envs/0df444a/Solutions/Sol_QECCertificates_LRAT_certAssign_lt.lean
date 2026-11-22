-- Prove2me | solution 1 for QECCertificates.LRAT.certAssign_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:58.338153+00:00
-- url     : https://prove2.me/submissions/c7614ecf-4012-4c3b-9c5a-c49c040e736d

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
theorem _root_.solution {n : ℕ} (E w : Vec n) {t : ℕ} (ht : t < n) :
    certAssign n E w t = decide (E ⟨t, ht⟩ = 1) := by
  unfold certAssign
  rw [dif_pos ht]
end QECCertificates.LRAT
