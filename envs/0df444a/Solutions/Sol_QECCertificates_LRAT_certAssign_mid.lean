-- Prove2me | solution 1 for QECCertificates.LRAT.certAssign_mid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:18:13.412832+00:00
-- url     : https://prove2.me/submissions/f8bd0025-2d84-4bdc-a549-968018946502

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
theorem _root_.solution {n : ℕ} (E w : Vec n) {t : ℕ} (h1 : ¬ t < n) (h2 : t < 2 * n) :
    certAssign n E w t = decide (w ⟨t - n, by omega⟩ = 1) := by
  unfold certAssign
  rw [dif_neg h1, dif_pos h2]
end QECCertificates.LRAT
