-- Prove2me | solution 1 for QECCertificates.LRAT.vecOf_certAssign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:18:34.469667+00:00
-- url     : https://prove2.me/submissions/855e745b-1a17-4736-aba3-f1b5104dc9cd

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
public import Theorems.Thm_QECCertificates_LRAT_zmod2_indicator
public import Theorems.Thm_QECCertificates_LRAT_certAssign_lt

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {n : ℕ} (E w : Vec n) : vecOf (certAssign n E w) n = E := by
  funext i
  rw [vecOf, certAssign_lt E w i.isLt]
  exact zmod2_indicator (E i)
end QECCertificates.LRAT
