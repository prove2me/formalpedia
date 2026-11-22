-- Prove2me | solution 1 for QECCertificates.LRAT.natCast_zmod2_eq_zero_iff_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:34.118612+00:00
-- url     : https://prove2.me/submissions/b9980f5c-fb33-45a3-bf9d-41bc76b0303f

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
theorem _root_.solution (c : ℕ) : ((c : ZMod 2) = 0) ↔ Even c := by
  rw [← ZMod.val_eq_zero, ZMod.val_natCast, Nat.even_iff]
end QECCertificates.LRAT
