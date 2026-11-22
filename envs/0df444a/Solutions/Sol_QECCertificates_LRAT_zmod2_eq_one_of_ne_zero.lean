-- Prove2me | solution 1 for QECCertificates.LRAT.zmod2_eq_one_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:00:30.40584+00:00
-- url     : https://prove2.me/submissions/697851be-dec9-4cec-bbdd-156e9ab10dac

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
theorem _root_.solution {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  have hv : x.val ≠ 0 := fun h0 => h ((ZMod.val_eq_zero x).mp h0)
  have hlt : x.val < 2 := ZMod.val_lt x
  have h1 : x.val = 1 := by omega
  rw [← ZMod.natCast_zmod_val x, h1]
  norm_num
end QECCertificates.LRAT
