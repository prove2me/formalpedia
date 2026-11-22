-- Prove2me | solution 1 for QECCertificates.LRAT.even_one_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:33.65628+00:00
-- url     : https://prove2.me/submissions/b2d6998a-5fc4-4a8c-a55f-9cc966b77161

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
theorem _root_.solution (m : ℕ) : Even (1 + m) ↔ ¬ Even m := by
  rw [Nat.add_comm 1 m, Nat.even_add_one]
end QECCertificates.LRAT
