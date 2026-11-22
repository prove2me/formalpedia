-- Prove2me | solution 1 for QECCertificates.DualWitness.not_mem_rowSpace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:25.676897+00:00
-- url     : https://prove2.me/submissions/f22672f4-7fff-4a1d-b030-2fc89b9db8fc

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Theorems.Thm_QECCertificates_not_mem_rowspace_iff_exists_mem_ker


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
namespace DualWitness
theorem _root_.solution {m : ℕ} {H : Matrix (Fin m) (Fin n) (ZMod 2)} {E : Vec n}
    (hw : DualWitness H E) : E ∉ H.certificateRowSpace :=
  (not_mem_rowspace_iff_exists_mem_ker H E).mpr ⟨hw.w, hw.mem_ker, hw.pairing⟩
end DualWitness
end QECCertificates
