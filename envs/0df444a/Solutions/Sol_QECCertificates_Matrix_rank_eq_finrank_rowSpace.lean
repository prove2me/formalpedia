-- Prove2me | solution 1 for QECCertificates.Matrix.rank_eq_finrank_rowSpace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:27.615914+00:00
-- url     : https://prove2.me/submissions/c459f947-3ed6-4d8d-986e-6482019f3c5b

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
namespace Matrix
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    M.rank = Module.finrank (ZMod 2) M.certificateRowSpace := by
  rw [Matrix.rank_eq_finrank_span_row]
  rfl
end Matrix
end QECCertificates
