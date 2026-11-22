-- Prove2me | solution 1 for QECCertificates.exists_dualWitness_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:22.398539+00:00
-- url     : https://prove2.me/submissions/325471fd-ca94-4849-a90a-60f99f7eb7f5

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Theorems.Thm_QECCertificates_DualWitness_not_mem_rowSpace
public import Theorems.Thm_QECCertificates_not_mem_rowspace_iff_exists_mem_ker


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) (E : Vec n) :
    (∃ _ : DualWitness H E, True) ↔ E ∉ H.certificateRowSpace := by
  constructor
  · rintro ⟨hw, -⟩; exact hw.not_mem_rowSpace
  · intro hE
    obtain ⟨w, hker, hpair⟩ := (not_mem_rowspace_iff_exists_mem_ker H E).mp hE
    exact ⟨⟨w, hker, hpair⟩, trivial⟩
end QECCertificates
