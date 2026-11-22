-- Prove2me | solution 1 for QECCertificates.echSelf_echelonFrom_foldl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:28.39257+00:00
-- url     : https://prove2.me/submissions/f257fa93-a7cd-43c8-912d-a6ca1d7856c9

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Theorems.Thm_QECCertificates_EchSelf_stepA
public import Theorems.Thm_QECCertificates_EchPair_stepA

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (D : List (PivRow n)) (L : List (Vec n))
    (h1 : EchSelf D) (h2 : EchPair D) :
    EchSelf (L.foldl stepA D) ∧ EchPair (L.foldl stepA D) := by
  induction L generalizing D with
  | nil => exact ⟨h1, h2⟩
  | cons v rest ih =>
      rw [List.foldl_cons]
      exact ih (stepA D v) (EchSelf_stepA h1 v) (EchPair_stepA h1 h2 v)
end QECCertificates
