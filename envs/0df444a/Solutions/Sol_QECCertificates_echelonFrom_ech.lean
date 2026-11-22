-- Prove2me | solution 1 for QECCertificates.echelonFrom_ech
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:04.246434+00:00
-- url     : https://prove2.me/submissions/f728ce56-f85c-43ad-be10-c5d6fae30bf5

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Theorems.Thm_QECCertificates_echSelf_nil
public import Theorems.Thm_QECCertificates_echPair_nil
public import Theorems.Thm_QECCertificates_echSelf_echelonFrom_foldl

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (L : List (Vec n)) :
    EchSelf (echelonFrom L) ∧ EchPair (echelonFrom L) :=
  echSelf_echelonFrom_foldl [] L echSelf_nil echPair_nil
end QECCertificates
