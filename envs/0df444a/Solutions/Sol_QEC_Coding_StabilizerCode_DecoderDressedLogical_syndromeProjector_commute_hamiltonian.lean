-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.syndromeProjector_commute_hamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:57:32.467619+00:00
-- url     : https://prove2.me/submissions/b9ca4dc3-e792-4707-8c73-4afab6531731

import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_generatorOperator_commute_syndromeProjector
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
open Semantics
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
open QEC.Coding.StabilizerCode.DecoderDressedLogical
variable {H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)}
namespace QEC.Coding.StabilizerCode.DecoderDressedLogical
theorem _root_.solution
    (D : DecoderDressedLogical H) (syndrome : DecoderSyndrome κ) :
    Commute (H.syndromeProjector syndrome) H.operator := by
  classical
  change H.syndromeProjector syndrome * H.operator =
    H.operator * H.syndromeProjector syndrome
  rw [LocalStabilizerHamiltonian.operator, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro check _
  rw [LocalStabilizerHamiltonian.term, mul_neg, neg_mul]
  exact congrArg Neg.neg
    (D.generatorOperator_commute_syndromeProjector check syndrome).eq.symm
end QEC.Coding.StabilizerCode.DecoderDressedLogical
