-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.elementaryError_commutator_dressedX_mul_goodSyndromeProjector_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:09:01.096581+00:00
-- url     : https://prove2.me/submissions/07a52d99-6413-42f1-9106-2d7e4fda10a2

import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_elementaryError_commutator_dressedLogical_mul_goodSyndromeProjector_eq_zero

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
    (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι))
    {error : Binary ι} (herror : error ∈ elementaryErrors) :
    (toHermitianQubitOperator error * D.dressedX -
        D.dressedX * toHermitianQubitOperator error) *
      D.goodSyndromeProjector elementaryErrors = 0 :=
  D.elementaryError_commutator_dressedLogical_mul_goodSyndromeProjector_eq_zero
    elementaryErrors herror D.logicalX_normalizer
end QEC.Coding.StabilizerCode.DecoderDressedLogical
