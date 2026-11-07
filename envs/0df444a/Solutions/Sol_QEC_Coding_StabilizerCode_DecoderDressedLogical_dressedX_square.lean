-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedX_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:50:31.410792+00:00
-- url     : https://prove2.me/submissions/fa113858-36a5-4bd4-a334-7866fe631e70

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedLogical_square

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
theorem _root_.solution (D : DecoderDressedLogical H) :
    D.dressedX * D.dressedX = 1 :=
  D.dressedLogical_square D.logicalX_normalizer
end QEC.Coding.StabilizerCode.DecoderDressedLogical
