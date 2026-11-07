-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedX_commute_hamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:07:52.550293+00:00
-- url     : https://prove2.me/submissions/fa95f8be-50e2-47a3-a87c-94d7921b28b9

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedLogical_commute_hamiltonian

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
    Commute D.dressedX H.operator :=
  D.dressedLogical_commute_hamiltonian D.logicalX_normalizer
end QEC.Coding.StabilizerCode.DecoderDressedLogical
