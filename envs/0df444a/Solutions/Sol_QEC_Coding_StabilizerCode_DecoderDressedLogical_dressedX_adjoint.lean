-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedX_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:50:43.025194+00:00
-- url     : https://prove2.me/submissions/b45296b2-cf0a-4476-af38-5e98b9362271

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedLogical_adjoint

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
    LinearMap.adjoint D.dressedX = D.dressedX := by
  exact D.dressedLogical_adjoint D.logicalX_normalizer
end QEC.Coding.StabilizerCode.DecoderDressedLogical
