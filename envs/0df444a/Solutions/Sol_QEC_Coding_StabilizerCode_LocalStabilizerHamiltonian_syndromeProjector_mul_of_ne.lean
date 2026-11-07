-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.syndromeProjector_mul_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:13:32.468216+00:00
-- url     : https://prove2.me/submissions/06ce233a-d548-473c-b0aa-7fba75d85473

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_mul_of_ne
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generators_commute


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
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
theorem _root_.solution
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (left right : DecoderSyndrome κ) (hne : left ≠ right) :
    H.syndromeProjector left * H.syndromeProjector right = 0 :=
  jointStabilizerProjector_mul_of_ne
    H.generators H.generators_commute left right hne
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
