-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.syndromeProjector_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:13:42.655308+00:00
-- url     : https://prove2.me/submissions/3d615753-4376-4c94-9759-940f88d5d32a

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
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
    (syndrome : DecoderSyndrome κ) :
    H.syndromeProjector syndrome * H.syndromeProjector syndrome =
      H.syndromeProjector syndrome :=
  jointStabilizerProjector_idempotent H.generators H.generators_commute syndrome
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
