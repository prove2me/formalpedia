-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.toHermitianQubitOperator_anticommute_of_not_commutes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:13:55.589854+00:00
-- url     : https://prove2.me/submissions/96d96aaf-adef-4f5d-9375-e59f360848b8

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_anticommute_of_not_commutes


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
    (P Q : Binary ι) (h : ¬ Commutes P Q) :
    toHermitianQubitOperator P * toHermitianQubitOperator Q =
      -(toHermitianQubitOperator Q * toHermitianQubitOperator P) := by
  unfold toHermitianQubitOperator
  rw [smul_mul_smul_comm, smul_mul_smul_comm]
  rw [toQubitOperator_anticommute_of_not_commutes P Q h]
  module
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
