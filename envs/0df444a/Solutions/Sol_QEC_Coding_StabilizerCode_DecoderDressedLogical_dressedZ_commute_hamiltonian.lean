-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedZ_commute_hamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:59:41.627686+00:00
-- url     : https://prove2.me/submissions/3e96e5b5-9180-4f36-a329-c7f2d9a5b756

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
    Commute D.dressedZ H.operator :=
  D.dressedLogical_commute_hamiltonian D.logicalZ_normalizer
end QEC.Coding.StabilizerCode.DecoderDressedLogical
