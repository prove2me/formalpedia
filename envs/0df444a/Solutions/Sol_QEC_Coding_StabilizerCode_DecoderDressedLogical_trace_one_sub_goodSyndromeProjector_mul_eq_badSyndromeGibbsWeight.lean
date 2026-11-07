-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.trace_one_sub_goodSyndromeProjector_mul_eq_badSyndromeGibbsWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:00:22.365936+00:00
-- url     : https://prove2.me/submissions/0119e7f5-3c9f-4662-afc4-42e8dbdc9bb8

import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_one_sub_goodSyndromeProjector_eq_badSyndromeProjector

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
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι))
    (rhoBeta : DensityOperator (Qubit.QubitRegister ι)) :
    LinearMap.trace Complex (Qubit.QubitRegister ι)
        ((1 - D.goodSyndromeProjector elementaryErrors) * rhoBeta.toOperator) =
      D.badSyndromeGibbsWeight elementaryErrors rhoBeta := by
  rw [D.one_sub_goodSyndromeProjector_eq_badSyndromeProjector,
    badSyndromeGibbsWeight, badSyndromeProjector, Finset.sum_mul, map_sum]
end QEC.Coding.StabilizerCode.DecoderDressedLogical
