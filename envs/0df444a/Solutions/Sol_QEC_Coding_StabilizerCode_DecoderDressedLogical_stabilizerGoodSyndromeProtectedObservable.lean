-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.stabilizerGoodSyndromeProtectedObservable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:07:56.968139+00:00
-- url     : https://prove2.me/submissions/cf2fb9dc-522c-4240-b83c-7fe96adc8991

import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_isStarProjection
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_commute_dressedX
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_commute_dressedZ
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_commute_hamiltonian
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_invariant_dressedX
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_invariant_dressedZ
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_elementaryError_commutator_dressedX_mul_goodSyndromeProjector_eq_zero
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_elementaryError_commutator_dressedZ_mul_goodSyndromeProjector_eq_zero
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_trace_one_sub_goodSyndromeProjector_mul_eq_badSyndromeGibbsWeight

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
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    IsStarProjection (D.goodSyndromeProjector elementaryErrors) ∧
      Commute (D.goodSyndromeProjector elementaryErrors) D.dressedX ∧
      Commute (D.goodSyndromeProjector elementaryErrors) D.dressedZ ∧
      Commute (D.goodSyndromeProjector elementaryErrors) H.operator ∧
      D.goodSyndromeProjector elementaryErrors * D.dressedX *
          D.goodSyndromeProjector elementaryErrors =
        D.dressedX * D.goodSyndromeProjector elementaryErrors ∧
      D.goodSyndromeProjector elementaryErrors * D.dressedZ *
          D.goodSyndromeProjector elementaryErrors =
        D.dressedZ * D.goodSyndromeProjector elementaryErrors ∧
      (∀ error ∈ elementaryErrors,
        (toHermitianQubitOperator error * D.dressedX -
            D.dressedX * toHermitianQubitOperator error) *
          D.goodSyndromeProjector elementaryErrors = 0 ∧
        (toHermitianQubitOperator error * D.dressedZ -
            D.dressedZ * toHermitianQubitOperator error) *
          D.goodSyndromeProjector elementaryErrors = 0) ∧
      ∀ rhoBeta : DensityOperator (Qubit.QubitRegister ι),
        LinearMap.trace Complex (Qubit.QubitRegister ι)
            ((1 - D.goodSyndromeProjector elementaryErrors) *
              rhoBeta.toOperator) =
          D.badSyndromeGibbsWeight elementaryErrors rhoBeta := by
  refine ⟨D.goodSyndromeProjector_isStarProjection elementaryErrors,
    D.goodSyndromeProjector_commute_dressedX elementaryErrors,
    D.goodSyndromeProjector_commute_dressedZ elementaryErrors,
    D.goodSyndromeProjector_commute_hamiltonian elementaryErrors,
    D.goodSyndromeProjector_invariant_dressedX elementaryErrors,
    D.goodSyndromeProjector_invariant_dressedZ elementaryErrors, ?_, ?_⟩
  · intro error herror
    exact ⟨
      D.elementaryError_commutator_dressedX_mul_goodSyndromeProjector_eq_zero
        elementaryErrors herror,
      D.elementaryError_commutator_dressedZ_mul_goodSyndromeProjector_eq_zero
        elementaryErrors herror⟩
  · intro rhoBeta
    exact D.trace_one_sub_goodSyndromeProjector_mul_eq_badSyndromeGibbsWeight
      elementaryErrors rhoBeta
end QEC.Coding.StabilizerCode.DecoderDressedLogical
