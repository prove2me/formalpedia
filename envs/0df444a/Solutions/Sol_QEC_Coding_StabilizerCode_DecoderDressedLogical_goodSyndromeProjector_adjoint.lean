-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:16:41.171908+00:00
-- url     : https://prove2.me/submissions/f32505a1-962d-4f77-8605-c56c0f422f3c

import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_syndromeProjector_adjoint
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.syndromeProjector_adjoint



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
    LinearMap.adjoint (D.goodSyndromeProjector elementaryErrors) =
      D.goodSyndromeProjector elementaryErrors := by
  classical
  rw [goodSyndromeProjector, map_sum]
  apply Finset.sum_congr rfl
  intro syndrome _
  exact H.syndromeProjector_adjoint syndrome
end QEC.Coding.StabilizerCode.DecoderDressedLogical
