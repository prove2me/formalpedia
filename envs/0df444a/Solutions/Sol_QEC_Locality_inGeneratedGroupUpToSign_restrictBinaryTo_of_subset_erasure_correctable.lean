-- Prove2me | solution 1 for QEC.Locality.inGeneratedGroupUpToSign_restrictBinaryTo_of_subset_erasure_correctable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:21:14.785656+00:00
-- url     : https://prove2.me/submissions/1074fb35-1055-4812-9c6b-6de5a9f85b9b

import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Theorems.Thm_QEC_Locality_restrictBinaryTo_restrictBinaryTo_vector_of_subset
import Theorems.Thm_QEC_Locality_inGeneratedGroupUpToSign_restrictBinaryTo_of_erasure_correctable
import Theorems.Thm_QEC_Coding_StabilizerCode_vector_mem_generatedVectorSubspace_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_vector_mem_orthogonal_iff_inBinaryNormalizer


set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open PauliSymplectic
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (S : FiniteSubsystem ι) (R : Finset ι) (hRS : R ⊆ S.selected)
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι))
    (hRecovery : Correctable (Qubit.QubitRegister ι) S.complementSystem P.semanticCode
      S.erasureChannelFromRegister recovery)
    (E : Binary ι) (hNormalizer : P.code.1.InBinaryNormalizer (restrictBinaryTo R E)) :
    P.code.1.InGeneratedGroupUpToSign (restrictBinaryTo R E) := by
  have hNormalizerS :
      P.code.1.InBinaryNormalizer (restrictBinaryTo S.selected (restrictBinaryTo R E)) := by
    apply (StabilizerCode.vector_mem_orthogonal_iff_inBinaryNormalizer P.code.1 _).1
    rw [restrictBinaryTo_restrictBinaryTo_vector_of_subset R S.selected hRS E]
    exact (StabilizerCode.vector_mem_orthogonal_iff_inBinaryNormalizer P.code.1 _).2
      hNormalizer
  have hGeneratedS :=
    inGeneratedGroupUpToSign_restrictBinaryTo_of_erasure_correctable
      P S recovery hRecovery (restrictBinaryTo R E) hNormalizerS
  apply (StabilizerCode.vector_mem_generatedVectorSubspace_iff P.code.1 _).1
  rw [← restrictBinaryTo_restrictBinaryTo_vector_of_subset R S.selected hRS E]
  exact (StabilizerCode.vector_mem_generatedVectorSubspace_iff P.code.1 _).2 hGeneratedS
end QEC.Locality
