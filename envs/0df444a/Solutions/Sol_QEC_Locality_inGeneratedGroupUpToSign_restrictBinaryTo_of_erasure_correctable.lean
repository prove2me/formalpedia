-- Prove2me | solution 1 for QEC.Locality.inGeneratedGroupUpToSign_restrictBinaryTo_of_erasure_correctable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:14:38.077649+00:00
-- url     : https://prove2.me/submissions/4bfe9d8b-259e-42ac-8e99-6b2a0d0fcb5d

import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Theorems.Thm_QEC_Locality_restrictBinaryTo_eq_embeddedLocalPauli
import Theorems.Thm_QEC_Coding_StabilizerCode_inGeneratedGroupUpToSign_of_detectableOn_of_inBinaryNormalizer
import Theorems.Thm_QEC_Locality_detectableOn_embeddedLocalPauli_of_erasureCorrectableFromRegister


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
    (S : FiniteSubsystem ι)
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι))
    (hRecovery : Correctable (Qubit.QubitRegister ι) S.complementSystem P.semanticCode
      S.erasureChannelFromRegister recovery)
    (E : Binary ι) (hNormalizer : P.code.1.InBinaryNormalizer (restrictBinaryTo S.selected E)) :
    P.code.1.InGeneratedGroupUpToSign (restrictBinaryTo S.selected E) := by
  apply StabilizerCode.inGeneratedGroupUpToSign_of_detectableOn_of_inBinaryNormalizer
    P.code (restrictBinaryTo S.selected E) hNormalizer
  rw [restrictBinaryTo_eq_embeddedLocalPauli]
  exact detectableOn_embeddedLocalPauli_of_erasureCorrectableFromRegister
    S P.semanticCode recovery hRecovery (localIndexOfBinary S E)
end QEC.Locality
