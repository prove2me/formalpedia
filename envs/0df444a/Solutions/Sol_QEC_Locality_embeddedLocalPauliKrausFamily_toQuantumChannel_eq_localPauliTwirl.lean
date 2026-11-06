-- Prove2me | solution 1 for QEC.Locality.embeddedLocalPauliKrausFamily_toQuantumChannel_eq_localPauliTwirl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:09:42.006111+00:00
-- url     : https://prove2.me/submissions/db4902fd-1606-4236-9659-796973972edc

import Definitions.Def_QEC_Coding_Stabilizer_Correctability
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Theorems.Thm_QEC_Locality_quantumChannel_ext
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_toQuantumChannel_apply_sum


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Locality
open QEC Semantics Coding
open scoped TensorProduct
open PauliSymplectic
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (S : FiniteSubsystem ι) :
    (binaryPauliKrausFamily (embeddedLocalPauli S)
      (fun _ => localPauliAmplitude S)).toQuantumChannel
        (embeddedLocalPauliKrausFamily_complete S) =
      localPauliTwirl S := by
  apply quantumChannel_ext
  apply LinearMap.ext
  intro A
  unfold localPauliTwirl
  rw [FiniteKrausFamily.toQuantumChannel_apply_sum,
    FiniteKrausFamily.toQuantumChannel_apply_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hoperator :
      (binaryPauliKrausFamily (embeddedLocalPauli S)
        (fun _ => localPauliAmplitude S)).operator p =
        (localPauliFamily S).operator p :=
    congrFun (congrArg FiniteKrausFamily.operator
      (embeddedLocalPauliKrausFamily_eq_localPauliFamily S)) p
  rw [hoperator]
end QEC.Locality
