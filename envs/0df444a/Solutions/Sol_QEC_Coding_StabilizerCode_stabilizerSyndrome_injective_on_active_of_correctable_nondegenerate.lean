-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.stabilizerSyndrome_injective_on_active_of_correctable_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:15:38.568994+00:00
-- url     : https://prove2.me/submissions/8755901f-4b8a-4300-bb20-6cbc688255a8

import Definitions.Def_QEC_Coding_Stabilizer_Correctability
import Definitions.Def_QEC_Coding_Stabilizer_Degeneracy
import Definitions.Def_QEC_Coding_Stabilizer_SyndromeInjectivity
import Theorems.Thm_QEC_Coding_StabilizerCode_stabilizerSyndrome_injectiveUpToSign_of_correctable_nondegenerate

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.StabilizerCode
theorem _root_.solution
    {κ : Type v} [Fintype κ] {α : Type w} [Fintype α]
    (Q : SourceValidBinary ι) (generators : κ → Binary ι)
    (hgenerated : {S | GeneratedStabilizer generators S} = Q.1.generatedGroup)
    (d t : Nat) (hd : SemanticStabilizerDistance Q d)
    (hNondegenerate : ¬ SemanticallyDegenerateAtDistance Q d)
    (E : α → Binary ι) (amp : α → Complex)
    (hcomplete : (binaryPauliKrausFamily E amp).Complete)
    (hcorrectable : ∃ recovery : Semantics.QuantumChannel
          (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι),
        Semantics.FiniteKrausCorrectable α
          (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι)
          Q.1.code (binaryPauliKrausFamily E amp) recovery)
    (hweight : ∀ i, amp i ≠ 0 → weight (E i) ≤ t)
    (hradius : 2 * t < d)
    (hNoDuplicates : ∀ i j, amp i ≠ 0 → amp j ≠ 0 →
      BinaryUpToSign (E i) (E j) → i = j) :
    Function.Injective (fun i : {i // amp i ≠ 0} =>
      stabilizerSyndrome generators (E i.1)) := by
  intro i j hsyndrome
  apply Subtype.ext
  apply hNoDuplicates i.1 j.1 i.2 j.2
  exact stabilizerSyndrome_injectiveUpToSign_of_correctable_nondegenerate
    Q generators hgenerated d t hd hNondegenerate E amp hcomplete hcorrectable
      hweight hradius i.1 j.1 i.2 j.2 hsyndrome
end QEC.Coding.StabilizerCode
