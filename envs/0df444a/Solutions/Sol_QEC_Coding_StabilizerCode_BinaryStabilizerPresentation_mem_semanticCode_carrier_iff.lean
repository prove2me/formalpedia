-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_semanticCode_carrier_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:11:05.261826+00:00
-- url     : https://prove2.me/submissions/abfddcd5-1273-4514-a9d5-965e815403b5

import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_Parameters

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
universe u v
open QEC.Coding.StabilizerCode
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (ψ : Semantics.Qubit.QubitRegister ι) :
    ψ ∈ P.semanticCode.carrier ↔
      ∀ G, GeneratedStabilizer P.generators G → toQubitOperator G ψ = ψ := by
  rw [semanticCode]
  constructor
  · intro hψ G hG
    apply (P.code.2.2 ψ).1 hψ G
    rw [← P.generated_eq]
    exact hG
  · intro hfixed
    apply (P.code.2.2 ψ).2
    intro G hG
    apply hfixed G
    change G ∈ generatedStabilizerSet P.generators
    rw [P.generated_eq]
    exact hG
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
