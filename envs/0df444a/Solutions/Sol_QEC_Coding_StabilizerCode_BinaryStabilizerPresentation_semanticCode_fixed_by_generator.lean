-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.semanticCode_fixed_by_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:11:02.840214+00:00
-- url     : https://prove2.me/submissions/daee5da5-e80d-4ff6-89db-3a3a85160352

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
    {ψ : Semantics.Qubit.QubitRegister ι}
    (hψ : ψ ∈ P.semanticCode.carrier) (j : κ) :
    toQubitOperator (P.generators j) ψ = ψ := by
  have hgenerated : P.generators j ∈ P.code.1.generatedGroup := by
    rw [← P.generated_eq]
    exact GeneratedStabilizer.generator j
  exact (P.code.2.2 ψ).1 hψ (P.generators j) hgenerated
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
