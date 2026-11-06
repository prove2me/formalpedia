-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.fixed_generatedStabilizer_iff_fixed_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:09:43.445652+00:00
-- url     : https://prove2.me/submissions/bc19759f-00b4-4112-bd8e-0cc99a540bd7

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_fixed_of_generatedStabilizer

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι)
    (ψ : Semantics.Qubit.QubitRegister ι) :
    (∀ P, GeneratedStabilizer generators P → toQubitOperator P ψ = ψ) ↔
      ∀ j, toQubitOperator (generators j) ψ = ψ := by
  constructor
  · intro h j
    exact h (generators j) (.generator j)
  · intro h P hP
    exact toQubitOperator_fixed_of_generatedStabilizer generators h hP
end QEC.Coding.PauliSymplectic
