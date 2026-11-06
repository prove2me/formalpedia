-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.exists_finiteKrausCorrectable_iff_pairProductCriterion_on_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:09:25.610208+00:00
-- url     : https://prove2.me/submissions/90df58af-c096-43d7-8495-c57f14c3561f

import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Correctability
import Theorems.Thm_QEC_Coding_StabilizerCode_binaryPauliKrausFamily_sameSpaceKnillLaflammeCriterion_iff_pairProductCriterion_on_support
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_iff_exists_finiteKrausCorrectable


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.StabilizerCode
theorem _root_.solution
    {α : Type v} [Fintype α]
    (Q : SourceValidBinary ι) (E : α → Binary ι) (amp : α → Complex)
    (hcomplete : (binaryPauliKrausFamily E amp).Complete) :
    (∃ recovery : Semantics.QuantumChannel
          (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι),
      Semantics.FiniteKrausCorrectable α
        (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι)
        Q.1.code (binaryPauliKrausFamily E amp) recovery) ↔
    ∀ a b, amp a ≠ 0 → amp b ≠ 0 →
      Q.1.InGeneratedGroupUpToSign
          (binaryMul (binaryDagger (E a)) (E b)) ∨
      ¬ Q.1.InBinaryNormalizer
          (binaryMul (binaryDagger (E a)) (E b)) := by
  rw [← (binaryPauliKrausFamily E amp).sameSpaceKnillLaflammeCriterion_iff_exists_finiteKrausCorrectable
    Q.1.code hcomplete]
  exact
    binaryPauliKrausFamily_sameSpaceKnillLaflammeCriterion_iff_pairProductCriterion_on_support
      Q E amp
end QEC.Coding.StabilizerCode
