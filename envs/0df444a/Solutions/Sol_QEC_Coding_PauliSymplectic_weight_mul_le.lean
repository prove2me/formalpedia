-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.weight_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:55:39.450381+00:00
-- url     : https://prove2.me/submissions/da53876f-979c-4667-90b2-642fac8d7da1

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]

theorem solution (P Q : Binary ι) :
    weight (binaryMul P Q) ≤ weight P + weight Q := by
  unfold weight
  calc
    (support (binaryMul P Q)).card ≤ (support P ∪ support Q).card := by
      apply Finset.card_le_card
      intro i hi
      simp only [mem_support, xSupport, zSupport, mem_binarySupport, binaryMul,
        Pi.add_apply] at hi
      simp only [Finset.mem_union, mem_support, xSupport, zSupport, mem_binarySupport]
      by_cases hx : P.vector.xPart i = 0
      · by_cases hz : P.vector.zPart i = 0
        · right
          rcases hi with hi | hi
          · exact Or.inl (by simpa [hx] using hi)
          · exact Or.inr (by simpa [hz] using hi)
        · exact Or.inl (Or.inr hz)
      · exact Or.inl (Or.inl hx)
    _ ≤ (support P).card + (support Q).card := Finset.card_union_le _ _
