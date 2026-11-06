-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.inStabilizerNormalizer_iff_commutes_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:22:07.064186+00:00
-- url     : https://prove2.me/submissions/3c575b02-521b-40ca-b6d3-2395c0b40cf6

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_binaryMul_right
import Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_binaryDagger_right

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
omit [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E : Binary ι) :
    InStabilizerNormalizer generators E ↔ ∀ j, Commutes E (generators j) := by
  constructor
  · intro h j
    exact h (generators j) (.generator j)
  · intro h S hS
    induction hS with
    | one => exact commutes_binaryOne_right E
    | generator j => exact h j
    | mul hP hQ ihP ihQ => exact commutes_binaryMul_right ihP ihQ
    | dagger hP ihP => exact commutes_binaryDagger_right ihP
end QEC.Coding.PauliSymplectic
