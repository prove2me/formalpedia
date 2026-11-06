-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.support_mul_subset
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:10:42.957402+00:00
-- url     : https://prove2.me/submissions/2c6d853f-f4f6-4719-846c-053590c17076

-- ID: c644b6ca-1fad-4ccf-8c21-48401cef8730 | NAME: QEC.Coding.PauliSymplectic.support_mul_subset | 未本地编译验证
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
    support (binaryMul P Q) ⊆ support P ∪ support Q := by
  intro i hi
  simp only [Finset.mem_union, mem_support, xSupport, zSupport, mem_binarySupport,
    binaryMul, Pi.add_apply] at hi ⊢
  rcases hi with hx | hz
  · by_cases hp : P.vector.xPart i = 0
    · right; left
      intro hq
      apply hx
      simp [hp, hq]
    · left; left; exact hp
  · by_cases hp : P.vector.zPart i = 0
    · right; right
      intro hq
      apply hz
      simp [hp, hq]
    · left; right; exact hp
