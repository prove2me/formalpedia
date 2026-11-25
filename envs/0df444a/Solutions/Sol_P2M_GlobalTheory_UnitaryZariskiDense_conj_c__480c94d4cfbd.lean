-- Prove2me | solution 1 for P2M_GlobalTheory_UnitaryZariskiDense_conj_c__480c94d4cfbd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:39.583221+00:00
-- url     : https://prove2.me/submissions/5f1a3e53-55d1-45fd-a621-0038de8c68b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Classical MvPolynomial
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.UnitaryZariskiDense
variable {ι : Type} {a : ℕ}
namespace GlobalTheory.UnitaryZariskiDense
theorem _root_.solution : (starRingEnd ℂ) cα = -cβ := by
  apply Complex.ext <;> simp [cα, cβ] <;> norm_num
end GlobalTheory.UnitaryZariskiDense
