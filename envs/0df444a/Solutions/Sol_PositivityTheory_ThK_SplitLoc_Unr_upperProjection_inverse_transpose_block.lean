-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.upperProjection_inverse_transpose_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:21:19.851603+00:00
-- url     : https://prove2.me/submissions/1f483626-abfd-4471-bc94-51a319763030

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_invT_mul_transpose
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_transpose_mul_invT
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {a a' : ℕ} {b : GL (Fin (a + a')) k} (hb : IsBlockUpper b) {dA : kˣ}
    (h1 : (dA : k) = (blkA b).det) :
    (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT b).val : Matrix (Fin a) (Fin (a + a')) k) =
      (invT (blkAGL b dA h1)).val * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) := by
  have key : ((blkAGL b dA h1).val)ᵀ * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) =
      X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * b.valᵀ := by
    ext i j
    obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j
    · simp [X0, Matrix.mul_apply, blkAGL, blkA, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]
    · simp [X0, Matrix.mul_apply, blkAGL, blkA, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]
      exact (hb j i).symm
  calc (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT b).val : Matrix (Fin a) (Fin (a + a')) k)
      = (invT (blkAGL b dA h1)).val * (((blkAGL b dA h1).val)ᵀ * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a'))) * (invT b).val := by
        rw [← Matrix.mul_assoc (invT (blkAGL b dA h1)).val, invT_mul_transpose, Matrix.one_mul]
    _ = (invT (blkAGL b dA h1)).val * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) := by
        rw [key, Matrix.mul_assoc, Matrix.mul_assoc, transpose_mul_invT, Matrix.mul_one]
end PositivityTheory.ThK.SplitLoc.Unr
