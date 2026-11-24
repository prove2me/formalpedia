-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.gdet_of_isBlockUpper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:15:49.571152+00:00
-- url     : https://prove2.me/submissions/83518f63-21d3-4bd3-8b7e-8187bbde51ad

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
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
theorem _root_.solution {a a' : ℕ} {b : GL (Fin (a + a')) k} (hb : IsBlockUpper b) {dA dD : kˣ}
    (h1 : (dA : k) = (blkA b).det) (h2 : (dD : k) = (blkD b).det) : gdet b = dA * dD := by
  refine Units.ext ?_
  rw [Units.val_mul, h1, h2, Matrix.GeneralLinearGroup.val_det_apply,
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  rw [show (b : Matrix (Fin (a + a')) (Fin (a + a')) k).submatrix finSumFinEquiv finSumFinEquiv =
    Matrix.fromBlocks (blkA b) (Matrix.of fun i j => (b : Matrix (Fin (a + a')) (Fin (a + a')) k)
      (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))) 0 (blkD b) from ?_,
    Matrix.det_fromBlocks_zero₂₁]
  ext (i | i) (j | j) <;> simp [blkA, blkD] <;> exact hb _ _
end PositivityTheory.ThK.SplitLoc.Unr
