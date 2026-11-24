-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.int_of_mem_coset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:15:34.745412+00:00
-- url     : https://prove2.me/submissions/6f7bdf1b-4177-4e57-852a-997e8e4cf903

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
open GlobalTheory.SatakeBound
omit [MeasurableSpace k] [BorelSpace k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {p : 𝒪[k]} (hp : Irreducible p) {n : ℕ} {a : Fin n → ℕ} {c : HermIdx p a} {g : GL (Fin n) k}
    (hg : (hermGL hp a c)⁻¹ * g ∈ KO k (Fin n)) (i j : Fin n) : g.val i j ∈ 𝒪[k] := by
  rw [← mul_inv_cancel_left (hermGL hp a c) g, Units.val_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => mul_mem (hermMat p a c i l).2 (((mem_KO_iff _).1 hg).1 _ _)
end PositivityTheory.ThK.SplitLoc.Unr
