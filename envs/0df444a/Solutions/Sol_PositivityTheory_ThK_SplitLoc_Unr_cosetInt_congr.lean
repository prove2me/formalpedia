-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.cosetInt_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:47.079831+00:00
-- url     : https://prove2.me/submissions/78be09c7-c30c-4a8c-9119-1795ed89b8ed

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_GlobalTheory_IwahoriInj_Inj_trans
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


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
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) {n : ℕ} {φ : Matrix (Fin n) (Fin n) k → ℂ} {M : ℕ}
    (hp : ∀ x y : Matrix (Fin n) (Fin n) k, (∀ i j, valuation k (y i j) ≤ valuation k (ϖ : k) ^ M) → φ (x + y) = φ x)
    {B B' : Matrix (Fin n) (Fin n) 𝒪[k]} (h : ∀ i j, (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) ^ M ∣ B i j - B' i j) :
    cosetInt φ ((algebraMap 𝒪[k] k).mapMatrix B) = cosetInt φ ((algebraMap 𝒪[k] k).mapMatrix B') := by
  refine setIntegral_congr_fun isOpen_KO.measurableSet fun w hw => ?_
  have e : (algebraMap 𝒪[k] k).mapMatrix B * w.val =
      (algebraMap 𝒪[k] k).mapMatrix B' * w.val + (algebraMap 𝒪[k] k).mapMatrix (B - B') * w.val := by
    rw [map_sub, sub_mul, add_sub_cancel]
  show φ _ = φ _
  rw [e]
  refine hp _ _ fun i j => ?_
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  have h1 := (Valuation.integer.integers (valuation k)).le_of_dvd (h i l)
  rw [map_pow, map_pow] at h1
  rw [map_mul]
  exact (mul_le_of_le_one_right' (((mem_KO_iff _).1 hw).1 l j)).trans h1
end PositivityTheory.ThK.SplitLoc.Unr
