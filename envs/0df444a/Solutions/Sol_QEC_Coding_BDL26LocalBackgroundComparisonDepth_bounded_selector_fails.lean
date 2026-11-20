-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonDepth.bounded_selector_fails
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T15:42:04.310804+00:00
-- url     : https://prove2.me/submissions/8a31a788-02ae-427d-a529-20311dfab0cf

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonDepth_fixed_scale_no_bounded_response
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonDepth_restriction_weight_le_card
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonDepth
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open BDL26LocalBackgroundComparisonResponse
open scoped Classical BigOperators
namespace QEC.Coding.BDL26LocalBackgroundComparisonDepth
theorem _root_.solution (S : OddScale) (large : 33 ≤ S.ell) (B : Nat)
    (response : ∀ n : Nat, W S n → Q S n → Finset (Q S n))
    (bounded : ∀ (n : Nat) (g : W S n) (q : Q S n), (response n g q).card ≤ B) :
    ∃ (g : W S (budgetDepth B)) (q : Q S (budgetDepth B)),
      B < HammingWeight g ∧ g ≠ 0 ∧
      canonicalBasisWord (F:=BDL26Field) q ≠ (0 : W S (budgetDepth B)) ∧
      BDL26AllDepthBottomComparisonStability.residual S (budgetDepth B)
        (perturbTop S (budgetDepth B)
          (BDL26NonzeroBackgroundComparisonStability.zeroInput S (budgetDepth B)) g)
        (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S (budgetDepth B) ∧
      BDL26AllDepthBottomComparisonStability.residual S (budgetDepth B)
        (perturbTop S (budgetDepth B)
          (BDL26NonzeroBackgroundComparisonStability.zeroInput S (budgetDepth B)) g)
        (canonicalBasisWord (F:=BDL26Field) q)-
      BDL26AllDepthBottomComparisonStability.residual S (budgetDepth B)
        (perturbTop S (budgetDepth B)
          (BDL26NonzeroBackgroundComparisonStability.zeroInput S (budgetDepth B))
          (backgroundRestriction S (budgetDepth B) g (response (budgetDepth B) g q)))
        (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S (budgetDepth B) := by
  obtain ⟨P,q,hP,hq,hn,heavy,nonzero,flip,bad,exclude⟩ :=
    fixed_scale_no_bounded_response S large B
  let g := backgroundRestriction S (budgetDepth B) (logicalError S (budgetDepth B)) P
  refine ⟨g,q,heavy,nonzero,flip,bad,?_⟩
  exact exclude (response (budgetDepth B) g q)
    ((restriction_weight_le_card S (budgetDepth B) g _).trans (bounded (budgetDepth B) g q))
end QEC.Coding.BDL26LocalBackgroundComparisonDepth
