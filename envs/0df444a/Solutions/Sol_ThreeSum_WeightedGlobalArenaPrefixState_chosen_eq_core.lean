-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixState.chosen_eq_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:38:45.217699+00:00
-- url     : https://prove2.me/submissions/cd39c447-74d8-45da-ac7e-5503ccfbb42d

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerPlan
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedBudgets
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixState
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixState
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalArenaSeedData WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
namespace ThreeSum.WeightedGlobalArenaPrefixState
theorem _root_.solution (maps : Fin F→WeightedGlobalCoverGoodMaps.Weight m p) (τ cap U V scoreBound U' : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (b K n U0 j : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p) (s : State (p := p) A)
    (L R O : ℕ→ℕ→ℤ) (catalog : ℕ→ℕ→ℕ) (catalogs : ℕ→ℕ→ℕ→ℕ) :
    (WeightedGlobalArenaControllerCore.family maps τ cap U' Q I A
      (fun k => data I A j b k ℓ (WeightedGlobalArenaFamilyBudget.seedAt e k) s.row
        (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) s.rows catalog) L R).pick
      K N (p^(j+1)) (p^(j+1)) ((p^(2*K))^(j+1)) (9^(j+1)*n^2) (9^(j+1)*n^2)
      (scale m j K*(9*pairFactor m F K)^(j+1)*U0)-1=
      chosen maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs j s := by
  unfold chosen budgetGood Family.pick
  congr 2
end ThreeSum.WeightedGlobalArenaPrefixState
