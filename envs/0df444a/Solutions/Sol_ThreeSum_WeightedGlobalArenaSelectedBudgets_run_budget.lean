-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSelectedBudgets.run_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:34:55.73279+00:00
-- url     : https://prove2.me/submissions/5978f485-6063-493c-8b44-12134072e0e2

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFamilyBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixInitial
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedBudgets
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedBudgets_step_budget
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedBudgets_initial_budget
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_Candidate_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_SpanGuard_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_Ready_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFamilyBudget_exists_good
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectedBudgets
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSeedData
open WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
variable (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (b K n U0 : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→ℕ→ℤ) (catalog : ℕ→ℕ→ℕ→ℕ)
namespace ThreeSum.WeightedGlobalArenaSelectedBudgets
theorem _root_.solution (stop : ℕ) (hstop : stop≤A.J) (hℓ : ℓ≠0) (hp : 3≤p)
    (hL : ∀ i (t : Fin (A.J+2)), (L i t.val).natAbs≤b)
    (hR : ∀ i (t : Fin (A.J+2)), (R i t.val).natAbs≤b)
    (hLn : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+L i t.val)
    (hRn : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+R i t.val)
    (hOn : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+O i t.val)
    (hinjL : Function.Injective (fun i : Fin I.nB => fun t : Fin (A.J+2) => (L i.val t.val : ZMod p)))
    (hinjR : Function.Injective (fun i : Fin I.nC => fun t : Fin (A.J+2) => (R i.val t.val : ZMod p)))
    (hdet : (K+K).factorial*b^(K+K)<p)
    (hsize1 : 8*(A.J+2)*p^2≤Fintype.card E)
    (hsize : 8*(A.J+2)*p^(2*(K+K))≤Fintype.card E)
    (hB : I.nB≤n) (hC : I.nC≤n)
    (hU : I.requesterCount*n^(2*K)*(A.J+2)^(2*K)*((2*K).factorial*b^(2*K))^2≤U0) :
    ∀j≤stop, Budget maps τ cap Q I A K n U0 L R O j
      (run maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalog j) := by
  intro j
  induction j with
  | zero =>
    intro hj
    exact initial_budget maps τ cap Q I A b K n U0 L R O hL hR hB hC hU
  | succ j ih =>
    intro hj
    have hh := ih (by omega)
    let s := run maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalog j
    have hlength : s.rows.length=j := hh.length
    have hlen : s.rows.length<A.J := by omega
    have hex := exists_good maps τ cap U V scoreBound Q I A j b K e ℓ s.row L R O s.rows
      (catalog j) n U0 hℓ hlen hp hL hR hLn hRn hOn hinjL hinjR hdet hsize1 hsize
      hh.paired hh.left hh.right
    exact step_budget maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalog j s hex hLn hRn hOn hh.length
end ThreeSum.WeightedGlobalArenaSelectedBudgets
