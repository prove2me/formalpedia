-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSelectedTerminal.native_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:47:03.757412+00:00
-- url     : https://prove2.me/submissions/ec27f6c2-a9b9-448b-a725-1b5c862ed0f1

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedBudgets
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCompactSupport
import Definitions.Def_Submission_Weighted_Global_TernaryPairedBudgetCollision
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedTerminal
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_TernaryPairedBudgetSelector_terminal_zero
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixPotential_value_eq_native
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectedTerminal
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSeedData
open WeightedGlobalArenaBudgetExistence WeightedGlobalArenaSelectedBudgets
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (K n U0 : ℕ) (L R O : ℕ→ℕ→ℤ) (r : ℕ) (s : State (p := p) A)
namespace ThreeSum.WeightedGlobalArenaSelectedTerminal
theorem _root_.solution (M C : ℕ)
    (hbudget : Budget maps τ cap Q I A K n U0 L R O r s)
    (hb : 0<9*pairFactor m F K)
    (hdrift : (9*pairFactor m F K)^4*M^(4*K+3)≤(p^(2*K))^4)
    (hcover : n^2≤M^r) (hinit : U0^4≤C*n^(8*K+5)) (hn : C<n) :
    WeightedGlobalNativeTensorScore.pairedPotential
      (setup (r := r) maps τ cap Q (input I A s L R O r)) K A.J L R=0 := by
  have hz := TernaryPairedBudgetSelector.terminal_zero K M (p^(2*K)) (9*pairFactor m F K)
    U0 (current maps τ cap I A s.row L R O Q r K) r n C hb hbudget.paired hdrift hcover hinit hn
  have he := WeightedGlobalArenaPrefixPotential.value_eq_native maps τ cap I L R s.row
    (root s.row (fun i t => O i t.val)) Q r K
  exact he.symm.trans hz
end ThreeSum.WeightedGlobalArenaSelectedTerminal
