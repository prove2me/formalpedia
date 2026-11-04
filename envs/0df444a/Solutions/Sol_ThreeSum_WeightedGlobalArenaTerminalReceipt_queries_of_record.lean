-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaTerminalReceipt.queries_of_record
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:26:02.128507+00:00
-- url     : https://prove2.me/submissions/d7a19ddd-3b7f-4a27-a67c-f52b20eec6ae

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhaseBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalMetadata
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPreparedMemory
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTerminalReceipt
import Theorems.Thm_ThreeSum_WeightedGlobalArenaTerminalReceipt_source_input_run
import Theorems.Thm_ThreeSum_WeightedGlobalArenaTerminalReceipt_queries_of_final
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_prepared
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_prepared
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_before
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixState_prepared
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPreparedMemory_prepared
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_KeepInputs_trans
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
attribute [local simp] ThreeSum.LightTernaryCountFrontend.prepared
attribute [local simp] ThreeSum.LightWeightedCountFrontend.prepared



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaTerminalReceipt
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalArenaSeedData WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open WeightedGlobalArenaSelectedSigned WeightedGlobalArenaSelectedTerminal WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 7000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
variable {K : ℕ}
namespace ThreeSum.WeightedGlobalArenaTerminalReceipt
theorem _root_.solution (S : WeightedGlobalArenaLoop.Setup p m F K N E) (j : ℕ) (ω : ℕ→ℤ)
    (T : WeightedGlobalArenaLoop.LastRecord S j ω)
    (hcap : 106≤S.input.capacity) (hB : S.input.nB≤S.input.capacity)
    (hC : S.input.nC≤S.input.capacity) (hO : S.input.requesterCount≤S.input.capacity)
    (hspan : S.arrays.J*(p^j)*p≤S.input.capacity)
    (hprefix : S.input.prefixFree=addr S.input.free S.input.capacity 13)
    (hbank : S.input.prefixFree+nb m (j+1)≤addr S.input.free S.input.capacity 16)
    (hpower : S.input.prefixFree+4^(WeightedGlobalArenaSourceSetup.N m (j+1))+
      (2*WeightedGlobalArenaSourceSetup.N m (j+1)+1)≤addr S.input.free S.input.capacity 16)
    (hL : ∀i (t : Fin (S.arrays.J+2)),0≤(p:ℤ)+S.L i t.val)
    (hR : ∀i (t : Fin (S.arrays.J+2)),0≤(p:ℤ)+S.R i t.val)
    (hOraw : ∀i (t : Fin (S.arrays.J+2)),0≤(p:ℤ)+S.O i t.val) :
    QueryReceipt S.maps S.threshold S.cap (j+1) S.Q
      (WeightedGlobalArenaSelectedTerminal.input S.input S.arrays (S.state (j+1)) S.L S.R S.O (j+1)) ω := by
  have hp : 1≤p := (Fact.out : p.Prime).pos
  have hold : S.arrays.J*p^j≤S.input.capacity :=
    (Nat.le_mul_of_pos_right _ hp).trans hspan
  obtain ⟨_,hcodes,hpowers,ret,hheader⟩ := WeightedGlobalArenaPreparedMemory.prepared S.input S.arrays j S.n S.U0
    S.alpha S.beta S.budgetScale S.Q _ _ _ (S.state j) T.catalog S.initial T.before T.preparedMemory
    T.prepared hprefix hcap hB hC hO hold T.oldTemplate T.oldMemory
  have hqueries := queries_of_final S.maps S.threshold S.cap K j S.Q S.input S.arrays
    (S.family j T.catalog) (S.chosen j T.catalog) T.preparedMemory T.finalMemory ω T.final T.committed
    hcap hO hspan hprefix hbank hpower hcodes hpowers ret hheader
  have heq := source_input_run S.maps S.threshold S.cap S.valueTag S.V S.scoreBound S.tagBound
    S.Q S.input S.arrays j S.featureBound K S.n S.U0 S.enumeration S.ell S.L S.R S.O
    S.catalogs T.catalog hL hR hOraw
  exact heq ▸ hqueries
end ThreeSum.WeightedGlobalArenaTerminalReceipt
