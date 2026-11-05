-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSignedSelection.budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:02:41.769176+00:00
-- url     : https://prove2.me/submissions/e87b28dd-e6a9-4f85-b4df-b80e61078459

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSignedSelection
import Theorems.Thm_ThreeSum_LightTernaryMomentChannels_left_bound
import Theorems.Thm_ThreeSum_LightTernaryMomentChannels_right_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSelectedBudgets_run_budget
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSelectedSigned_left_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSelectedSigned_requester_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSelectedSigned_right_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSelectedSigned_signed_nonnegative
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSignedFeatureHash_left_injective
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSignedFeatureHash_right_injective


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSignedSelection
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedSigned WeightedGlobalArenaBudgetExistence WeightedGlobalCoverGoodMaps
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
variable (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (K n radix nA : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (X B C : ℕ→ℤ) (catalog : ℕ→ℕ→ℕ→ℕ)
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSignedSelection
theorem _root_.solution (stop : ℕ) (hstop : stop≤A.J) (hℓ : ℓ≠0) (hp : 3≤p)
    (hbase : 1<radix) (hprime : 2*radix<p) (hcap : 4*U<radix^A.J)
    (hinjB : Function.Injective (fun i : Fin I.nB => B i.val))
    (hinjC : Function.Injective (fun i : Fin I.nC => C i.val))
    (hB : ∀i<I.nB, |B i|≤(U : ℤ)) (hC : ∀i<I.nC, |C i|≤(U : ℤ))
    (hdet : (K+K).factorial*radix^(K+K)<p)
    (hsize1 : 8*(A.J+2)*p^2≤Fintype.card E)
    (hsize : 8*(A.J+2)*p^(2*(K+K))≤Fintype.card E)
    (hnB : I.nB≤n) (hnC : I.nC≤n) :
    ∀j≤stop, Budget maps τ cap Q (base I A.J nA) A K n (initialBudget A K n radix nA)
      (left U radix A.J B) (right U radix A.J C) (requester U radix A.J X) j
      (state maps τ cap U V scoreBound Q I A K n radix nA e ℓ X B C catalog j) := by
  have hbp : radix≤p := by omega
  exact run_budget maps τ cap U V scoreBound Q (base I A.J nA) A radix K n
    (initialBudget A K n radix nA) e ℓ (left U radix A.J B) (right U radix A.J C)
    (requester U radix A.J X) catalog stop hstop hℓ hp
    (fun i t => left_bound hbase B i t.val) (fun i t => right_bound hbase C i t.val)
    (fun i t => signed_nonnegative hbp (left_bound hbase B i t.val))
    (fun i t => signed_nonnegative hbp (right_bound hbase C i t.val))
    (fun i t => signed_nonnegative hbp (requester_bound hbase X i t.val))
    (WeightedGlobalSignedFeatureHash.left_injective (fun i : Fin I.nB => B i.val) hbase hprime hcap
      (fun i => hB i.val i.isLt) hinjB)
    (WeightedGlobalSignedFeatureHash.right_injective (fun i : Fin I.nC => C i.val) hbase hprime hcap
      (fun i => hC i.val i.isLt) hinjC)
    hdet hsize1 hsize hnB hnC (by rfl)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSignedSelection
