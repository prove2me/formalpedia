-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixState.final_transition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:27:05.452518+00:00
-- url     : https://prove2.me/submissions/e77d8676-2574-4048-8594-6e434cb5ff1e

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaControllerPlan
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedBudgets
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixState
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPrefixState_chosen_eq_core
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPrefixState_transition_run
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalControllerFactory_Candidate_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalControllerFactory_SpanGuard_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalControllerFactory_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixPhases_LoopPlan_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixPhases_Phase_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixStep_PrepareReady_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScoreFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.rows



set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixState
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalArenaSeedData WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixState
theorem _root_.solution (maps : Fin F→WeightedGlobalCoverGoodMaps.Weight m p)
    (τ cap U V scoreBound U' : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (j b K n U0 Rb Sb : ℕ) (e : (E×E)≃Fin N)
    (ℓ : E→ₗ[ZMod p] ZMod p) (L R O : ℕ→ℕ→ℤ)
    (catalogs : ℕ→ℕ→ℕ→ℕ) (catalog : ℕ→ℕ→ℕ) (raws : List ℤ) (words localMaps : List ℕ)
    (initial μ ζ ν : ℕ→ℤ)
    (hmem : Memory I A (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) j
      (run maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs j) catalog initial μ)
    (hL : ∀i (t : Fin (A.J+2)),0≤(p:ℤ)+L i t.val)
    (hR : ∀i (t : Fin (A.J+2)),0≤(p:ℤ)+R i t.val)
    (hO : ∀i (t : Fin (A.J+2)),0≤(p:ℤ)+O i t.val)
    (hcapacity : A.J*(p^j)*p≤I.capacity) :
    let s := run maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs j
    let Ds := fun k => data I A j b k ℓ (seedAt e k) s.row
      (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) s.rows catalog
    let f := WeightedGlobalArenaControllerCore.family maps τ cap U' Q I A Ds L R
    let ordinal := f.pick K N (p^(j+1)) (p^(j+1)) ((p^(2*K))^(j+1))
      (9^(j+1)*n^2) (9^(j+1)*n^2) (scale m j K*(9*pairFactor m F K)^(j+1)*U0)-1
    WeightedGlobalArenaControllerPlan.Final I f K Rb Sb ordinal (addr I.free I.capacity 8)
      raws words localMaps μ ζ→
    LightWeightedGlobalPrefixFinish.Committed (config p (j+1) I A 0) (p^(j+1)) (addr I.free I.capacity 8) ζ ν→
    ∃catalog', Memory I A (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) (j+1)
      (run maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs (j+1)) catalog' initial ν := by
  intro s Ds f ordinal hfinal hcommit
  rcases hfinal with ⟨ξ,⟨hkeep,houtputs⟩,hspan⟩
  have hchosen : ordinal=chosen maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs j s :=
    chosen_eq_core maps τ cap U V scoreBound U' Q I A b K n U0 j e ℓ s L R O catalog catalogs
  have ho : LightWeightedGlobalSeedScoreFull.Outputs (config p (j+1) I A ordinal) (Ds ordinal) Rb Sb raws words localMaps ξ := houtputs
  have hs : SpanDone (config p (j+1) I A ordinal) (Ds ordinal) (addr I.free I.capacity 8) ξ ζ := hspan
  unfold Ds at ho hs
  rw [hchosen] at ho hs
  exact transition_run maps τ cap U V scoreBound Q I A j b K n U0 Rb Sb e ℓ L R O catalogs catalog
    raws words localMaps initial μ ξ ζ ν hmem hkeep hL hR hO hcapacity ho hs hcommit
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixState
