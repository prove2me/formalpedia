-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseBudget.good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:22:38.981444+00:00
-- url     : https://prove2.me/submissions/afa21efc-db96-44b8-9dfd-7ca75ce7b45f

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPhase
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSignedSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFixedParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPhaseBudget
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_TernaryActualSeedEnumeration_exists_good
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFamilyBudget_exists_good
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.rows



set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseBudget
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSeedData WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters TernaryExtensionEncoding
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseBudget
theorem _root_.solution (maps : Fin F→Weight m p) (τ cap tag : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (j b K n U0 : ℕ) (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (s : State (p := p) A) (L R O : ℕ→ℕ→ℤ) (catalog : ℕ→ℕ→ℕ)
    (hbudget : Budget maps τ cap Q I A K n U0 L R O j s)
    (hj : j<A.J) (hℓ : ℓ≠0) (hp : 3≤p)
    (hL : ∀ i (t : Fin (A.J+2)), (L i t.val).natAbs≤b)
    (hR : ∀ i (t : Fin (A.J+2)), (R i t.val).natAbs≤b)
    (hLn : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+L i t.val)
    (hRn : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+R i t.val)
    (hOn : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+O i t.val)
    (hinjL : Function.Injective (fun i : Fin I.nB => fun t : Fin (A.J+2) => (L i.val t.val : ZMod p)))
    (hinjR : Function.Injective (fun i : Fin I.nC => fun t : Fin (A.J+2) => (R i.val t.val : ZMod p)))
    (hdet : (K+K).factorial*b^(K+K)<p)
    (hsize1 : 8*(A.J+2)*p^2≤Fintype.card E) (hsize : 8*(A.J+2)*p^(2*(K+K))≤Fintype.card E) :
    ∃i<N,LightTernaryRowSelector.Good
      (WeightedGlobalArenaPhase.family maps τ cap tag Q I A j b ℓ (seedAt e) L R O s catalog).flag
      (WeightedGlobalArenaPhase.family maps τ cap tag Q I A j b ℓ (seedAt e) L R O s catalog).scoreB
      (WeightedGlobalArenaPhase.family maps τ cap tag Q I A j b ℓ (seedAt e) L R O s catalog).scoreC
      ((WeightedGlobalArenaPhase.family maps τ cap tag Q I A j b ℓ (seedAt e) L R O s catalog).scoreP K)
      (p^(j+1)) (p^(j+1)) ((p^(2*K))^(j+1)) (9^(j+1)*n^2) (9^(j+1)*n^2)
      (U0*((9*pairFactor m F K)*(2^((fixedPi m 2)*K)))^(j+1)) i := by
  have hlen : s.rows.length<A.J := by rw [hbudget.length];exact hj
  obtain ⟨i,hi,hg⟩ := exists_good maps τ cap tag (WeightedGlobalArenaSeedPrimitiveGuards.rawCap m p (j+1))
    (WeightedGlobalNativeMomentBounds.scoreBound (setup (r := j+1) maps τ cap Q I)) Q I A j b K e ℓ
    s.row L R O s.rows catalog n U0 hℓ hlen hp hL hR hLn hRn hOn hinjL hinjR hdet hsize1 hsize
    hbudget.paired hbudget.left hbudget.right
  refine ⟨i,hi,?_⟩
  rw [threshold]
  exact hg
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseBudget
