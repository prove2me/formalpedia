-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaFamilyBudget.exists_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:58:15.630651+00:00
-- url     : https://prove2.me/submissions/9eff7634-58a1-40ce-a8aa-7bd20e194e5a

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaBudgetExistence
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFamilyBudget
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFamilyBudget_good_of_seed
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_WeightedGlobalArenaBudgetExistence_exists_seed
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFamilyBudget
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory
open LightWeightedGlobalControllerFactory TernaryOriginalRowMenu TernaryExtensionEncoding
open WeightedGlobalArenaSeedData WeightedGlobalArenaBudgetExistence
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
variable (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (r b K : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→ℕ→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ)
namespace ThreeSum.WeightedGlobalArenaFamilyBudget
theorem _root_.solution (n U0 : ℕ) (hℓ : ℓ≠0) (hlen : rows.length<A.J) (hp : 3≤p)
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
    (hPi : (p^(2*K))^r*current maps τ cap I A row L R O Q r K≤(9*pairFactor m F K)^r*U0)
    (hB : p^r*collisions A row L r I.nB≤9^r*n^2)
    (hC : p^r*collisions A row R r I.nC≤9^r*n^2) :
    ∃i<N, budgetGood (D maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog) p m F r K n U0 i := by
  obtain ⟨seed,hs,hp,hb,hc⟩ := WeightedGlobalArenaBudgetExistence.exists_seed maps τ cap I A ℓ hℓ row L R O Q
    rows hlen r K b n U0 hp hL hR hinjL hinjR hdet hsize1 hsize hPi hB hC
  exact good_of_seed maps τ cap U V scoreBound Q I A r b K e ℓ row L R O rows catalog n U0 seed hs hLn hRn hOn hp hb hc
end ThreeSum.WeightedGlobalArenaFamilyBudget
