-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSeedData.candidate_score
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:14:29.262138+00:00
-- url     : https://prove2.me/submissions/5f036434-9e67-4fb8-be4c-0404aed531f3

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixStep
import Definitions.Def_Submission_ThreeSum_TernaryOriginalAppendSemantics
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedData
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedData_sourceInput_eq
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixPotential_value_eq_native
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSeedData
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory TernaryExtensionEncoding
open TernaryOriginalRowMenu
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
namespace ThreeSum.WeightedGlobalArenaSeedData
theorem _root_.solution {m F : ℕ} (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (r b k K : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→ℕ→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ)
    (hR : ∀ i : ℕ, ∀ t : Fin (A.J+2), 0≤(p : ℤ)+R i t.val)
    (hO : ∀ i : ℕ, ∀ t : Fin (A.J+2), 0≤(p : ℤ)+O i t.val)
    (hLall : ∀ i : ℕ, ∀ t : Fin (A.J+2), 0≤(p : ℤ)+L i t.val) :
    (candidate maps τ cap U V scoreBound Q I A k
      (data I A r b k ℓ seed row (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) rows catalog) L R).score K=
      (2^(((r+1)*fixedPi m 2)*K)*
        WeightedGlobalArenaPrefixPotential.value maps τ cap I (fun i t => L i t.val) (fun i t => R i t.val)
          (Function.update row r (TernaryOriginalRowMenu.row (A.J+2) ℓ seed))
          (root (Function.update row r (TernaryOriginalRowMenu.row (A.J+2) ℓ seed)) (fun i t => O i t.val)) Q (r+1) K : ℕ) := by
  change ((2 : ℤ)^((r+1)*fixedPi m 2))^K*
    (WeightedGlobalNativeTensorScore.pairedPotential
      (setup (r := r+1) maps τ cap Q (sourceInput I A k
        (data I A r b k ℓ seed row (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) rows catalog)))
      K A.J L R : ℤ)=_
  rw [sourceInput_eq I A r b k ℓ seed row _ _ _ rows catalog hLall hR hO,
    ←WeightedGlobalArenaPrefixPotential.value_eq_native]
  push_cast
  rw [←pow_mul]
end ThreeSum.WeightedGlobalArenaSeedData
