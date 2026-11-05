-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearPair.pairTime_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:41:55.926708+00:00
-- url     : https://prove2.me/submissions/91f48c46-975c-4333-9515-5433c412d64e

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_KernelProgram
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearSourceWords
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearPair
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightTernaryDivide_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_time_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedEulerMetadata_time_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumeration_time_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearSetup_time_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearSource_time_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessorTable_time_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessor_time_bound


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearPair
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearPair
theorem _root_.solution (N rows : ℕ) (f g : Config) :
    pairTime N rows f g≤23000*
      (N+f.L+g.L+Nat.log 2 (f.V+1)+Nat.log 2 (g.V+1)+3)^3*(rows+1) := by
  let K := N+f.L+g.L+Nat.log 2 (f.V+1)+Nat.log 2 (g.V+1)+3
  have hK : 1≤K := by omega
  have hf := LightWeightedNearSource.time_bound (N := N) (L := f.L) (rows := rows)
    (stages := 2*N-f.h) (V := f.V) (by omega)
  have hg := LightWeightedNearSource.time_bound (N := N) (L := g.L) (rows := rows)
    (stages := 2*N-g.h) (V := g.V) (by omega)
  have hfK : time N rows f≤11000*K^3*(rows+1) := by
    calc
      _≤11000*(N+f.L+Nat.log 2 (f.V+1)+3)^3*(rows+1) := hf
      _≤11000*K^3*(rows+1) := by gcongr; omega
  have hgK : time N rows g≤11000*K^3*(rows+1) := by
    calc
      _≤11000*(N+g.L+Nat.log 2 (g.V+1)+3)^3*(rows+1) := hg
      _≤11000*K^3*(rows+1) := by gcongr; omega
  have hkpow : 1≤K^3 := one_le_pow₀ hK
  have hsmall : LightTernaryProduct.time rows+1000≤1000*K^3*(rows+1) := by
    unfold LightTernaryProduct.time
    have hKthree : 3≤K := by omega
    have hpow : 3≤K^3 := hKthree.trans (le_self_pow (by omega) (by decide))
    nlinarith
  unfold pairTime
  change _≤23000*K^3*(rows+1)
  nlinarith only [hfK,hgK,hsmall]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearPair
