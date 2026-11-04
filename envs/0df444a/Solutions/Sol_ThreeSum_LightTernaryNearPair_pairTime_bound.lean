-- Prove2me | solution 1 for ThreeSum.LightTernaryNearPair.pairTime_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:09:44.910198+00:00
-- url     : https://prove2.me/submissions/cb7ba4e1-2b1f-499b-b23d-06df76e8771b

import Definitions.Def_Submission_ThreeSum_LightTernaryNearSourceWords
import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryDivide_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryNearSource_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryNearPair
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
namespace ThreeSum.LightTernaryNearPair
theorem _root_.solution (N rows : ℕ) (f g : Config) :
    pairTime N rows f g≤23000*
      (N+f.L+g.L+Nat.log 2 (f.V+1)+Nat.log 2 (g.V+1)+3)^3*(rows+1) := by
  let K := N+f.L+g.L+Nat.log 2 (f.V+1)+Nat.log 2 (g.V+1)+3
  have hK : 1≤K := by omega
  have hf := LightTernaryNearSource.time_bound (N := N) (L := f.L) (rows := rows)
    (stages := 2*N-f.T) (V := f.V) (by omega)
  have hg := LightTernaryNearSource.time_bound (N := N) (L := g.L) (rows := rows)
    (stages := 2*N-g.T) (V := g.V) (by omega)
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
end ThreeSum.LightTernaryNearPair
