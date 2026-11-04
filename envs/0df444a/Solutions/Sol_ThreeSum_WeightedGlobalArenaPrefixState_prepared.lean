-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixState.prepared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:39:08.623789+00:00
-- url     : https://prove2.me/submissions/e7f12c29-71e6-4bcd-a3df-0945b5bab2c2

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerPlan
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedBudgets
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixState
import Theorems.Thm_Light_SegN_read
import Theorems.Thm_ThreeSum_LightBalancedOffset_offset_lt
import Theorems.Thm_ThreeSum_SourceBucketView_read
import Theorems.Thm_ThreeSum_TernarySignedLayout_offset_lt
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_offset_lt
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_KeepInputs_trans
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalPrefixSeedHeader_prepared_kept_regions


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixState
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalArenaSeedData WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
namespace ThreeSum.WeightedGlobalArenaPrefixState
theorem _root_.solution (I : Input) (A : Inputs) (L R O : ℕ→Fin (A.J+2)→ℤ)
    (j : ℕ) (s : State (p := p) A) (catalog : ℕ→ℕ→ℕ) (initial μ ν : ℕ→ℤ)
    (X : LightWeightedGlobalPrefixStep.Inputs) (H : LightWeightedGlobalPrefixStep.Prepared X μ ν)
    (hhost : X.liveHeader=addr I.free I.capacity 1)
    (hseed : X.seed=addr I.free I.capacity 3)
    (hprefix : X.prefixFree=addr I.free I.capacity 13)
    (hcap : 106≤I.capacity) (hB : I.nB≤I.capacity) (hC : I.nC≤I.capacity)
    (hO : I.requesterCount≤I.capacity) (hSpan : A.J*p^j≤I.capacity)
    (hmem : Memory I A L R O j s catalog initial μ) : Memory I A L R O j s catalog initial ν := by
  have hlow (x : ℕ) (hx : x<I.free) : ν x=μ x :=
    WeightedGlobalPrefixSeedHeader.prepared_kept_regions H x
      (by rw [hprefix];unfold addr;omega)
      (Or.inl (by rw [hhost];unfold addr;omega))
      (Or.inl (by rw [hseed];unfold addr;omega))
  have hregions (x : ℕ) (hx : addr I.free I.capacity 4≤x) (hy : x<addr I.free I.capacity 8) : ν x=μ x :=
    WeightedGlobalPrefixSeedHeader.prepared_kept_regions H x
      (by rw [hprefix];unfold addr at *;omega)
      (Or.inr (by rw [hhost];unfold addr at *;omega))
      (Or.inr (by rw [hseed];unfold addr at *;omega))
  have hkeys (slot count : ℕ) (hs : 4≤slot ∧ slot<7) (hc : count≤I.capacity) (i : ℕ) (hi : i<count) :
      ν (addr I.free I.capacity slot+i)=μ (addr I.free I.capacity slot+i) := by
    apply hregions
    · unfold addr
      have hh := Nat.mul_le_mul_right I.capacity hs.1
      omega
    · have hh := offset_lt (free := I.free) (C := I.capacity) (slot := slot) hi hc
      unfold addr at *
      have hm := Nat.mul_le_mul_right I.capacity (show slot+1≤8 by omega)
      omega
  refine ⟨?_,?_,?_,?_,hmem.represents,hmem.bounded,?_⟩
  · intro x hx
    exact (hlow x hx).trans (hmem.immutable x hx)
  · intro i hi
    exact (hkeys 4 I.nB (by omega) hB i hi).trans (hmem.B i hi)
  · intro i hi
    exact (hkeys 5 I.nC (by omega) hC i hi).trans (hmem.Cvalues i hi)
  · intro i hi
    exact (hkeys 6 I.requesterCount (by omega) hO i hi).trans (hmem.Ovalues i hi)
  · intro q hq i hi
    have hindex : A.J*q+i<A.J*p^j := by nlinarith
    have htop := offset_lt (free := I.free) (C := I.capacity) (slot := 7) hindex hSpan
    rw [←Nat.add_assoc] at htop
    exact (hregions _ (by unfold addr;omega) htop).trans (hmem.read q hq i hi)
end ThreeSum.WeightedGlobalArenaPrefixState
