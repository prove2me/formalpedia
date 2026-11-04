-- Prove2me | solution 1 for ThreeSum.LightLocalCoverResources.word_polynomial_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:05:34.269198+00:00
-- url     : https://prove2.me/submissions/2eb7abe8-561c-4b9f-849b-d16e10a8a6d4

import Definitions.Def_Submission_ThreeSum_LightLocalCoverSetup
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Theorems.Thm_ThreeSum_LocalParameterBounds_pow_pos


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMagnitude
set_option maxHeartbeats 1800000
namespace ThreeSum.LightLocalCoverResources
theorem _root_.solution {h B : ℕ} (H : Bounds h B) :
    LightLocalCoverSetup.word h ≤ 2000*B^2 := by
  have hB := H.positive
  have hL := H.width
  have hn := H.vertices
  have hp := H.prime
  have hcap := H.cap
  have hN := H.candidates
  have hT := H.rounds
  have hP := H.decodePower
  have hmask := H.maskPower
  have hB2 : B ≤ B^2 := Nat.le_self_pow (by decide) B
  have hB2' : 1 ≤ B^2 := Nat.pow_pos (by omega)
  have hn2 : vertices h*vertices h ≤ B^2 := by
    have hh := Nat.pow_le_pow_left hn 2
    nlinarith
  have hp2 : localPrime h*localPrime h ≤ B^2 := by
    have hh := Nat.pow_le_pow_left hp 2
    nlinarith
  have hLp : (512*h+1)*localPrime h ≤ B^2 := by
    calc
      _ ≤ B*B := Nat.mul_le_mul hL (by omega)
      _ = _ := by ring
  have hdecode : LightWeightDecode.word (512*h) (localPrime h) (rows h) ≤ 20*B := by
    unfold LightWeightDecode.word LightWeightRow.word
    omega
  have hhash : LightHashHistogram.word (512*h) (localPrime h) (localPrime h) ≤ 22*B^2 := by
    unfold LightHashHistogram.word LightOneHot.word
    ring_nf at hLp hmask ⊢
    omega
  have hpair : LightPairFlags.word (512*h) (vertices h) (localPrime h) (localBucketCap h) ≤ 700*B^2 := by
    unfold LightPairFlags.word
    omega
  have hcandidate : LightLocalCoverCandidate.word (512*h) (vertices h)
      (localPrime h) (localBucketCap h) (rows h) ≤ 742*B^2 := by
    unfold LightLocalCoverCandidate.word
    omega
  have hgather : LightWeightGather.word (rows h) (scheduleSize h) (2*(512*h)) ≤ 5*B := by
    unfold LightWeightGather.word
    omega
  have hhost : LightLocalCoverHost.word h ≤ 747*B^2 := by
    unfold LightLocalCoverHost.word
    change LightLocalCoverCandidate.word (512*h) (vertices h)
      (localPrime h) (localBucketCap h) (rows h)+
      LightWeightGather.word (rows h) (scheduleSize h) (2*(512*h)) ≤ _
    omega
  have hbuild : LightLocalCoverBuild.word h ≤ 748*B^2 := by
    unfold LightLocalCoverBuild.word
    omega
  unfold LightLocalCoverSetup.word cols
  omega
end ThreeSum.LightLocalCoverResources
