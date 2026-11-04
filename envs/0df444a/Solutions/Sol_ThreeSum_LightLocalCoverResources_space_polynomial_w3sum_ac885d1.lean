-- Prove2me | solution 1 for ThreeSum.LightLocalCoverResources.space_polynomial_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:05:35.64812+00:00
-- url     : https://prove2.me/submissions/f7f6a757-4cb5-444e-af3f-c0f02d88631d

import Definitions.Def_Submission_ThreeSum_LightLocalCoverSetup
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Theorems.Thm_ThreeSum_LightLocalCoverLayout_space_shift
import Theorems.Thm_ThreeSum_LocalParameterBounds_pow_pos


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMagnitude
set_option maxHeartbeats 1800000
namespace ThreeSum.LightLocalCoverResources
theorem _root_.solution {h B : ℕ} (H : Bounds h B) (base : ℕ) :
    space base h ≤ base+20*B^3 := by
  have hB := H.positive
  have hL := H.width
  have hn := H.vertices
  have hp := H.prime
  have hN := H.candidates
  have hT := H.rounds
  have hB13 : B ≤ B^3 := Nat.le_self_pow (by decide) B
  have hB12 : B ≤ B^2 := Nat.le_self_pow (by decide) B
  have hB23 := Nat.pow_le_pow_right hB (by decide : 2 ≤ 3)
  have hB2 : 1 ≤ B^2 := Nat.pow_pos (by omega)
  have hvL : vertices h*(512*h) ≤ B^2 := by
    calc
      _ ≤ B*B := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hNL : rows h*(2*(512*h)) ≤ 2*B^2 := by
    calc
      _ ≤ B*(2*B) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hNp : rows h*localPrime h ≤ B^2 := by
    calc
      _ ≤ B*B := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hp2 : cols h ≤ B^2 := by
    have hh := Nat.pow_le_pow_left hp 2
    unfold cols
    nlinarith
  have hn2 : vertices h*vertices h ≤ B^2 := by
    have hh := Nat.pow_le_pow_left hn 2
    nlinarith
  have hNp2 : rows h*cols h ≤ B^3 := by
    calc
      _ ≤ B*(B^2) := Nat.mul_le_mul (by omega) hp2
      _ = _ := by ring
  have hT2L : scheduleSize h*(2*(512*h)) ≤ 2*B^2 := by
    calc
      _ ≤ B*(2*B) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hwork : work 0 h ≤ 11*B^3 := by
    unfold work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr
    omega
  have hLp : 512*h*localPrime h ≤ B^2 := by
    calc
      _ ≤ B*B := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hlog := Nat.log_le_self 2 (512*h*localPrime h+1)
  have hmax : max (512*h+1) (Nat.log 2 (512*h*localPrime h+1)+2) ≤ 4*B^2 := by omega
  have hscratch : LightLocalCoverCandidate.space (work 0 h) (512*h) (vertices h) (localPrime h) ≤ 20*B^3 := by
    unfold LightLocalCoverCandidate.space
    omega
  have hout : scheduleMaps 0 h+scheduleSize h*(2*(512*h)) ≤ 20*B^3 := by
    unfold scheduleMaps LightCoverGreedy.total
    omega
  rw [space_shift]
  exact Nat.add_le_add_left (max_le hscratch hout) base
end ThreeSum.LightLocalCoverResources
