-- Prove2me | solution 1 for ThreeSum.ModuloCosts.roundedPower_fifth_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:48:35.293798+00:00
-- url     : https://prove2.me/submissions/68234b24-9369-47b9-8953-b2b9e1129cfc

import Definitions.Def_Submission_ThreeSum_ModuloRuntime
import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Definitions.Def_Submission_ThreeSum_ModuloCosts
import Definitions.Def_WeightedCache3SUM_Alias_44fe933b0cad9ef5


set_option autoImplicit false
open ThreeSum ThreeSum.ModuloCosts
open KaratsubaInterface
namespace ThreeSum.ModuloCosts
theorem _root_.solution {p : ℕ} (hp : 0 < p) :
    roundedPower p ^ 5 ≤ 2^8*p^8 := by
  have ht : (3 : ℕ)^5 ≤ 2^8 := by norm_num
  calc
    _ = ((3 : ℕ)^5)^(Nat.clog 2 p) := by
      unfold roundedPower
      rw [← pow_mul, Nat.mul_comm (Nat.clog 2 p) 5, pow_mul]
    _ ≤ ((2 : ℕ)^8)^(Nat.clog 2 p) := Nat.pow_le_pow_left ht _
    _ = capacity p ^ 8 := by
      unfold capacity
      rw [← pow_mul, Nat.mul_comm 8 (Nat.clog 2 p), pow_mul]
    _ ≤ (2*p)^8 := Nat.pow_le_pow_left (capacity_lt_twice hp).le _
    _ = _ := by rw [mul_pow]
end ThreeSum.ModuloCosts
