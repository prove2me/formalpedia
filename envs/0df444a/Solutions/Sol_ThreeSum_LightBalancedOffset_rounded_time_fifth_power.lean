-- Prove2me | solution 1 for ThreeSum.LightBalancedOffset.rounded_time_fifth_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:24:34.782693+00:00
-- url     : https://prove2.me/submissions/5ab05ec1-5cd6-473d-bbdf-2f545322af4a

import Definitions.Def_Submission_ThreeSum_LightCyclic
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Theorems.Thm_ThreeSum_LightBalancedOffset_time_bound
import Theorems.Thm_ThreeSum_KaratsubaInterface_le_capacity
import Theorems.Thm_ThreeSum_KaratsubaInterface_rounded_time_fifth_power
import Theorems.Thm_ThreeSum_LightCyclic_rounded_time_fifth_power
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightBalancedOffset
open Light Karatsuba CyclicFold LightKaratsuba Finset
open scoped BigOperators
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightBalancedOffset
theorem _root_.solution {p : ℕ} (hp : 0 < p) :
    time (Nat.clog 2 p) p ^ 5 ≤ ((2530+2*226)^5*2^8)*p^8 := by
  exact (Nat.pow_le_pow_left (time_bound _ _ (KaratsubaInterface.le_capacity p)) 5).trans
    (KaratsubaInterface.rounded_time_fifth_power hp 226)
end ThreeSum.LightBalancedOffset
