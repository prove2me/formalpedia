-- Prove2me | solution 1 for ThreeSum.LightCyclic.rounded_time_fifth_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:28:51.486204+00:00
-- url     : https://prove2.me/submissions/b57469dc-c4bf-45e6-b29b-4c58339c1fe9

import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Definitions.Def_Submission_ThreeSum_LightCyclic
import Theorems.Thm_ThreeSum_LightCyclic_combinedTime_bound
import Theorems.Thm_ThreeSum_KaratsubaInterface_le_capacity
import Theorems.Thm_ThreeSum_KaratsubaInterface_rounded_time_fifth_power


set_option autoImplicit false
open ThreeSum ThreeSum.LightCyclic
open Light Karatsuba CyclicFold LightKaratsuba
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightCyclic
theorem _root_.solution {p : ℕ} (hp : 0 < p) :
    combinedTime (Nat.clog 2 p) p ^ 5 ≤
      ((2530+2*106)^5 * 2^8) * p^8 := by
  exact (Nat.pow_le_pow_left
    (combinedTime_bound _ _ (KaratsubaInterface.le_capacity p)) 5).trans
      (KaratsubaInterface.rounded_time_fifth_power hp 106)
end ThreeSum.LightCyclic
