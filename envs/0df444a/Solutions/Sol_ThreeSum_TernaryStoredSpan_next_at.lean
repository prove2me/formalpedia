-- Prove2me | solution 1 for ThreeSum.TernaryStoredSpan.next_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:12:25.542937+00:00
-- url     : https://prove2.me/submissions/1e3ee7c6-0318-480f-98e5-38bfc56cfecb

import Definitions.Def_Submission_ThreeSum_LightSpanCatalogTest
import Definitions.Def_Submission_ThreeSum_TernaryStoredSpan
import Theorems.Thm_Light_Ends_next


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryStoredSpan
open ThreeSum
set_option maxHeartbeats 3000000
variable {p J n : ℕ}
namespace ThreeSum.TernaryStoredSpan
theorem _root_.solution (f : ℕ → ℕ → ℕ) (row : ℕ → ℕ) (hp : 0<n) {a k : ℕ} (hk : k<n) (i : ℕ) :
    next f row p n (a*n+k) i=(f k i+a*row i)%p := by
  have hd : (a*n+k)/n=a := by
    rw [Nat.add_comm,Nat.add_mul_div_right k a hp,Nat.div_eq_of_lt hk,Nat.zero_add]
  unfold next
  rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hk,hd]
end ThreeSum.TernaryStoredSpan
