-- Prove2me | solution 1 for ThreeSum.LightPolynomialProductCheck.flag_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:14:41.797425+00:00
-- url     : https://prove2.me/submissions/1f11b45a-0dba-4a14-947b-81280fc34766

import Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient
import Definitions.Def_Submission_ThreeSum_LightPolynomialProductCheck

set_option autoImplicit false
open ThreeSum ThreeSum.LightPolynomialProductCheck
open Light
set_option maxHeartbeats 2000000
attribute [local instance] ThreeSum.LightPolynomialProductCheck._p2m_local_instance_3bb6a27167_6
namespace ThreeSum.LightPolynomialProductCheck
theorem _root_.solution (p : ℕ) (f g expected : ℕ → ℕ) (n m len : ℕ) :
    0≤flag p f g expected n m len ∧ flag p f g expected n m len≤1 := by
  unfold flag
  split_ifs <;> omega
end ThreeSum.LightPolynomialProductCheck
