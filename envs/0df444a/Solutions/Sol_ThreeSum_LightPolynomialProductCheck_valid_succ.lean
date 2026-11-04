-- Prove2me | solution 1 for ThreeSum.LightPolynomialProductCheck.valid_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:14:39.329064+00:00
-- url     : https://prove2.me/submissions/70dc2964-b2b8-43c8-848c-2f65e56e85e6

import Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient
import Definitions.Def_Submission_ThreeSum_LightPolynomialProductCheck

set_option autoImplicit false
open ThreeSum ThreeSum.LightPolynomialProductCheck
open Light
set_option maxHeartbeats 2000000
attribute [local instance] ThreeSum.LightPolynomialProductCheck._p2m_local_instance_3bb6a27167_6
namespace ThreeSum.LightPolynomialProductCheck
theorem _root_.solution (p : ℕ) (f g expected : ℕ → ℕ) (n m len : ℕ) :
    Valid p f g expected n m (len+1) ↔
      Valid p f g expected n m len ∧ expected len=coefficient p f g n m len := by
  constructor
  · intro h; exact ⟨fun k hk => h k (by omega),h len (by omega)⟩
  · rintro ⟨h,he⟩ k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact h k hk
    · exact he
end ThreeSum.LightPolynomialProductCheck
