-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.TransverseBudgetUse6814.cheap_dvd_thick_yukon_52e00c71af95
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-02T21:48:27.668214+00:00
-- url     : https://prove2.me/submissions/29b013c7-ffdb-47d7-8bdb-77d6ab11d058




import Definitions.Def_Yukon_82654001b76f2786fe41eaa7
set_option backward.isDefEq.respectTransparency.types false
namespace Polynomial
end Polynomial
namespace ProximityPrize.SubmissionLower.TransverseBudgetUse6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial
variable {K : Type*} [CommRing K]
theorem _root_.solution (f : K) : cheap f ∣ thick f  := by
  refine ⟨(Polynomial.X-1)*cheap f,?_⟩
  simp only [thick]
  ring
end
end TransverseBudgetUse6814
end SubmissionLower
end ProximityPrize
