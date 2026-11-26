-- Prove2me | solution 1 for Sendov.sumEraseProd_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:52:02.625125+00:00
-- url     : https://prove2.me/submissions/89fe25e5-e9b9-41d1-8e6a-8a50bd029664

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities

set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
namespace Sendov
theorem _root_.solution : sumEraseProd 0 = 0 := by simp [sumEraseProd]
end Sendov
