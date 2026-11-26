-- Prove2me | solution 1 for Sendov.prod_cons_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:02:13.225198+00:00
-- url     : https://prove2.me/submissions/9a82a3fa-9857-4a68-aa30-35d721c3acbf

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities

set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
namespace Sendov
theorem _root_.solution (a : ℂ) (z : Multiset ℂ) :
    (X - C a) * (z.map (fun w => X - C w)).prod
      = ((a ::ₘ z).map (fun w => X - C w)).prod := by
  rw [Multiset.map_cons, Multiset.prod_cons]
end Sendov
