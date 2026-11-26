-- Prove2me | solution 1 for Sendov.prod_map_mul_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:02:42.37711+00:00
-- url     : https://prove2.me/submissions/5a7cfb0b-af2e-4a61-9d54-7dfde5d420d2

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero

set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
namespace Sendov
theorem _root_.solution (b : ℂ) (s : Multiset ℂ) (f : ℂ → ℂ) :
    (s.map (fun v => b * f v)).prod = b ^ (Multiset.card s) * (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih]
    ring
end Sendov
