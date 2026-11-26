-- Prove2me | solution 1 for P2M_FourierJacobi_Algebra_special_negative_d__9d3a998530fe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:05.687866+00:00
-- url     : https://prove2.me/submissions/28d1fd16-0fbf-4b79-a150-b7c71e6e5d48

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_FourierJacobi_Algebra_EulerFactors

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
namespace FourierJacobi.Algebra
theorem _root_.solution (t a b : K) :
    d₁ t a b (-t) = fourFactors a b (-t ^ 2) := by
  unfold d₁
  congr 1
  ring
end FourierJacobi.Algebra
