-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Divisor.mem_support_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:08:40.358167+00:00
-- url     : https://prove2.me/submissions/2cd3a113-0ee3-47f5-b26d-699b297f15eb

import Mathlib.Data.Finsupp.Weight
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators
open QEC.Coding.AlgebraicGeometry.Divisor
variable {P : Type*}
namespace QEC.Coding.AlgebraicGeometry.Divisor
theorem _root_.solution {D : Divisor P} {place : P} :
    place ∈ support D ↔ D place ≠ 0 :=
  by simpa only [support] using
    (Finsupp.mem_support_iff : place ∈ D.support ↔ D place ≠ 0)
end QEC.Coding.AlgebraicGeometry.Divisor
