-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ValuationBound.mul_mem_space_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:13:56.738853+00:00
-- url     : https://prove2.me/submissions/d7e34d48-b2b8-4921-8b64-b9c731574c4b

import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.FieldTheory.Finite.Valuation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_ValuationBound

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
open QEC.Coding.AlgebraicGeometry.ValuationBound
variable {k F P : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.ValuationBound
theorem _root_.solution (valuations : P → Valuation F ℤᵐ⁰) {G H : Divisor P}
    {f g : F} (hf : f ∈ space (k := k) valuations G)
    (hg : g ∈ space (k := k) valuations H) :
    f * g ∈ space (k := k) valuations (G + H) := by
  intro place
  calc
    valuations place (f * g) = valuations place f * valuations place g :=
      (valuations place).map_mul f g
    _ ≤ WithZero.exp (G place) * WithZero.exp (H place) :=
      mul_le_mul' (hf place) (hg place)
    _ = WithZero.exp (G place + H place) :=
      (WithZero.exp_add _ _).symm
    _ = WithZero.exp ((G + H) place) := by rw [Finsupp.add_apply]
end QEC.Coding.AlgebraicGeometry.ValuationBound
