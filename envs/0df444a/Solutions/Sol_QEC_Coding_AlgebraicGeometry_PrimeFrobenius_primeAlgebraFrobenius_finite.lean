-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.PrimeFrobenius.primeAlgebraFrobenius_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:55:51.373645+00:00
-- url     : https://prove2.me/submissions/f1895db6-fd3a-4214-af42-7b4bec5b6873

import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeFrobenius_primeAlgebraFrobenius_comp_base
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeFrobenius_primeAlgebraFrobenius_integral

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.PrimeFrobenius
noncomputable section
variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [Algebra (ZMod p) R]
namespace QEC.Coding.AlgebraicGeometry.PrimeFrobenius
theorem _root_.solution [Algebra.FiniteType (ZMod p) R] :
    (primeAlgebraFrobenius p R).Finite := by
  have hb : (algebraMap (ZMod p) R).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  have hc : ((primeAlgebraFrobenius p R).comp (algebraMap (ZMod p) R)).FiniteType := by
    rw [primeAlgebraFrobenius_comp_base]
    exact hb
  exact RingHom.finite_iff_isIntegral_and_finiteType.mpr
    ⟨primeAlgebraFrobenius_integral p R, RingHom.FiniteType.of_comp_finiteType hc⟩
end QEC.Coding.AlgebraicGeometry.PrimeFrobenius
