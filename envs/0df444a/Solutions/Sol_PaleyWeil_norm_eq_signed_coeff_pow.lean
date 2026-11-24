-- Prove2me | solution 1 for PaleyWeil.norm_eq_signed_coeff_pow
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T17:30:40.41781+00:00
-- url     : https://prove2.me/submissions/ebe6910a-2f33-4b6a-a119-5222dc7e676e

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace IntermediateField
end IntermediateField
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial


open Polynomial IntermediateField
open PaleyWeil

theorem solution {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (x : L) :
    Algebra.norm K x =
      ((-1 : K) ^ (minpoly K x).natDegree * (minpoly K x).coeff 0) ^
        (Module.finrank K L / (minpoly K x).natDegree) := by
  have hx : IsIntegral K x := IsIntegral.of_finite K x
  have he : Module.finrank K L / (minpoly K x).natDegree =
      Module.finrank K⟮x⟯ L := by
    rw [← IntermediateField.adjoin.finrank hx, ← Module.finrank_mul_finrank K K⟮x⟯ L]
    exact Nat.mul_div_cancel_left _ (Module.finrank_pos (R := K) (M := K⟮x⟯))
  rw [he, Algebra.norm_eq_norm_adjoin K x]
  congr 1
  have hnorm := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hx)
  have hpoly : minpoly K (AdjoinSimple.gen K x) = minpoly K x := by
    rw [← minpoly.algebraMap_eq (algebraMap K⟮x⟯ L).injective]
    rfl
  simpa only [IntermediateField.adjoin.powerBasis_gen,
    IntermediateField.adjoin.powerBasis_dim, hpoly] using hnorm
