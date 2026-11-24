-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.length_quot_prime_ne_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:05.838805+00:00
-- url     : https://prove2.me/submissions/8486d6bb-2bc0-4713-9489-42313ec99c13

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module PrimeSpectrum
open scoped Pointwise
universe u v
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (q : Ideal A) [q.IsPrime] :
    length A (A ⧸ q) ≠ ⊤ ↔ q.IsMaximal := by
  constructor
  · intro h
    haveI : IsArtinian A (A ⧸ q) :=
      (isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 h)).2
    apply Ideal.Quotient.maximal_of_isField
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : A ⧸ q)
    refine ⟨y, ?_⟩
    have hxn : (Ideal.Quotient.mk q x) ^ n ≠ 0 := pow_ne_zero _ ha
    apply mul_left_cancel₀ hxn
    rw [mul_one, ← mul_assoc, ← pow_succ]
    first
      | simpa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hy
      | (rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_pow, map_pow,
          mul_one] at hy; exact hy)
  · intro hq
    have hs : IsSimpleModule A (A ⧸ q) := isSimpleModule_iff_isCoatom.2 hq.out
    rw [Module.length_eq_one_iff.2 hs]
    first | exact ENat.one_ne_top | simp | decide
end ReciprocityTheory.ChartRestriction.G.AI
