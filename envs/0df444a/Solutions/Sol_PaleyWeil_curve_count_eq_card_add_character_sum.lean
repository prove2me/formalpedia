-- Prove2me | solution 1 for PaleyWeil.curve_count_eq_card_add_character_sum
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T14:18:49.131536+00:00
-- url     : https://prove2.me/submissions/de78b18d-d40d-4810-a74e-5dfceb087535

import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial


open Polynomial Finset
open PaleyWeil

theorem solution {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (hF : ringChar F ≠ 2) (f : F[X]) :
    (Fintype.card {p : F × F // p.2 ^ 2 = f.eval p.1} : ℤ) =
      (Fintype.card F : ℤ) + ∑ x : F, quadraticChar F (f.eval x) := by
  classical
  let e : {p : F × F // p.2 ^ 2 = f.eval p.1} ≃
      Σ x : F, {y : F // y ^ 2 = f.eval x} :=
    { toFun := fun p ↦ ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
      invFun := fun p ↦ ⟨(p.1, p.2.1), p.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma, Nat.cast_sum]
  have hfiber (x : F) : (Fintype.card {y : F // y ^ 2 = f.eval x} : ℤ) =
      quadraticChar F (f.eval x) + 1 := by
    simpa only [Fintype.card_subtype, Set.toFinset_ofPred] using
      quadraticChar_card_sqrts hF (f.eval x)
  simp_rw [hfiber]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact add_comm _ _
