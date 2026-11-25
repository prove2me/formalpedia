-- Prove2me | solution 1 for PaleyWeil.paley_sign_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-25T06:47:54.71175+00:00
-- url     : https://prove2.me/submissions/050cde3a-c41d-41b0-81e1-55e3f5a6a8ac

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659CharacterBounds
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659Histogram
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659LowMoments
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial

section


open Finset

namespace PaleyWeil

noncomputable section















@[simp] theorem paleySign_self (a : PaleyField) : paleySign a a = 0 := by
  simp [paleySign]



theorem paleySign_dichotomy (a x : PaleyField) (h : x ≠ a) :
    paleySign a x = 1 ∨ paleySign a x = -1 :=
  quadraticChar_dichotomy (sub_ne_zero.mpr h)

























end
end PaleyWeil

end

section


open Finset Polynomial

namespace PaleyWeil

noncomputable section













theorem paleyPositive_filter_erase (H : Finset PaleyField) (x : PaleyField) :
    (H.erase x).filter (fun a ↦ paleySign a x = 1) =
      H.filter (fun a ↦ paleySign a x = 1) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · exact fun h ↦ ⟨h.1.2, h.2⟩
  · intro h
    refine ⟨⟨?_, h.1⟩, h.2⟩
    intro heq
    subst a
    simp at h



private theorem paley_sign_polynomial_of_notMem (H : Finset PaleyField) (x : PaleyField)
    (hx : x ∉ H) :
    (∏ a ∈ H, (X + C (paleySign a x) : ℤ[X])) =
      signedHistogramPolynomial H.card (paleyPositiveCount H x) := by
  have hplus : (∏ a ∈ H.filter (fun a ↦ paleySign a x = 1),
      (X + C (paleySign a x) : ℤ[X])) = (X + 1) ^ paleyPositiveCount H x := by
    rw [Finset.prod_congr rfl (fun a ha ↦ by rw [(Finset.mem_filter.mp ha).2, C_1])]
    exact Finset.prod_const _
  have hminus : (∏ a ∈ H.filter (fun a ↦ ¬paleySign a x = 1),
      (X + C (paleySign a x) : ℤ[X])) = (X - 1) ^ (H.card - paleyPositiveCount H x) := by
    have hcard : (H.filter (fun a ↦ ¬paleySign a x = 1)).card =
        H.card - paleyPositiveCount H x := by
      have h := Finset.card_filter_add_card_filter_not (s := H) (fun a ↦ paleySign a x = 1)
      change paleyPositiveCount H x + _ = _ at h
      omega
    have hf (a : PaleyField) (ha : a ∈ H.filter (fun a ↦ ¬paleySign a x = 1)) :
        (X + C (paleySign a x) : ℤ[X]) = X - 1 := by
      have haH := (Finset.mem_filter.mp ha).1
      have hane := (Finset.mem_filter.mp ha).2
      have hxa : x ≠ a := by intro h; exact hx (h ▸ haH)
      rw [(paleySign_dichotomy a x hxa).resolve_left hane]
      simp only [C_neg, C_1, sub_eq_add_neg]
    rw [Finset.prod_congr rfl hf, Finset.prod_const, hcard]
  rw [← Finset.prod_filter_mul_prod_filter_not H (fun a ↦ paleySign a x = 1), hplus, hminus]
  rfl










end
end PaleyWeil

end

open Finset Polynomial
open PaleyWeil

theorem solution (H : Finset PaleyField) (x : PaleyField) :
    (∏ a ∈ H, (X + C (paleySign a x) : ℤ[X])) =
      signedHistogramPolynomial (H.card - paleyInside H x) (paleyPositiveCount H x) *
        X ^ paleyInside H x := by
  by_cases hx : x ∈ H
  · rw [paleyInside, if_pos hx, pow_one, ← Finset.mul_prod_erase H _ hx]
    rw [paleySign_self, C_0, add_zero,
      paley_sign_polynomial_of_notMem (H.erase x) x (Finset.notMem_erase x H)]
    rw [Finset.card_erase_of_mem hx]
    have hp : paleyPositiveCount (H.erase x) x = paleyPositiveCount H x := by
      unfold paleyPositiveCount
      rw [paleyPositive_filter_erase]
    rw [hp, mul_comm]
  · rw [paleyInside, if_neg hx, Nat.sub_zero, pow_zero, mul_one]
    exact paley_sign_polynomial_of_notMem H x hx
