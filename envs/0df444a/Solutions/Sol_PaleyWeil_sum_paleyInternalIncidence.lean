-- Prove2me | solution 1 for PaleyWeil.sum_paleyInternalIncidence
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-25T06:47:56.888064+00:00
-- url     : https://prove2.me/submissions/93fe4d18-8824-48da-8082-808b0a92d695

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659CharacterBounds
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
import Mathlib.Data.Nat.Sqrt
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
import Mathlib.Tactic.IntervalCases
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

section


open Finset

namespace PaleyWeil

noncomputable section















@[simp] theorem paleySign_self (a : PaleyField) : paleySign a a = 0 := by
  simp [paleySign]



theorem paleySign_dichotomy (a x : PaleyField) (h : x ≠ a) :
    paleySign a x = 1 ∨ paleySign a x = -1 :=
  quadraticChar_dichotomy (sub_ne_zero.mpr h)

theorem paleySign_swap (a x : PaleyField) : paleySign a x = -paleySign x a := by
  have hneg : quadraticChar PaleyField (-1) = -1 := by
    rw [quadraticChar_neg_one_iff_not_isSquare, FiniteField.isSquare_neg_one_iff]
    simp only [ZMod.card]
    norm_num
  unfold paleySign
  rw [show x - a = -1 * (a - x) by ring, map_mul, hneg, neg_one_mul]























end
end PaleyWeil

end

section


open Finset

namespace PaleyWeil

noncomputable section

theorem paleyPositiveCount_sum (H : Finset PaleyField) (x : PaleyField) :
    (paleyPositiveCount H x : ℤ) =
      ∑ a ∈ H, (if paleySign a x = 1 then (1 : ℤ) else 0) := by
  simp only [Finset.sum_boole, paleyPositiveCount]

private theorem two_mul_choose_two (n : ℕ) :
    (2 : ℤ) * (Nat.choose n 2 : ℤ) = (n : ℤ) ^ 2 - (n : ℤ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hrec : Nat.choose (n + 1) 2 = n + Nat.choose n 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ n 1
    rw [hrec]
    push_cast
    nlinarith
































end
end PaleyWeil

end

open Finset
open PaleyWeil

theorem solution (H : Finset PaleyField) :
    (∑ x ∈ H, (paleyPositiveCount H x : ℤ)) = (Nat.choose H.card 2 : ℤ) := by
  have horient (a x : PaleyField) :
      (if paleySign a x = 1 then (1 : ℤ) else 0) +
        (if paleySign x a = 1 then (1 : ℤ) else 0) = if a = x then 0 else 1 := by
    by_cases hax : a = x
    · subst a
      simp
    · rw [paleySign_swap x a]
      rcases paleySign_dichotomy a x (Ne.symm hax) with h | h <;> simp [h, hax]
  have hsum : (2 : ℤ) * (∑ x ∈ H, (paleyPositiveCount H x : ℤ)) =
      (H.card : ℤ) ^ 2 - (H.card : ℤ) := by
    simp_rw [paleyPositiveCount_sum]
    calc
      2 * (∑ x ∈ H, ∑ a ∈ H, if paleySign a x = 1 then (1 : ℤ) else 0) =
          (∑ x ∈ H, ∑ a ∈ H, if paleySign a x = 1 then (1 : ℤ) else 0) +
            (∑ x ∈ H, ∑ a ∈ H, if paleySign x a = 1 then (1 : ℤ) else 0) := by
        have hcomm : (∑ x ∈ H, ∑ a ∈ H, if paleySign x a = 1 then (1 : ℤ) else 0) =
            ∑ x ∈ H, ∑ a ∈ H, if paleySign a x = 1 then (1 : ℤ) else 0 := Finset.sum_comm
        rw [hcomm]
        ring
      _ = ∑ x ∈ H, ∑ a ∈ H, (if a = x then (0 : ℤ) else 1) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        exact fun a _ ↦ horient a x
      _ = ∑ _x ∈ H, ((H.card : ℤ) - 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        calc
          _ = ∑ a ∈ H, (1 - if a = x then (1 : ℤ) else 0) := by
            apply Finset.sum_congr rfl
            intro a _
            split_ifs <;> norm_num
          _ = _ := by rw [Finset.sum_sub_distrib]; simp [hx]
      _ = _ := by simp; ring
  have hchoose := two_mul_choose_two H.card
  omega
