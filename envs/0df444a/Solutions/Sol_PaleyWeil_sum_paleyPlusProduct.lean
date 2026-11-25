-- Prove2me | solution 1 for PaleyWeil.sum_paleyPlusProduct
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-25T06:47:55.699699+00:00
-- url     : https://prove2.me/submissions/49f0107e-fa78-4622-97f9-23f355d0bf9d

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

open Finset
open PaleyWeil

theorem solution (H : Finset PaleyField) :
    (∑ x : PaleyField, paleyPlusProduct H x) =
      (2 : ℤ) ^ H.card * (paleyCommonCount H : ℤ) + paleyInternalCorrection H := by
  have hp (x : PaleyField) : paleyPlusProduct H x =
      (2 : ℤ) ^ H.card * (if ∀ a ∈ H, paleySign a x = 1 then 1 else 0) +
        (if x ∈ H then paleyPlusProduct H x else 0) := by
    by_cases hx : x ∈ H
    · have hn : ¬∀ a ∈ H, paleySign a x = 1 := by
        intro h
        have := h x hx
        simp at this
      simp [hx, hn]
    · by_cases ha : ∀ a ∈ H, paleySign a x = 1
      · have hprod : paleyPlusProduct H x = (2 : ℤ) ^ H.card := by
          unfold paleyPlusProduct
          rw [Finset.prod_congr rfl (fun a ha' ↦ by rw [ha a ha'])]
          norm_num
        rw [if_pos ha, if_neg hx, mul_one, add_zero]
        exact hprod
      · obtain ⟨a, haH, han⟩ := not_forall.mp ha |>.imp fun a h ↦ by
          simpa only [not_forall, exists_prop] using h
        have hxa : x ≠ a := by intro h; exact hx (h ▸ haH)
        have hsign : paleySign a x = -1 := (paleySign_dichotomy a x hxa).resolve_left han
        have hprod : paleyPlusProduct H x = 0 := by
          apply Finset.prod_eq_zero haH
          simp [hsign]
        simp [hx, ha, hprod]
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ (Finset.univ : Finset PaleyField)) ↦ hp x)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcount : (∑ x : PaleyField,
      if ∀ a ∈ H, paleySign a x = 1 then (1 : ℤ) else 0) =
      (paleyCommonCount H : ℤ) := by
    rw [Finset.sum_boole]
    rfl
  have hcorr : (∑ x : PaleyField, if x ∈ H then paleyPlusProduct H x else 0) =
      paleyInternalCorrection H := by
    rw [← Finset.sum_filter]
    have hfilter : (Finset.univ : Finset PaleyField).filter (fun x ↦ x ∈ H) = H := by
      ext x
      simp
    rw [hfilter]
    rfl
  rw [hcount, hcorr]
