-- Prove2me | solution 1 for PaleyWeil.actualPaleyPrefixCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-25T06:47:57.986878+00:00
-- url     : https://prove2.me/submissions/9e34c5df-5626-44d1-acc8-fa12c5d2e2d0

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659CharacterBounds
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659LowMoments
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659PopulationMajorant
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_PaleyActualModel
import Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentSocketGuards
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
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
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
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction

section


/-! Exact identification with the campaign's Fin2659 nonzero-square orientation. -/

open Finset
open SensitivityRankedConstruction

namespace PaleyWeil

noncomputable section
open scoped Classical



@[simp] theorem paleyFinEquiv_val (x : Fin 2659) : (paleyFinEquiv x).val = x.val := rfl


private theorem paley_sub_val (a x : Fin 2659) :
    (paleyFinEquiv x - paleyFinEquiv a).val = (x.val + 2659 - a.val) % 2659 := by
  change ((x - a : Fin 2659).val) = (x.val + 2659 - a.val) % 2659
  rw [Fin.val_sub]
  apply congrArg (fun n : ℕ ↦ n % 2659)
  omega

theorem paley2659Arc_iff_nonzero_square (a x : Fin 2659) :
    paley2659Arc a x ↔
      ∃ z : PaleyField, z ≠ 0 ∧ z * z = paleyFinEquiv x - paleyFinEquiv a := by
  constructor
  · rintro ⟨z, hz, hroot⟩
    refine ⟨paleyFinEquiv z, ?_, ?_⟩
    · exact (ZMod.val_eq_zero (paleyFinEquiv z)).not.mp hz
    · apply ZMod.val_injective 2659
      rw [ZMod.val_mul, paley_sub_val, paleyFinEquiv_val]
      exact hroot
  · rintro ⟨z, hz, hroot⟩
    refine ⟨paleyFinEquiv.symm z, ?_, ?_⟩
    · exact (ZMod.val_eq_zero z).not.mpr hz
    · have hv := congrArg ZMod.val hroot
      rw [ZMod.val_mul, paley_sub_val] at hv
      exact hv

theorem paley2659Arc_iff_paleySign (a x : Fin 2659) :
    paley2659Arc a x ↔ paleySign (paleyFinEquiv a) (paleyFinEquiv x) = 1 := by
  rw [paley2659Arc_iff_nonzero_square]
  constructor
  · rintro ⟨z, hz, hroot⟩
    unfold paleySign
    rw [← hroot, ← pow_two]
    exact quadraticChar_sq_one' hz
  · intro h
    have hnz : paleyFinEquiv x - paleyFinEquiv a ≠ 0 := by
      intro hz
      have h' := h
      rw [paleySign, hz, quadraticChar_zero] at h'
      exact zero_ne_one h'
    obtain ⟨z, hz⟩ := (quadraticChar_one_iff_isSquare hnz).mp h
    refine ⟨z, ?_, hz.symm⟩
    intro heq
    subst z
    exact hnz (by simpa only [mul_zero] using hz)



@[simp] theorem card_paleyFieldSet (H : Finset (Fin 2659)) : (paleyFieldSet H).card = H.card :=
  Finset.card_map _

@[simp] theorem mem_paleyFieldSet (H : Finset (Fin 2659)) (x : Fin 2659) :
    paleyFinEquiv x ∈ paleyFieldSet H ↔ x ∈ H := Finset.mem_map' _

theorem paleyPositiveCount_actual (H : Finset (Fin 2659)) (x : Fin 2659) :
    paleyPositiveCount (paleyFieldSet H) (paleyFinEquiv x) =
      (H.filter (fun a ↦ paley2659Arc a x)).card := by
  unfold paleyPositiveCount paleyFieldSet
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  ext a
  simp only [Finset.mem_filter, Function.comp_apply, Equiv.toEmbedding_apply,
    paley2659Arc_iff_paleySign]






















end
end PaleyWeil

end

/-! Exact identification with the campaign's Fin2659 nonzero-square orientation. -/
open Finset
open SensitivityRankedConstruction
open PaleyWeil
open scoped Classical

theorem solution (H : Finset (Fin 2659)) (failures : ℕ) :
    actualPaleyPrefixCount H failures = paleyPrefixCount (paleyFieldSet H) failures := by
  let A := (Finset.univ : Finset (Fin 2659)).filter (fun x ↦ x ∉ H ∧
    H.card - failures ≤ (H.filter (fun a ↦ paley2659Arc a x)).card)
  let B := (Finset.univ : Finset PaleyField).filter (fun x ↦ x ∉ paleyFieldSet H ∧
    (paleyFieldSet H).card - failures ≤ paleyPositiveCount (paleyFieldSet H) x)
  have hm (x : Fin 2659) : x ∈ A ↔ paleyFinEquiv x ∈ B := by
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_paleyFieldSet, card_paleyFieldSet, paleyPositiveCount_actual]
  change A.card = B.card
  apply Finset.card_bij (fun x _ ↦ paleyFinEquiv x)
  · exact fun x hx ↦ (hm x).mp hx
  · exact fun x _ y _ h ↦ paleyFinEquiv.injective h
  · intro y hy
    refine ⟨paleyFinEquiv.symm y, ?_, paleyFinEquiv.apply_symm_apply y⟩
    exact (hm _).mpr (by simpa only [paleyFinEquiv.apply_symm_apply] using hy)
