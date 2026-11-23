-- Prove2me | solution 1 for PI.SqfRootsInj.W.pow_card_minpoly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:43.332994+00:00
-- url     : https://prove2.me/submissions/606cbcf5-8463-4d0b-9cc4-a807090d5919

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_ClaimOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
namespace PI.SqfRootsInj.W
theorem _root_.solution {g : ℕ} [Fact g.Prime] (w : Fbar g) :
    w ^ (g ^ (minpoly (ZMod g) w).natDegree) = w := by
  have hw : IsIntegral (ZMod g) w := Algebra.IsIntegral.isIntegral w
  haveI : FiniteDimensional (ZMod g) (IntermediateField.adjoin (ZMod g) {w}) :=
    IntermediateField.adjoin.finiteDimensional hw
  haveI : Finite (IntermediateField.adjoin (ZMod g) {w}) :=
    Module.finite_of_finite (ZMod g)
  letI : Fintype (IntermediateField.adjoin (ZMod g) {w}) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin (ZMod g) {w}) =
      g ^ (minpoly (ZMod g) w).natDegree := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, IntermediateField.adjoin.finrank hw]
  have h := FiniteField.pow_card (IntermediateField.AdjoinSimple.gen (ZMod g) w)
  rw [hcard] at h
  have h2 := congrArg Subtype.val h
  simpa using h2
end PI.SqfRootsInj.W
