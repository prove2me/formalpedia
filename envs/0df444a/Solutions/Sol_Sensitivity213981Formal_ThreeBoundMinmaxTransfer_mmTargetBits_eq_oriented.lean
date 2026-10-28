-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mmTargetBits_eq_oriented
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:08:30.728414+00:00
-- url     : https://prove2.me/submissions/67f5cf7b-917d-45c6-bacc-7a9916752b79

import Definitions.Def_Sensitivity213981Formal_MinmaxB
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto


namespace Sensitivity213981Formal
section
/- Actual min/max downward transfer, with the upper-child improvement and
exact next-tier guard-destruction gate. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem mm_left_eq_lower (F : L → (I → Bool) → Bool) (hF : Nested F)
    (t u : L) (htu : t ≤  u) (y : I → Bool) (hy : F u y=true) :
    (fun x => mm F t u x y)=F t := by
  funext x
  have hyt := hF _ _ htu _ hy
  simp only [mm,hyt,hy,Bool.and_true,Bool.or_true]

theorem mm_left_eq_upper (F : L → (I → Bool) → Bool) (hF : Nested F)
    (t u : L) (htu : t ≤  u) (y : I → Bool) (hyt : F t y=true) (hyu : F u y=false) :
    (fun x => mm F t u x y)=F u := by
  funext x
  simp only [mm,hyt,hyu,Bool.and_true,Bool.or_false]
  cases hu : F u x with
  | false => simp
  | true => simp only [hF _ _ htu _ hu,Bool.and_self]







theorem mmTargetBits_eq_oriented (F : L → (I → Bool) → Bool) (hF : Nested F)
    (t u : L) (htu : t ≤  u) (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool)
    (hh : F u (child x w c)=true) (hl : F t (child x w (!c))=true) :
    mmTargetBits F t u x w =
      if F u (child x w (!c))=true then orientedBits F t t x w c else orientedBits F t u x w c := by
  cases c
  · simp only [Bool.not_false] at hl ⊢
    by_cases ho : F u (child x w true)=true
    · rw [if_pos ho]
      unfold mmTargetBits orientedBits
      simp only [Bool.not_false]
      rw [mm_left_eq_lower F hF t u htu _ ho,mm_left_eq_lower F hF t u htu _ hh,Finset.union_comm]
    · rw [if_neg ho]
      have ho' : F u (child x w true)=false := by cases he : F u (child x w true) <;> simp_all
      unfold mmTargetBits orientedBits
      simp only [Bool.not_false]
      rw [mm_left_eq_upper F hF t u htu _ hl ho',mm_left_eq_lower F hF t u htu _ hh,Finset.union_comm]
  · simp only [Bool.not_true] at hl ⊢
    by_cases ho : F u (child x w false)=true
    · rw [if_pos ho]
      unfold mmTargetBits orientedBits
      simp only [Bool.not_true]
      rw [mm_left_eq_lower F hF t u htu _ hh,mm_left_eq_lower F hF t u htu _ ho]
    · rw [if_neg ho]
      have ho' : F u (child x w false)=false := by cases he : F u (child x w false) <;> simp_all
      unfold mmTargetBits orientedBits
      simp only [Bool.not_true]
      rw [mm_left_eq_lower F hF t u htu _ hh,mm_left_eq_upper F hF t u htu _ hl ho']











end
end ThreeBoundMinmaxTransfer




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [inst_1 : Fintype.{0} I] [Fintype.{0} V] (F : L → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      F)
  (t u : L)
  (htu :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      t u)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (w : V) (c : Bool)
  (hh : @Eq.{1} Bool (F u (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w c)) Bool.true)
  (hl : @Eq.{1} Bool (F t (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w (Bool.not c))) Bool.true),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
    (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mmTargetBits L I V inst_1 F t u x w)
    (@ite.{1} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@Eq.{1} Bool (F u (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w (Bool.not c))) Bool.true)
      (instDecidableEqBool (F u (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w (Bool.not c))) Bool.true)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedBits L I V inst_1 F t t x w c)
      (@Sensitivity213981Formal.ThreeBoundMinmaxTransfer.orientedBits L I V inst_1 F t u x w c)) := @Sensitivity213981Formal.ThreeBoundMinmaxTransfer.mmTargetBits_eq_oriented
