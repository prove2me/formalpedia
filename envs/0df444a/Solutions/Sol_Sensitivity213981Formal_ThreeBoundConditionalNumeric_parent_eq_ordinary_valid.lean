-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundConditionalNumeric.parent_eq_ordinary_valid
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:05:20.955023+00:00
-- url     : https://prove2.me/submissions/dde24f1a-5237-4801-ad16-3bda28d8ed0a

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_OrdinaryParentBridge
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
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
/-
Common block and positive-sensitivity witnesses for a broad two-child
guarded construction. These are lower-bound witnesses; no upper sensitivity
transfer theorem is asserted here.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundWitness
open OAI.Paper320

variable {L I V : Type}









theorem parent_true_iff [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool) :
    parent S F l x = true ↔ ∃ v : V,
      (failed S F l x v).card ≤  S.tolerance l ∧
      S.target l (failed S F l x v).card (child x v false) (child x v true) = true := by
  classical
  simp [parent]















































/- Reindexing lemmas follow the accepted Apache-2.0 source by @yousofy:
   Sol_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate,
   together with Definitions.Def_Paley11987Support_053. -/










end ThreeBoundWitness








end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/-
Ordinary-component conditional transfers for the actual guarded Boolean family.
This development uses the shared campaign bit-flip definitions throughout.
-/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]









@[simp] theorem ordinary_failed (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g l : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) (v : V) :
    failed (ordinaryStage S F t g q) F l x v = guardFailures S F g x v := rfl

@[simp] theorem ordinary_parent_true (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) :
    ordinaryParent S F t g q x = true ↔ ∃ v, ordinaryRow S F t g q x v := by
  simp only [ordinaryParent, parent_true_iff, ordinary_failed, ordinaryStage,
    Bool.and_eq_true, ordinaryRow]
  constructor
  · rintro ⟨v,hc,hf,ht⟩
    exact ⟨v, fun c => by cases c <;> assumption, hc⟩
  · rintro ⟨v,ht,hc⟩
    exact ⟨v,hc,ht false,ht true⟩































































end
end ThreeBoundConditional




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Semantic interpretation of numeric entries, ordinary components and raw B. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace ThreeBoundConditionalNumeric
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundGradedCandidates ThreeBoundHeadExpressions
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]











/-- Only target values at feasible guard counts are needed for parent equality. -/
theorem parent_eq_ordinary_valid (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (l t : Fin n)
    (hconstant : ∀ d, d ≤  S.tolerance l → ∀ u z,
      S.target l d u z = (F t u && F t z)) :
    parent S F l = ordinaryParent S F t (S.guard l) (S.tolerance l) := by
  funext x
  have hfailed (w : V) : failed S F l x w=guardFailures S F (S.guard l) x w := rfl
  have hi : parent S F l x=true ↔ ordinaryParent S F t (S.guard l) (S.tolerance l) x=true := by
    rw [parent_true_iff,ordinary_parent_true]
    constructor
    · rintro ⟨w,hc,ht⟩
      rw [hconstant _ hc] at ht
      have hh : ∀ c, F t (child x w c)=true := by
        intro c
        cases c <;> simp_all
      exact ⟨w,hh,by simpa only [hfailed] using hc⟩
    · rintro ⟨w,ht,hc⟩
      have hc' : (failed S F l x w).card ≤  S.tolerance l := by simpa only [hfailed] using hc
      refine ⟨w,hc',?_⟩
      rw [hconstant _ hc']
      simp [ht]
  cases h₁ : parent S F l x <;>
    cases h₂ : ordinaryParent S F t (S.guard l) (S.tolerance l) x <;> simp_all











end
end ThreeBoundConditionalNumeric




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n : Nat} {I V : Type} [Fintype.{0} I] [inst : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (l t : Fin n)
  (hconstant :
    ∀ (d : Nat),
      @LE.le.{0} Nat instLENat d (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance (Fin n) I V S l) →
        ∀ (u z : I → Bool),
          @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.Stage.target (Fin n) I V S l d u z)
            (Bool.and (F t u) (F t z))),
  @Eq.{1} ((x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) → Bool)
    (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst S F l)
    (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent (Fin n) I V inst S F t
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard (Fin n) I V S l)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance (Fin n) I V S l)) := @Sensitivity213981Formal.ThreeBoundConditionalNumeric.parent_eq_ordinary_valid
