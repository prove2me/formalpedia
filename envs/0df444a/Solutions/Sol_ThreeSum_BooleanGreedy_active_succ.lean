-- Prove2me | solution 1 for ThreeSum.BooleanGreedy.active_succ
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:41:35.75032+00:00
-- url     : https://prove2.me/submissions/6239245c-4c58-4668-9d9c-a09f46cc9970

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-! # An executable finite greedy cover and its logarithmic length bound -/

namespace ThreeSum.Cover

open Finset
open scoped BigOperators

variable {Ω U : Type*} [Inhabited Ω] [DecidableEq U]






theorem selectMap_mem (maps : List Ω) (hne : maps ≠ [])
    (covers : Ω → U → Prop) [DecidableRel covers] (targets : Finset U) :
    selectMap maps covers targets ∈ maps := by
  unfold selectMap
  cases h : maps.argmax (fun ω => (targets.filter (covers ω)).card) with
  | none => exact False.elim (hne (List.argmax_eq_none.mp h))
  | some ω =>
    simp only [Option.getD_some]
    exact List.argmax_mem (f := fun ω => (targets.filter (covers ω)).card)
      (by simpa only [Option.mem_def] using h)








































































































































end ThreeSum.Cover

end

section


/-! # Boolean-array semantics of the already specified finite greedy schedule -/

namespace ThreeSum.BooleanGreedy

open Finset
open scoped BigOperators





















































theorem choice_lt {matrix : ℕ → ℕ → ℕ} {rows cols : ℕ} (hrows : 0 < rows) (t : ℕ) :
    choice matrix rows cols t < rows := by
  apply List.mem_range.mp
  exact Cover.selectMap_mem _ (by simpa using hrows.ne') _ _





























theorem active_succ_sourceProof {matrix : ℕ → ℕ → ℕ} {rows cols : ℕ}
    (hrows : 0 < rows)
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1) (t j : ℕ) (hj : j < cols) :
    active matrix rows cols (t+1) j =
      active matrix rows cols t j * (1-matrix (choice matrix rows cols t) j) := by
  have hm := hmatrix _ (choice_lt (matrix := matrix) (cols := cols) hrows t) j hj
  have hmem : j ∈ state matrix rows cols (t+1) ↔
      j ∈ state matrix rows cols t ∧ ¬covers matrix (choice matrix rows cols t) j :=
    Finset.mem_filter
  by_cases ha : j ∈ state matrix rows cols t <;>
    by_cases hc : matrix (choice matrix rows cols t) j = 1
  · have hn : j ∉ state matrix rows cols (t+1) := fun h => (hmem.mp h).2 hc
    simp only [active,if_neg hn,if_pos ha,hc,Nat.sub_self,Nat.mul_zero]
  · have hz : matrix (choice matrix rows cols t) j = 0 := by omega
    have hn : j ∈ state matrix rows cols (t+1) := hmem.mpr ⟨ha,hc⟩
    simp only [active,if_pos hn,if_pos ha,hz,Nat.sub_zero,Nat.mul_one]
  · have hn : j ∉ state matrix rows cols (t+1) := fun h => ha (hmem.mp h).1
    simp only [active,if_neg hn,if_neg ha,Nat.zero_mul]
  · have hn : j ∉ state matrix rows cols (t+1) := fun h => ha (hmem.mp h).1
    simp only [active,if_neg hn,if_neg ha,Nat.zero_mul]







end ThreeSum.BooleanGreedy

end


theorem solution : ∀ {matrix : Nat → Nat → Nat} {rows cols : Nat},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) rows →
    (∀ (i : Nat),
        @LT.lt.{0} Nat instLTNat i rows →
          ∀ (j : Nat),
            @LT.lt.{0} Nat instLTNat j cols →
              @LE.le.{0} Nat instLENat (matrix i j) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      ∀ (t j : Nat),
        @LT.lt.{0} Nat instLTNat j cols →
          @Eq.{1} Nat
            (ThreeSum.BooleanGreedy.active matrix rows cols
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              j)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (ThreeSum.BooleanGreedy.active matrix rows cols t j)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (matrix (ThreeSum.BooleanGreedy.choice matrix rows cols t) j))) := by
  exact @ThreeSum.BooleanGreedy.active_succ_sourceProof

#print axioms solution
