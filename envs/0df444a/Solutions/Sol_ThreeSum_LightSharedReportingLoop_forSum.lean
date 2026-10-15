-- Prove2me | solution 1 for ThreeSum.LightSharedReportingLoop.forSum
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:02:52.935705+00:00
-- url     : https://prove2.me/submissions/888f9dec-bced-449b-a51e-341b3180d2e8

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_Light_Ends_while


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

section


/-!
# Proof rules for the light language

Ends lim P d s σ T Q says: the statement s, started in σ, ends within T steps in a state that
satisfies Q.  There is one rule for each construct; a rule turns a goal about a statement into goals
about its parts, so a proof follows the text of the program from top to bottom.  Recursion needs no
rule: a statement about a recursive procedure is proved by induction (in Lean) on a measure, and the
rule for calls unfolds the body.

There are three rules for loops: with an invariant indexed by the number of the round and a cost for
each round (Ends.while), the same with one cost for all rounds (Ends.whileConst), and, for a loop
whose number of rounds depends on the data, with a quantity that every round decreases
(Ends.whileVariant).

The file also has the basic facts about runs (a run stays a run when procedures are appended to the
program), notation for writing programs, the simplification set
`light_norm`, and the standing assumptions `Std` about the limits.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Runs -/



































/-! ## The rules -/






/-- More time and a weaker conclusion. -/
theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩










theorem Ends.set {σ T x e} {Q : State → Prop} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ) }) : Ends lim P d (.set x e) σ T Q :=
  ⟨_, _, .set hs, hT, h⟩







theorem Ends.seq {σ T s₁ s₂} {Q : State → Prop} (T₁ T₂ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' T₂ Q) (hT : T₁ + T₂ ≤ T) :
    Ends lim P d (.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .seq he₁ he₂, by omega, hq⟩


































































































/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/




























/-! ## Simplification -/

attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame
















/-! ## The limits -/
























end Light

end
end

section


/-! # Counting loops with the sum of the actual per-index budgets -/

namespace ThreeSum.LightSharedReportingLoop

open Light

theorem forSum_sourceProof {lim : Limits} {P : Program} {d : ℕ}
    {σ : State} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n : ℕ) (b : ℕ → ℕ)
    (start : I 0 {σ with loc := Function.update σ.loc i 0})
    (round : ∀ (j : ℕ) (σ : State), j < n → σ.loc i=(j : ℤ) → I j σ →
      Ends lim P d body σ (b j) (fun σ' =>
        σ'.loc i=(j : ℤ) ∧ I (j+1) {σ' with loc := Function.update σ'.loc i ((j : ℤ)+1)}))
    (done : ∀ (σ : State), σ.loc i=(n : ℤ) → I n σ → Q σ)
    (bound : ∀ (j : ℕ) (σ : State), j ≤ n → σ.loc i=(j : ℤ) → I j σ →
      hi.Safe lim σ ∧ hi.val σ=(n : ℤ))
    (hn : (n : ℤ) ≤ lim.word)
    (hT : (∑ j ∈ Finset.range n, (hi.cost+b j+7))+hi.cost+5 ≤ T) :
    Ends lim P d (Stmt.for i hi body) σ T Q := by
  have h0 : (0 : ℤ) ≤ lim.word := (Int.natCast_nonneg n).trans hn
  refine Ends.seq 2 ((∑ j ∈ Finset.range n, (hi.cost+b j+7))+hi.cost+3)
    (Ends.set (by simpa using h0) (by simp) ?_) (by omega)
  have H := Ends.while (lim := lim) (P := P) (d := d) (Q := Q)
    (σ := {σ with loc := Function.update σ.loc i 0})
    (c := (Light.Cond.lt (v i) hi)) (s := (Light.Stmt.seq body (.set i ((Light.Expr.op Light.Op.add) (v i) (k 1)))))
    (fun j σ => σ.loc i=(j : ℤ) ∧ I j σ) n (fun j => b j+4)
    (by exact ⟨by simp,by simpa using start⟩) ?round ?done
  · refine H.mono ?_ (fun _ h => h)
    simp only [Cond.cost,Expr.cost]
    have hsum : (∑ j ∈ Finset.range n, (1+hi.cost+1+1+(b j+4)))=
        ∑ j ∈ Finset.range n, (hi.cost+b j+7) := by
      apply Finset.sum_congr rfl
      intro j hj
      omega
    rw [hsum]
    omega
  case round =>
    rintro j σ hj ⟨hc,hI⟩
    obtain ⟨hs,hv⟩ := bound j σ hj.le hc hI
    refine ⟨⟨trivial,hs⟩,?_,Ends.seq (b j) 4 ((round j σ hj hc hI).mono le_rfl ?_) le_rfl⟩
    · change σ.loc i < hi.val σ
      rw [hc,hv]
      exact_mod_cast hj
    · rintro σ' ⟨hc',hI'⟩
      have hval : (((Light.Expr.op Light.Op.add) (v i) (k 1))).val σ'=(j : ℤ)+1 := by simp [hc']
      have hj' : (j : ℤ)+1 ≤ n := by exact_mod_cast hj
      refine Ends.set ⟨trivial,?_,?_⟩ (by simp) ⟨?_,?_⟩
      · change ((1 : ℕ) : ℤ) ≤ lim.word
        push_cast
        omega
      · change |(((Light.Expr.op Light.Op.add) (v i) (k 1))).val σ'| ≤ lim.word
        rw [hval,abs_of_nonneg (by omega)]
        omega
      · simp [hc']
      · rw [hval]
        exact hI'
  case done =>
    rintro σ ⟨hc,hI⟩
    obtain ⟨hs,hv⟩ := bound n σ le_rfl hc hI
    refine ⟨⟨trivial,hs⟩,?_,done σ hc hI⟩
    change ¬ σ.loc i < hi.val σ
    rw [hc,hv]
    exact lt_irrefl _

end ThreeSum.LightSharedReportingLoop

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {σ : Light.State} {i : Nat} {hi : Light.Expr} {body : Light.Stmt}
  {T : Nat} {Q : Light.State → Prop} (I : Nat → Light.State → Prop) (n : Nat) (b : Nat → Nat),
  I (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      {
        loc :=
          @Function.update.{1, 1} Nat (fun (a : Nat) => Int) instDecidableEqNat σ.loc i
            (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))),
        mem := σ.mem } →
    (∀ (j : Nat) (σ : Light.State),
        @LT.lt.{0} Nat instLTNat j n →
          @Eq.{1} Int (σ.loc i) (@Nat.cast.{0} Int instNatCastInt j) →
            I j σ →
              Light.Ends lim P d body σ (b j) fun (σ' : Light.State) =>
                And (@Eq.{1} Int (σ'.loc i) (@Nat.cast.{0} Int instNatCastInt j))
                  (I
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    {
                      loc :=
                        @Function.update.{1, 1} Nat (fun (a : Nat) => Int) instDecidableEqNat σ'.loc i
                          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                            (@Nat.cast.{0} Int instNatCastInt j)
                            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))),
                      mem := σ'.mem })) →
      (∀ (σ : Light.State), @Eq.{1} Int (σ.loc i) (@Nat.cast.{0} Int instNatCastInt n) → I n σ → Q σ) →
        (∀ (j : Nat) (σ : Light.State),
            @LE.le.{0} Nat instLENat j n →
              @Eq.{1} Int (σ.loc i) (@Nat.cast.{0} Int instNatCastInt j) →
                I j σ →
                  And (Light.Expr.Safe lim σ hi)
                    (@Eq.{1} Int (Light.Expr.val σ hi) (@Nat.cast.{0} Int instNatCastInt n))) →
          @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt n) lim.word →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (∑ j ∈ Finset.range n,
                      @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hi.cost (b j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                    hi.cost)
                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                T →
              Light.Ends lim P d (Light.Stmt.for i hi body) σ T Q := by
  exact @ThreeSum.LightSharedReportingLoop.forSum_sourceProof

#print axioms solution
