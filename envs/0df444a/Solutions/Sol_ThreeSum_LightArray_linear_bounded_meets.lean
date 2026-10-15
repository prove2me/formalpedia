-- Prove2me | solution 1 for ThreeSum.LightArray.linear_bounded_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:43:58.902746+00:00
-- url     : https://prove2.me/submissions/3bad13eb-8985-4940-bb7a-52aa0da2511b

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Light_Ends_pass


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






































































































































/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/




























/-! ## Simplification -/

attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame












/-- The natural number behind an address that is a sum of two natural numbers. -/
@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]

/-! ## The limits -/
























end Light

end
end

section


/-!
# Calls

Meets lim P p d vals μ T R is the specification of a procedure: procedure number p of the program P,
run at depth d on the arguments vals in the memory μ, ends within T steps with a result and a memory
that satisfy R. A routine is proved to meet such a specification (Meets.of_body), and a caller uses
the specification only, so that the proof of a caller does not depend on the body of a callee.

The specification of a routine x, as its callers assume it, has the form
`∀ (data) μ, hypotheses → ∀ d, d + k ≤ lim.depth → Meets lim P p d vals μ T R`.  Here k is the
number of levels of calls that x needs below itself, and d, the depth at which the body of x runs,
comes last.

There is one rule for calls, in four forms.  It is told the fact about the callee, from which it
reads the values of the arguments, the time and what holds afterwards, and it asks for what follows
the call.  Three side goals have default proofs: the arguments are safe and have these values, one
more level of calls is allowed, and the time suffices.  Ends.callTo and Ends.callToThen are the rule
for a state ⟨frame l, μ⟩; Ends.callLast and Ends.callThen are the same for local variables that are
not given as a list.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Specifications of procedures -/







section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : Stmt}
    (hp : P[p]? = some body)
    (h : Ends lim P d body ⟨frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩























end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop} {s : Stmt}











































end

end Light

end
end

section


/-!
# Regions of the memory, and the cells that a step leaves alone

A region is given by its first address `a` and its number `n` of cells.  `Inside a n b` says that
the cell `b` lies in it, `Outside a n b` that it does not, and `Apart a n a' n'` that two regions do
not meet.  `InOrder top [(a, n), (a', n'), …]` says that the listed regions lie one behind the other
and end at or below `top`.  All of these abbreviate linear inequalities.

`SameOn K μ μ'` says that the memory `μ'` agrees with `μ` on every cell that satisfies `K`.  It is
the one notion of "these cells are unchanged": a routine promises `SameOn K μ μ'` for the cells
`K` that it leaves alone.  (It is `Set.EqOn μ' μ {b | K b}`, stated with a predicate: the conditions
`K b` that occur are linear inequalities between addresses and are used as such.)  The usual choices
of `K` have names.

* `SameOutside μ μ' a n`: all cells outside one region; `SameOutside2` and `SameOutside3`: all cells
  outside two or three regions.
* `Kept μ μ' fr`: all cells below the free pointer `fr`.
* `KeptBut μ μ' fr out len`: all cells below `fr` outside the region of an output.

## How a fact is carried from one memory to a later one

A predicate `X` about a memory has one lemma of the name `X.keep` and of the form

  `theorem X.keep (h : X μ …) (hs : SameOn K μ μ' := by light_keep) : X μ' …`

where `K` describes the cells that `X` reads; `Seg.keep` is the model.  The argument `hs` has a
default proof.  So `h.keep`, with no argument, stands for "`h` still holds in the memory that is
asked for here".  The default proof `light_keep` uses every hypothesis of the form `SameOn _ ν ν'`
in the context, that is, the promises of the steps that were taken since `h` was obtained, and the
inequalities in the context that say where the regions lie.  In the proofs a promise is named when
the step is taken, as `same₂` in `rintro _ μ₂ ⟨sY, same₂⟩`.

`wrote μ dst f j` is the memory `μ` after a loop has written `f 0`, …, `f (j - 1)` to the cells from
`dst`.
-/

@[expose] public section

namespace Light

/-! ## Regions -/


















/-! ## Memories that agree on some cells -/























variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}

/-- The case of a single cell. -/
theorem SameOn.cell (h : SameOn (· = b) μ μ') : μ' b = μ b := h b rfl




















/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}











/-- A cell that has been written. -/
theorem wrote_done {i : ℕ} (h : i < j) : wrote μ dst f j (dst + i) = f i := by
  unfold wrote
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

/-- A cell that has not been written (yet). -/
theorem wrote_rest {a : ℕ} (h : Outside dst j a) : wrote μ dst f j a = μ a := by
  unfold wrote
  rw [if_neg (by omega)]


























/-! ## The tactics -/









































end Light

end
end

section


/-!
# Costed array arithmetic in the benchmark's imperative language

These are actual `Light.Stmt` programs and `Light.Meets` execution proofs.
Their contracts count every expression evaluation and memory operation.
-/

namespace ThreeSum.LightArray

open Light

variable {lim : Limits} {P : Program} {d : ℕ}





theorem source_read {μ : ℕ → ℤ} {src dst n j : ℕ} {f : ℕ → ℤ}
    (h : SourceSafe src dst n) (hj : j < n) :
    wrote μ dst f j (src + j) = μ (src + j) := by
  rcases h with rfl | h
  · exact wrote_rest (by omega)
  · exact wrote_rest (by omega)







theorem linear_meets {p : ℕ} (hp : P[p]? = some linearBody)
    {μ : ℕ → ℤ} {srcA srcB dst n : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : srcA + n ≤ lim.space) (hB : srcB + n ≤ lim.space)
    (hD : dst + n ≤ lim.space)
    (hsepA : SourceSafe srcA dst n) (hsepB : SourceSafe srcB dst n)
    (hmul : ∀ i < n, |c * μ (srcB + i)| ≤ lim.word)
    (hsum : ∀ i < n, |μ (srcA + i) + c * μ (srcB + i)| ≤ lim.word) :
    Meets lim P p d [(srcA : ℤ), srcB, dst, n, c] μ (linearTime n) fun _ μ' =>
      (∀ i < n, μ' (dst + i) = μ (srcA + i) + c * μ (srcB + i)) ∧
        SameOutside μ μ' dst n := by
  refine .of_body hp (Ends.pass (fun i => μ (srcA + i) + c * μ (srcB + i))
    (fun i hi => ?_) ⟨fun i hi => wrote_done (f := fun i => μ (srcA + i) + c * μ (srcB + i)) hi, by ((try refine Light.SameOn.cell ?_); (intro apspMacro_10207_0 apspMacro_10207_1);
                                                                                                          (first
                                                                                                            |
                                                                                                              ((((repeat
                                                                                                                        (((with_reducible
                                                                                                                                rename Light.SameOn _ _ _ => apspMacro_10207_2));
                                                                                                                          ((try
                                                                                                                                have :=
                                                                                                                                  apspMacro_10207_2 apspMacro_10207_0 (by omega)));
                                                                                                                          (revert apspMacro_10207_2)));
                                                                                                                    (intros);
                                                                                                                    (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                                                (omega))
                                                                                                            |
                                                                                                              ((simp [] at apspMacro_10207_1);
                                                                                                                (((repeat
                                                                                                                        (((with_reducible
                                                                                                                                rename Light.SameOn _ _ _ => apspMacro_10207_3));
                                                                                                                          ((try
                                                                                                                                have :=
                                                                                                                                  apspMacro_10207_3 apspMacro_10207_0 (by omega)));
                                                                                                                          (revert apspMacro_10207_3)));
                                                                                                                    (intros);
                                                                                                                    (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                                                (omega))
                                                                                                            |
                                                                                                              ((((repeat
                                                                                                                        (((with_reducible
                                                                                                                                rename Light.SameOn _ _ _ => apspMacro_10207_4));
                                                                                                                          ((try
                                                                                                                                have :=
                                                                                                                                  apspMacro_10207_4 apspMacro_10207_0 (by omega)));
                                                                                                                          (revert apspMacro_10207_4)));
                                                                                                                    (intros);
                                                                                                                    (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                                                (fail
                                                                                                                    "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                                              SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                                              its condition K x does not follow from the hypotheses."))))⟩
    hw hD rfl rfl (hT := by first
                            |
                              ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, linearTime]);
                                (first
                                  | omega
                                  | ((ring_nf); (omega))))
                            | omega
                            |
                              (simp [linearTime] <;>
                                  first
                                  | omega
                                  | ((ring_nf); (omega)))))
  have hrA := source_read (μ := μ)
    (f := fun i => μ (srcA + i) + c * μ (srcB + i)) hsepA hi
  have hrB := source_read (μ := μ)
    (f := fun i => μ (srcA + i) + c * μ (srcB + i)) hsepB hi
  have hm := abs_le.mp (hmul i hi)
  have hs := abs_le.mp (hsum i hi)
  (((try have := Light.Std.space_le (by assumption)));
    ((try have := Light.Std.const_le (by assumption)));
    (simp [Light.Limits.Addr, abs_le, -abs_mul, hrA, hrB] <;> omega))

/-- A convenient polynomial-word bound for both addition and subtraction. -/
theorem linear_bounded_meets_sourceProof {p : ℕ} (hp : P[p]? = some linearBody)
    {μ : ℕ → ℤ} {srcA srcB dst n U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : srcA + n ≤ lim.space) (hB : srcB + n ≤ lim.space)
    (hD : dst + n ≤ lim.space)
    (hsepA : SourceSafe srcA dst n) (hsepB : SourceSafe srcB dst n)
    (hc : |c| ≤ 1) (hword : 2 * (U : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (srcA + i)| ≤ U ∧ |μ (srcB + i)| ≤ U) :
    Meets lim P p d [(srcA : ℤ), srcB, dst, n, c] μ (linearTime n) fun _ μ' =>
      (∀ i < n, μ' (dst + i) = μ (srcA + i) + c * μ (srcB + i)) ∧
        SameOutside μ μ' dst n := by
  have hm : ∀ i < n, |c * μ (srcB + i)| ≤ U := by
    intro i hi
    rw [abs_mul]
    calc
      _ ≤ 1 * (U : ℤ) := mul_le_mul hc (hvalues i hi).2 (abs_nonneg _) (by omega)
      _ = U := one_mul _
  apply linear_meets hp hw hA hB hD hsepA hsepB
  · intro i hi
    exact (hm i hi).trans (by omega)
  · intro i hi
    exact (abs_add_le _ _).trans ((add_le_add (hvalues i hi).1 (hm i hi)).trans (by omega))












end ThreeSum.LightArray

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d p : Nat},
  @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P p)
      (@Option.some.{0} Light.Stmt ThreeSum.LightArray.linearBody) →
    ∀ {μ : Nat → Int} {srcA srcB dst n U : Nat} {c : Int},
      @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
        @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcA n) lim.space →
          @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcB n) lim.space →
            @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst n) lim.space →
              ThreeSum.LightArray.SourceSafe srcA dst n →
                ThreeSum.LightArray.SourceSafe srcB dst n →
                  @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup c)
                      (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))) →
                    @LE.le.{0} Int Int.instLEInt
                        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))
                          (@Nat.cast.{0} Int instNatCastInt U))
                        lim.word →
                      (∀ (i : Nat),
                          @LT.lt.{0} Nat instLTNat i n →
                            And
                              (@LE.le.{0} Int Int.instLEInt
                                (@abs.{0} Int instLatticeInt Int.instAddGroup
                                  (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcA i)))
                                (@Nat.cast.{0} Int instNatCastInt U))
                              (@LE.le.{0} Int Int.instLEInt
                                (@abs.{0} Int instLatticeInt Int.instAddGroup
                                  (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcB i)))
                                (@Nat.cast.{0} Int instNatCastInt U))) →
                        Light.Meets lim P p d
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcA)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcB)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                                  (@List.cons.{0} Int c (@List.nil.{0} Int))))))
                          μ (ThreeSum.LightArray.linearTime n) fun (x : Int) (μ' : Nat → Int) =>
                          And
                            (∀ (i : Nat),
                              @LT.lt.{0} Nat instLTNat i n →
                                @Eq.{1} Int (μ' (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst i))
                                  (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                                    (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcA i))
                                    (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) c
                                      (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcB i)))))
                            (Light.SameOutside μ μ' dst n) := by
  exact @ThreeSum.LightArray.linear_bounded_meets_sourceProof

#print axioms solution
