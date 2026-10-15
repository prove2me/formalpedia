-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.ends
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:29:29.89116+00:00
-- url     : https://prove2.me/submissions/f8d1a149-f474-4b85-9559-a8ed26fa6888

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for
import Theorems.Thm_ThreeSum1960614_Machine_Light_emod_meets

namespace Light
end Light
namespace Light.Emod
end Light.Emod
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Emod
end ThreeSum1960614.Machine.Light.Emod
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues

namespace ThreeSum1960614.Machine

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
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Runs -/









/-! ## The rules -/





























/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/


















/-! ## Simplification -/

attribute [simp] _root_.ThreeSum1960614.Machine.Light.Expr.val _root_.ThreeSum1960614.Machine.Light.Expr.cost _root_.ThreeSum1960614.Machine.Light.Expr.Safe _root_.Light.Op.eval _root_.ThreeSum1960614.Machine.Light.Cond.Holds _root_.ThreeSum1960614.Machine.Light.Cond.cost _root_.ThreeSum1960614.Machine.Light.Cond.Safe _root_.Light.frame





/-- The natural number behind an address that is a sum of two natural numbers. -/
@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]

/-! ## The limits -/









end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Local variables as a list

In the proof of a procedure body the state is written out as ⟨frame [a, b, …], μ⟩: the list
holds the local variables 0, 1, …, and all further ones are 0.  An assignment to local x replaces
entry x of the list (setLocal).  The rules of this file treat one statement each.  They are told the
value that is assigned or stored, and they ask for one fact about each expression: that its
evaluation stays within the limits and gives this value (Expr.Gives).  This fact and the comparison
of the costs are proved by default from the hypotheses in the context.  Ends.forFrame and
Ends.forShape are the rules for counting loops in this form.  In the names of the rules, To says
that the state is ⟨frame l, μ⟩.

Locals by name, and locals whose values do not matter:

* `setLocals l [(x, a), (y, b), …]` is the list `l` after the assignments `x := a`, `y := b`, ….
  With the names of the locals for `x`, `y`, … it describes the locals of a procedure by name:
  `setLocals [] [(Size, n), (Bound, U), …]`.
* `updateLocals loc [(x, a), (y, b), …]` is the same for locals that are not given as a list.  A
  lemma about a piece of text that several procedures share is stated for arbitrary locals `loc`.
* `refreshLocals l loc xs` is the list `l` with the entries `xs` read from `loc`.
* `LocalsBut xs l loc` says that `loc` agrees with `frame l` except perhaps at the locals `xs`.  In
  an invariant, `xs` are the scratch variables.  `Ends.asFrame` goes from such locals to a list, and
  `LocalsBut.of_eq` comes back.
* `Ends.pieceTo` and `Ends.pieceToThen` use a lemma about a piece of text that assigns only the
  locals `xs`: afterwards the locals are `refreshLocals l loc' xs`, where `loc'` are the locals of
  which the lemma speaks.  The lemma need not mention the locals that the piece does not assign.
* `Ends.forScratch` is the rule for a counting loop whose body may change the scratch variables
  `xs`: the round says nothing about the locals.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## The list of the locals -/







/-- Zeros at the end of the list do not matter. -/
theorem frame_append_zeros (l : List ℤ) (n : ℕ) : _root_.Light.frame (l ++ List.replicate n 0) = _root_.Light.frame l := by
  funext y
  simp only [_root_.Light.frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]

/-! ## The value of an expression -/



/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}

















end rules

/-! ## Locals by name, and locals whose values do not matter -/























section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}







/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q R : _root_.ThreeSum1960614.Machine.Light.State → Prop}







/-! ## Counting loops with scratch variables -/



end

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The remainder of a division

emod(x, M, fr) returns the remainder of the integer x modulo M ≥ 1, a number in 0, …, M - 1.  The
language has no division: the routine writes M, 2M, 4M, … into a table at the free pointer fr as
long as they are at most |x|, subtracts them from |x| from the largest down where possible, and
corrects the sign (`emod_meets`).  With k = `emodRounds |x| M` doublings it takes `emodTime |x| M`
steps, a constant times k + 1, and k cells.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
namespace Emod
open _root_.Light.Emod









end Emod



















/-- There are at most log₂ (V + 1) + 1 doublings for a number up to V. -/
theorem emodRounds_le {a M V : ℕ} (ha : a ≤ V) : _root_.Light.emodRounds a M ≤ Nat.log 2 (V + 1) + 1 := by
  rw [_root_.Light.emodRounds, Nat.size_le]
  calc a / M ≤ a := Nat.div_le_self _ _
    _ < V + 1 := by omega
    _ < 2 ^ (Nat.log 2 (V + 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _


namespace Emod
open _root_.Light.Emod






variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}









end Emod

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Costed signed residue conversion

This loop uses the benchmark's proved division-free remainder procedure.
Its sign argument supports either an ordinary histogram or a histogram of
the negated original integers. All source multiplicities are retained.
The logarithmic scratch region is reused for each input element.
-/

namespace ThreeSum.LightResidues
open _root_.ThreeSum.LightResidues


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}













theorem emodTime_le {x : ℤ} {p U : ℕ} (hx : |x| ≤ (U : ℤ)) :
    _root_.Light.emodTime x.natAbs p ≤ _root_.ThreeSum.LightResidues.residueBudget U := by
  have hU : x.natAbs ≤ U := by simpa only [← Int.natCast_natAbs, Nat.cast_le] using hx
  have h := _root_.ThreeSum1960614.Machine.Light.emodRounds_le (M := p) hU
  unfold _root_.Light.emodTime _root_.ThreeSum.LightResidues.residueBudget
  omega







end ThreeSum.LightResidues

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-input residue keys with a carry offset

The source histogram uses `(x % p + shift) % m`, with two independently
chosen moduli. This procedure computes both remainders from each original
signed input and retains every incidence, including duplicate values.
-/

namespace ThreeSum.LightSourceResidues
open _root_.ThreeSum.LightSourceResidues


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000



theorem key_cast {p m : ℕ} (hm : 0 < m) (shift x : ℤ) :
    (_root_.ThreeSum.LightSourceResidues.key p m shift x : ℤ) = (x % (p : ℤ) + shift) % (m : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))

theorem key_lt {p m : ℕ} (hm : 0 < m) (shift x : ℤ) : _root_.ThreeSum.LightSourceResidues.key p m shift x < m := by
  have h := Int.emod_lt_of_pos (x % (p : ℤ) + shift)
    (by exact_mod_cast hm : (0 : ℤ) < m)
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.key_cast hm] at h
  exact_mod_cast h











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











end ThreeSum.LightSourceResidues

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.ends__implementation_2ad6c62761 {pEmod : ℕ} (hem : P[pEmod]? = some _root_.ThreeSum1960614.Machine.Light.emodBody)
    {μ : ℕ → ℤ} {src dst n p m work U D : ℕ} {shift : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hp : 0 < p) (hm : 0 < m)
    (hsrc : src+n ≤ work) (hdst : dst+n ≤ work)
    (hspace : _root_.ThreeSum.LightSourceResidues.space work p U D ≤ lim.space) (hsep : _root_.Light.Apart src n dst n)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (_root_.ThreeSum.LightSourceResidues.word p m U D : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src+i)| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.body pEmod) ⟨_root_.Light.frame [src,dst,n,p,m,work,shift],μ⟩
      (_root_.ThreeSum.LightSourceResidues.time n p U D) (fun σ =>
        (∀ i < n, σ.mem (dst+i) = (_root_.ThreeSum.LightSourceResidues.key p m shift (μ (src+i)) : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ σ.mem work dst n) := by
  have hspace0 : work+(Nat.log 2 (U+1)+2) ≤ lim.space :=
    (Nat.add_le_add_left (le_max_left _ _) work).trans hspace
  have hspace1 : work+(Nat.log 2 (p+D+1)+2) ≤ lim.space :=
    (Nat.add_le_add_left (le_max_right _ _) work).trans hspace
  have hword0 : (4*U+4*p+16 : ℤ) ≤ lim.word := by
    have hb : 4*U+4*p+16 ≤ _root_.ThreeSum.LightSourceResidues.word p m U D := by unfold _root_.ThreeSum.LightSourceResidues.word; omega
    exact (by exact_mod_cast hb : (4*U+4*p+16 : ℤ) ≤ (word p m U D : ℤ)).trans hword
  have hword1 : (4*(p+D)+4*m+16 : ℤ) ≤ lim.word := by
    have hb : 4*(p+D)+4*m+16 ≤ _root_.ThreeSum.LightSourceResidues.word p m U D := by unfold _root_.ThreeSum.LightSourceResidues.word; omega
    exact (by exact_mod_cast hb : (4*(p+D)+4*m+16 : ℤ) ≤ (word p m U D : ℤ)).trans hword
  have hpre0 : _root_.ThreeSum1960614.Machine.Light.Emod.Pre lim p U work := ⟨hp,hw,hword0,hspace0⟩
  have hpre1 : _root_.ThreeSum1960614.Machine.Light.Emod.Pre lim m (p+D) work := ⟨hm,hw,hword1,hspace1⟩
  have hshift' := abs_le.mp hshift
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.body _root_.ThreeSum.LightSourceResidues.time
  refine _root_.ThreeSum1960614.Machine.Light.Ends.for (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.Inv μ src dst n p m work shift) n
    (_root_.ThreeSum.LightResidues.residueBudget U + _root_.ThreeSum.LightResidues.residueBudget (p+D) + 92)
    ?start ?round ?done ?bound
  case start =>
    refine ⟨0,0,μ,?_,?_,fun _ _ => rfl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : _root_.ThreeSum1960614.Machine.Light.State))
        ((_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal _ _ _).trans (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros _ 2).symm)
    · intro j hj
      omega
  case round =>
    rintro i _ hi _ ⟨r0,r1,ν,rfl,written,kept⟩
    have hread : ν (src+i) = μ (src+i) := kept _ ⟨by omega,by omega⟩
    have hx := hvalues i hi
    have hx' := abs_le.mp hx
    have hmod0 : 0 ≤ μ (src+i) % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
    have hmodp : μ (src+i) % (p : ℤ) < (p : ℤ) :=
      Int.emod_lt_of_pos _ (by exact_mod_cast hp)
    have hsum : |μ (src+i) % (p : ℤ) + shift| ≤ ((p+D : ℕ) : ℤ) := by
      rw [Nat.cast_add]
      exact abs_le.mpr ⟨by omega,by omega⟩
    have hsum' := abs_le.mp hsum
    have htime0 := _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.emodTime_le (p := p) hx
    have htime1 := _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.emodTime_le (p := m) hsum
    unfold _root_.Light.emodTime _root_.ThreeSum.LightResidues.residueBudget at htime0 htime1
    have hlog0 : Nat.log 2 (1+U) = Nat.log 2 (U+1) := by rw [Nat.add_comm]
    have hlog1 : Nat.log 2 (1+(p+D)) = Nat.log 2 (p+D+1) := by rw [Nat.add_comm]
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       first
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.Light.emod_meets (x := μ (src + i)) hem hpre0 hx) _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.Light.emod_meets (x := μ (src + i)) hem hpre0 hx) ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hread, _root_.ThreeSum.LightResidues.residueBudget]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hread, _root_.ThreeSum.LightResidues.residueBudget] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread, _root_.ThreeSum.LightResidues.residueBudget] <;> omega)
       on_goal -1 => (rintro q0 ν₁ ⟨hresult0, hkeep0⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    subst q0
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       first
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.Light.emod_meets (x := μ (src + i) % (p : ℤ) + shift) hem hpre1 hsum) _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.Light.emod_meets (x := μ (src + i) % (p : ℤ) + shift) hem hpre1 hsum) ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightResidues.residueBudget]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightResidues.residueBudget] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightResidues.residueBudget] <;> omega)
       on_goal -1 => (rintro q1 ν₂ ⟨hresult1, hkeep1⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.key_cast hm] at hresult1
    subst q1
    have hlt := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.key_lt (p := p) hm shift (μ (src+i))
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + i) (_root_.ThreeSum.LightSourceResidues.key p m shift (μ (src + i)) : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightResidues.residueBudget]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightResidues.residueBudget] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightResidues.residueBudget] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    refine ⟨by simp,μ (src+i) % (p : ℤ),(_root_.ThreeSum.LightSourceResidues.key p m shift (μ (src+i)) : ℤ),
      Function.update ν₂ (dst+i) (_root_.ThreeSum.LightSourceResidues.key p m shift (μ (src+i)) : ℕ),
      by simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal],?_,?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega)]
        exact (hkeep1 _ (by omega)).trans ((hkeep0 _ (by omega)).trans (written j hj))
      · simp
    · intro a ⟨ha,hout⟩
      rw [Function.update_of_ne (by omega)]
      exact (hkeep1 a ha).trans ((hkeep0 a ha).trans (kept a ⟨ha,hout⟩))
  case done =>
    rintro _ _ ⟨r0,r1,ν,rfl,written,kept⟩
    exact ⟨written,kept⟩
  case bound =>
    rintro i _ _ _ ⟨r0,r1,ν,rfl,_,_⟩
    simp
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.ends__implementation_2ad6c62761) := (@ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.ends__implementation_2ad6c62761)

#print axioms solution
