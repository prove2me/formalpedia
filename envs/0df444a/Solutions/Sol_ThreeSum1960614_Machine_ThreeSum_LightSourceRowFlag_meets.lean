-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:29:01.496416+00:00
-- url     : https://prove2.me/submissions/ffd900e3-f10d-4b0c-974a-e4ee67253e04

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_emod_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceFlagTest_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceRowScan_meets

namespace Finset
end Finset
namespace Light
end Light
namespace Light.Emod
end Light.Emod
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSourceFlagTest
end ThreeSum.LightSourceFlagTest
namespace ThreeSum.LightSourceRowFlag
end ThreeSum.LightSourceRowFlag
namespace ThreeSum.LightSourceRowScan
end ThreeSum.LightSourceRowScan
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Emod
end ThreeSum1960614.Machine.Light.Emod
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest
end ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag
end ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceRowScan
end ThreeSum1960614.Machine.ThreeSum.LightSourceRowScan

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
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Specifications of procedures -/



section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : _root_.ThreeSum1960614.Machine.Light.Stmt}
    (hp : P[p]? = some body)
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d body ⟨_root_.Light.frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩









end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List _root_.ThreeSum1960614.Machine.Light.Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} {s : _root_.ThreeSum1960614.Machine.Light.Stmt}









end

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Independent cardinality-and-bucket trimming test -/

namespace ThreeSum.LightSourceFlagTest
open _root_.ThreeSum.LightSourceFlagTest


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light



theorem flag_le (card required count cap : ℕ) : _root_.ThreeSum.LightSourceFlagTest.flag card required count cap ≤ 1 := by
  unfold _root_.ThreeSum.LightSourceFlagTest.flag
  split <;> omega







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightSourceFlagTest

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Counting and hashing one physical block row

A single scan of the Boolean row constructs its cardinality and both raw
one-hot hashes. The two orientations are accumulated independently from the
stored unscaled map rows. All arithmetic is explicitly word bounded.
-/

namespace ThreeSum.LightSourceRowScan
open _root_.ThreeSum.LightSourceRowScan


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000












theorem count_le {L j : ℕ} (bits : ℕ → ℕ) (hb : ∀ i < L, bits i ≤ 1) (hj : j ≤ L) :
    _root_.ThreeSum.LightSourceRowScan.count bits j ≤ j := by
  unfold _root_.ThreeSum.LightSourceRowScan.count
  calc
    _ ≤ ∑ _i ∈ range j, (1 : ℕ) :=
      Finset.sum_le_sum (fun i hi => hb i ((mem_range.mp hi).trans_le hj))
    _ = j := by simp

theorem hash_le {L j U : ℕ} (bits w0 w1 : ℕ → ℕ)
    (h0 : ∀ i < L, w0 i ≤ U) (h1 : ∀ i < L, w1 i ≤ U) (hj : j ≤ L) :
    _root_.ThreeSum.LightSourceRowScan.hash bits w0 w1 j ≤ j*U := by
  unfold _root_.ThreeSum.LightSourceRowScan.hash
  calc
    _ ≤ ∑ _i ∈ range j, U := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := (mem_range.mp hi).trans_le hj
      split
      · exact h1 i hi'
      · exact h0 i hi'
    _ = j*U := by simp








variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightSourceRowScan

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



theorem residue_cast {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (_root_.ThreeSum.LightResidues.residue p c x : ℤ) = (c * x) % (p : ℤ) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast hp.ne')

theorem residue_lt {p : ℕ} (hp : 0 < p) (c x : ℤ) : _root_.ThreeSum.LightResidues.residue p c x < p := by
  have h := Int.emod_lt_of_pos (c * x) (by exact_mod_cast hp : (0 : ℤ) < p)
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hp] at h
  exact_mod_cast h







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
# Constructing both independent trimming flags for one block row

The program counts and hashes the actual Boolean row, reduces both local
hashes, reads the selected map's retained bucket tables, and independently
tests the two endpoint buckets. The cardinality test is performed for both
orientations, with no disjoint-pair or shared trimming assumption.
-/

namespace ThreeSum.LightSourceRowFlag
open _root_.ThreeSum.LightSourceRowFlag


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000



theorem flag_le (L h p cap : ℕ) (bits w0 w1 hist : ℕ → ℕ) :
    _root_.ThreeSum.LightSourceRowFlag.flag L h p cap bits w0 w1 hist ≤ 1 := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest.flag_le ..









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







end ThreeSum.LightSourceRowFlag

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceRowFlag
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag.meets__implementation_787ec2dea7 {pMain pRow pEmod pFlag : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag.body pRow pEmod pFlag))
    (hrow : P[pRow]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowScan.body)
    (hem : P[pEmod]? = some _root_.ThreeSum1960614.Machine.Light.emodBody)
    (hflag : P[pFlag]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest.body)
    {μ : ℕ → ℤ} {src src0 src1 L h histL histR p cap dst work U V : ℕ}
    (bits w0 w1 leftCount rightCount : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hp : 0 < p) (hh : h ≤ L)
    (hsrc : src+L ≤ work) (hsrc0 : src0+L ≤ work) (hsrc1 : src1+L ≤ work)
    (hleft : histL+p ≤ work) (hright : histR+p ≤ work) (hdst : dst+2 ≤ work)
    (hspace : _root_.ThreeSum.LightSourceRowFlag.space work L U ≤ lim.space) (hword : (_root_.ThreeSum.LightSourceRowFlag.word L p U V cap : ℤ) ≤ lim.word)
    (hbits : ∀ i < L, μ (src+i) = (bits i : ℤ))
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbitBound : ∀ i < L, bits i ≤ 1)
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U)
    (hcountL : ∀ r < p, μ (histL+r) = (leftCount r : ℤ))
    (hcountR : ∀ r < p, μ (histR+r) = (rightCount r : ℤ))
    (hcountBoundL : ∀ r < p, leftCount r ≤ V)
    (hcountBoundR : ∀ r < p, rightCount r ≤ V) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,src0,src1,L,h,histL,histR,p,cap,dst,work] μ (_root_.ThreeSum.LightSourceRowFlag.time L U)
      (fun _ ν => ν dst = (_root_.ThreeSum.LightSourceRowFlag.flag L h p cap bits w0 w1 leftCount : ℤ) ∧
        ν (dst+1) = (_root_.ThreeSum.LightSourceRowFlag.flag L h p cap bits w1 w0 rightCount : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν work dst 2) := by
  have hsp : work+3+(Nat.log 2 (L*U+1)+2) ≤ lim.space := hspace
  have hbudget (x : ℕ) (hx : x ≤ _root_.ThreeSum.LightSourceRowFlag.word L p U V cap) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hrowWord := hbudget (_root_.ThreeSum.LightSourceRowScan.word L U) (by unfold _root_.ThreeSum.LightSourceRowFlag.word; omega)
  have hemWord : (4*(L*U : ℕ)+4*p+16 : ℤ) ≤ lim.word := by
    have hh := hbudget (4*(L*U)+4*p+16) (by unfold _root_.ThreeSum.LightSourceRowFlag.word; omega)
    exact_mod_cast hh
  have hpre : _root_.ThreeSum1960614.Machine.Light.Emod.Pre lim p (L*U) (work+3) := ⟨hp,hw,hemWord,hsp⟩
  have hcBound := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowScan.count_le bits hbitBound (j := L) le_rfl
  have hlBound := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowScan.hash_le bits w0 w1 hbound0 hbound1 (j := L) le_rfl
  have hrBound := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowScan.hash_le bits w1 w0 hbound1 hbound0 (j := L) le_rfl
  have hlAbs : |(_root_.ThreeSum.LightSourceRowScan.hash bits w0 w1 L : ℤ)| ≤ ((L*U : ℕ) : ℤ) := by
    rw [Int.abs_natCast]
    exact Int.ofNat_le.mpr hlBound
  have hrAbs : |(_root_.ThreeSum.LightSourceRowScan.hash bits w1 w0 L : ℤ)| ≤ ((L*U : ℕ) : ℤ) := by
    rw [Int.abs_natCast]
    exact Int.ofNat_le.mpr hrBound
  have htimeL := _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.emodTime_le (p := p) hlAbs
  have htimeR := _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.emodTime_le (p := p) hrAbs
  unfold _root_.Light.emodTime _root_.ThreeSum.LightResidues.residueBudget at htimeL htimeR
  simp only [Int.natAbs_natCast] at htimeL htimeR
  have hlog : Nat.log 2 (1+L*U) = Nat.log 2 (L*U+1) := by rw [Nat.add_comm]
  have hlLt := _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_lt hp 1 (_root_.ThreeSum.LightSourceRowScan.hash bits w0 w1 L : ℤ)
  have hrLt := _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_lt hp 1 (_root_.ThreeSum.LightSourceRowScan.hash bits w1 w0 L : ℤ)
  have hlCast := _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hp 1 (_root_.ThreeSum.LightSourceRowScan.hash bits w0 w1 L : ℤ)
  have hrCast := _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hp 1 (_root_.ThreeSum.LightSourceRowScan.hash bits w1 w0 L : ℤ)
  simp only [one_mul] at hlCast hrCast
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag.body _root_.ThreeSum.LightSourceRowFlag.time
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowScan.meets (d := d+1) (μ := μ) (src := src)
    (src0 := src0) (src1 := src1) (L := L) (dst := work) (U := U)
    hrow bits w0 w1 hw (by omega) (by omega) (by omega) (by omega) hrowWord
    hbits hread0 hread1 hbitBound hbound0 hbound1
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hr _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hr ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;> omega)
     on_goal -1 => (rintro q ν₁ ⟨cardRead, leftRead, rightRead, kept₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.Light.emod_meets (x := (_root_.ThreeSum.LightSourceRowScan.hash bits w0 w1 L : ℤ)) hem hpre hlAbs) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.Light.emod_meets (x := (_root_.ThreeSum.LightSourceRowScan.hash bits w0 w1 L : ℤ)) hem hpre hlAbs) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, leftRead, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [leftRead, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, leftRead, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;> omega)
     on_goal -1 => (rintro l ν₂ ⟨lResult, kept₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  rw [← hlCast] at lResult
  subst l
  have rightRead₂ : ν₂ (work+2) = (_root_.ThreeSum.LightSourceRowScan.hash bits w1 w0 L : ℤ) :=
    (kept₂ _ (by omega)).trans rightRead
  have rightAddr : ((work : ℤ)+2).toNat = work+2 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using (Int.toNat_natCast (work+2))
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.Light.emod_meets (x := (_root_.ThreeSum.LightSourceRowScan.hash bits w1 w0 L : ℤ)) hem hpre hrAbs) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.Light.emod_meets (x := (_root_.ThreeSum.LightSourceRowScan.hash bits w1 w0 L : ℤ)) hem hpre hrAbs) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, rightRead₂, rightAddr, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [rightRead₂, rightAddr, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, rightRead₂, rightAddr, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;> omega)
     on_goal -1 => (rintro r ν₃ ⟨rResult, kept₃⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  rw [← hrCast] at rResult
  subst r
  have cardRead₃ : ν₃ work = (_root_.ThreeSum.LightSourceRowScan.count bits L : ℤ) :=
    (kept₃ _ (by omega)).trans ((kept₂ _ (by omega)).trans cardRead)
  have countLRead : ν₃ (histL+_root_.ThreeSum.LightResidues.residue p 1
      (_root_.ThreeSum.LightSourceRowScan.hash bits w0 w1 L : ℤ)) =
      (leftCount (_root_.ThreeSum.LightResidues.residue p 1 (_root_.ThreeSum.LightSourceRowScan.hash bits w0 w1 L : ℤ)) : ℤ) :=
    (kept₃ _ (by omega)).trans ((kept₂ _ (by omega)).trans
      ((kept₁ _ (Or.inl (by omega))).trans (hcountL _ hlLt)))
  have countRRead : ν₃ (histR+_root_.ThreeSum.LightResidues.residue p 1
      (_root_.ThreeSum.LightSourceRowScan.hash bits w1 w0 L : ℤ)) =
      (rightCount (_root_.ThreeSum.LightResidues.residue p 1 (_root_.ThreeSum.LightSourceRowScan.hash bits w1 w0 L : ℤ)) : ℤ) :=
    (kept₃ _ (by omega)).trans ((kept₂ _ (by omega)).trans
      ((kept₁ _ (Or.inl (by omega))).trans (hcountR _ hrLt)))
  have hflagWordL := hbudget (_root_.ThreeSum.LightSourceRowScan.count bits L+h+
    leftCount (_root_.ThreeSum.LightResidues.residue p 1 (_root_.ThreeSum.LightSourceRowScan.hash bits w0 w1 L : ℤ))+cap+2)
    (by have := hcountBoundL _ hlLt; unfold _root_.ThreeSum.LightSourceRowFlag.word; omega)
  have hflagWordR := hbudget (_root_.ThreeSum.LightSourceRowScan.count bits L+h+
    rightCount (_root_.ThreeSum.LightResidues.residue p 1 (_root_.ThreeSum.LightSourceRowScan.hash bits w1 w0 L : ℤ))+cap+2)
    (by have := hcountBoundR _ hrLt; unfold _root_.ThreeSum.LightSourceRowFlag.word; omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest.meets (d := d + 1) hflag ν₃ hflagWordL) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest.meets (d := d + 1) hflag ν₃ hflagWordL) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, cardRead₃, countLRead, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [cardRead₃, countLRead, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, cardRead₃, countLRead, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;> omega)
     on_goal -1 => (rintro fl ν₄ ⟨flResult, hmem₄⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst ν₄
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest.meets (d := d + 1) hflag ν₃ hflagWordR) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest.meets (d := d + 1) hflag ν₃ hflagWordR) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, cardRead₃, countRRead, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [cardRead₃, countRRead, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, cardRead₃, countRRead, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;> omega)
     on_goal -1 => (rintro fr ν₅ ⟨frResult, hmem₅⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst ν₅
  have flEq : fl = (_root_.ThreeSum.LightSourceRowFlag.flag L h p cap bits w0 w1 leftCount : ℤ) := flResult
  have frEq : fr = (_root_.ThreeSum.LightSourceRowFlag.flag L h p cap bits w1 w0 rightCount : ℤ) := frResult
  have flBound := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag.flag_le L h p cap bits w0 w1 leftCount
  have frBound := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag.flag_le L h p cap bits w1 w0 rightCount
  have h1 := hbudget 1 (by unfold _root_.ThreeSum.LightSourceRowFlag.word; omega)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen dst (_root_.ThreeSum.LightSourceRowFlag.flag L h p cap bits w0 w1 leftCount : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, flEq, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [flEq, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, flEq, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 1) (_root_.ThreeSum.LightSourceRowFlag.flag L h p cap bits w1 w0 rightCount : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, frEq, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [frEq, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, frEq, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine ⟨by simp,by simp,?_⟩
  intro a ⟨ha,hout⟩
  simp only [Function.update_of_ne (show a ≠ dst+1 by omega),
    Function.update_of_ne (show a ≠ dst by omega)]
  exact (kept₃ a (by omega)).trans ((kept₂ a (by omega)).trans (kept₁ a (Or.inl ha)))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag.meets__implementation_787ec2dea7) := (@ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag.meets__implementation_787ec2dea7)

#print axioms solution
