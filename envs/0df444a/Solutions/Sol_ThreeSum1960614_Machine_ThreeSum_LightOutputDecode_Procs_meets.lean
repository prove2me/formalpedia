-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightOutputDecode.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:28:07.148331+00:00
-- url     : https://prove2.me/submissions/937d3b57-16b3-4c1c-ad03-88016c30fc5f

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightOutputDecodeDigits_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightOutputDecodeStep_meets
import Theorems.Thm_ThreeSum_OutputDecodeOrder_indices_getD_reverse

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightOutputDecode
end ThreeSum.LightOutputDecode
namespace ThreeSum.LightOutputDecodeStep
end ThreeSum.LightOutputDecodeStep
namespace ThreeSum.OutputDecodeOccurrenceCode
end ThreeSum.OutputDecodeOccurrenceCode
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightOutputDecode
end ThreeSum1960614.Machine.ThreeSum.LightOutputDecode
namespace ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeStep
end ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeStep
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords

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

/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩







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

/-! # Occurrence-only source-bank indices, with first block most significant -/

namespace ThreeSum.OutputDecodeOccurrenceCode
open _root_.ThreeSum.OutputDecodeOccurrenceCode


open _root_.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding

set_option maxHeartbeats 1500000



theorem last_lt {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (k : ℕ) :
    (k%(T*M))/M < T :=
  (Nat.div_lt_iff_lt_mul hM).mpr (Nat.mod_lt _ (Nat.mul_pos hT hM))

theorem code_lt {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (J k : ℕ) : _root_.ThreeSum.OutputDecodeOccurrenceCode.code T M J k < T^J := by
  induction J generalizing k with
  | zero => simp [_root_.ThreeSum.OutputDecodeOccurrenceCode.code]
  | succ J ih =>
    have hm := Nat.mul_le_mul_left T (show _root_.ThreeSum.OutputDecodeOccurrenceCode.code T M J (k/(T*M))+1 ≤ T^J by exact ih _)
    have hd := _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode.last_lt hT hM k
    simp only [Nat.mul_add,Nat.mul_one] at hm
    rw [_root_.ThreeSum.OutputDecodeOccurrenceCode.code,pow_succ']
    omega

theorem code_step (T M i k : ℕ) :
    _root_.ThreeSum.OutputDecodeOccurrenceCode.code T M (i+1) k = _root_.ThreeSum.OutputDecodeOccurrenceCode.code T M i k+T^i*((k/(T*M)^i)%(T*M)/M) := by
  induction i generalizing k with
  | zero => simp [_root_.ThreeSum.OutputDecodeOccurrenceCode.code]
  | succ i ih =>
    change (k%(T*M))/M+T*_root_.ThreeSum.OutputDecodeOccurrenceCode.code T M (i+1) (k/(T*M)) =
      ((k%(T*M))/M+T*_root_.ThreeSum.OutputDecodeOccurrenceCode.code T M i (k/(T*M)))+T^(i+1)*((k/(T*M)^(i+1))%(T*M)/M)
    rw [ih,Nat.div_div_eq_div_mul,pow_succ',pow_succ']
    ring







end ThreeSum.OutputDecodeOccurrenceCode

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# One actual output-record decoding step

A local record digit is split into its occurrence and layer indices by
the checked logarithmic quotient routine. The layer mask is read from the
existing table, both output cells are written, and the occurrence-only
source-bank code is updated. Every other cell below the scratch pointer
is preserved, so separate output rows can be filled in any order.
-/

namespace ThreeSum.LightOutputDecodeStep
open _root_.ThreeSum.LightOutputDecodeStep


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 7000











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {x T M masks acc power outOcc outMask work V U : ℕ} {f : ℕ → ℕ}







theorem meets_code_step {pMain pDivide k i : ℕ}
    (hmain : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeStep.body pDivide))
    (hdivide : P[pDivide]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide.body)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hT : 1 ≤ T) (hM : 1 ≤ M)
    (hx : x=(k/(T*M)^i)%(T*M))
    (ha : acc=_root_.ThreeSum.OutputDecodeOccurrenceCode.code T M i k) (hp : power=T^i)
    (hxV : x ≤ V) (hmask : masks+M ≤ work)
    (hocc : outOcc < work) (hout : outMask < work) (hne : outOcc ≠ outMask)
    (hspace : _root_.ThreeSum.LightOutputDecodeStep.space work V ≤ lim.space)
    (hword : (_root_.ThreeSum.LightOutputDecodeStep.word V T M acc power U : ℤ) ≤ lim.word)
    (hf : ∀ s < M, f s ≤ U) (hread : ∀ s < M, μ (masks+s)=(f s : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [x,T,M,masks,acc,power,outOcc,outMask,work] μ (_root_.ThreeSum.LightOutputDecodeStep.time V)
      (fun r ν => r=(_root_.ThreeSum.OutputDecodeOccurrenceCode.code T M (i+1) k : ℤ) ∧
        ν outOcc=((x/M : ℕ) : ℤ) ∧ ν outMask=(f (x%M) : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeStep.KeptOthers μ ν work outOcc outMask) := by
  have hxlt : x < T*M := by rw [hx]; exact Nat.mod_lt _ (Nat.mul_pos hT hM)
  refine (_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeStep.meets hmain hdivide hw hd hT hM hxlt hxV hmask hocc hout hne hspace hword hf hread).mono le_rfl ?_
  rintro r ν ⟨hr,hocc',hmask',hk⟩
  refine ⟨?_,hocc',hmask',hk⟩
  rw [hr,ha,hp,hx,_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode.code_step]

end ThreeSum.LightOutputDecodeStep

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightOutputDecode
open _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecode

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {k J T M masks dst work V U : ℕ} {f : ℕ → ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightOutputDecode.Procs.meets__implementation_dcf315a21b {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecode.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hT : 1 ≤ T) (hM : 1 ≤ M) (hk : k ≤ V)
    (hmask : masks+M ≤ dst) (hsep : dst+J+J ≤ work)
    (hspace : _root_.ThreeSum.LightOutputDecode.space work V ≤ lim.space)
    (hword : (_root_.ThreeSum.LightOutputDecode.word V T M J U : ℤ) ≤ lim.word)
    (hf : ∀ s < M, f s ≤ U) (hread : ∀ s < M, μ (masks+s)=(f s : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [k,J,T,M,masks,dst,work] μ (_root_.ThreeSum.LightOutputDecode.time J V)
      (fun r ν => r=(_root_.ThreeSum.OutputDecodeOccurrenceCode.code T M J k : ℤ) ∧
        (∀ j < J, ν (dst+j)=(((_root_.ThreeSum.OutputDecodeOrder.indices (T*M) J k).getD j 0/M : ℕ) : ℤ)) ∧
        (∀ j < J, ν (dst+J+j)=(f ((_root_.ThreeSum.OutputDecodeOrder.indices (T*M) J k).getD j 0%M) : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst) := by
  have hbudget (a : ℕ) (ha : a ≤ _root_.ThreeSum.LightOutputDecode.word V T M J U) : (a : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ha).trans hword
  have hVWord := hbudget V (by unfold _root_.ThreeSum.LightOutputDecode.word; omega)
  have hkWord : (k : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hk).trans hVWord
  have hTWord := hbudget T (by unfold _root_.ThreeSum.LightOutputDecode.word; omega)
  have hMWord := hbudget M (by unfold _root_.ThreeSum.LightOutputDecode.word; omega)
  have hTMWord := hbudget (T*M) (by unfold _root_.ThreeSum.LightOutputDecode.word; omega)
  have hTMWord' : (T : ℤ)*(M : ℤ) ≤ lim.word := by exact_mod_cast hTMWord
  have hJWord := hbudget J (by unfold _root_.ThreeSum.LightOutputDecode.word; omega)
  have hpowerWord := hbudget (T^J) (by unfold _root_.ThreeSum.LightOutputDecode.word; omega)
  have h1Word := hbudget 1 (by unfold _root_.ThreeSum.LightOutputDecode.word; omega)
  have hwork : work ≤ lim.space := by unfold _root_.ThreeSum.LightOutputDecode.space at hspace; omega
  have hdigitsWord := hbudget (_root_.ThreeSum.LightOutputDecodeDigits.word V (T*M) J)
    (by unfold _root_.ThreeSum.LightOutputDecodeDigits.word _root_.ThreeSum.LightOutputDecode.word; omega)
  have hTM : 1 ≤ T*M := Nat.mul_pos hT hM
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body S.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecode.body _root_.ThreeSum.LightOutputDecode.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (T * M : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
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
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDigits.meets (d := d + 1) (μ := μ) (dst := dst) (work := work) S.digits S.divide hw (by omega) hTM hk (by omega) hspace hdigitsWord) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDigits.meets (d := d + 1) (μ := μ) (dst := dst) (work := work) S.digits S.divide hw (by omega) hTM hk (by omega) hspace hdigitsWord) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     on_goal -1 => (rintro q ν ⟨hq, digits, kept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (1 : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine _root_.ThreeSum1960614.Machine.Light.Ends.pieceThen (_root_.ThreeSum1960614.Machine.Light.Ends.for
    (T := J*(_root_.ThreeSum.LightOutputDecodeStep.time V+100)+6)
    (Q := _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecode.Inv μ k J T M masks dst work q f J)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecode.Inv μ k J T M masks dst work q f) J
    (_root_.ThreeSum.LightOutputDecodeStep.time V+92) ?start ?round ?done ?bound) ?finish
  case start =>
    refine ⟨0,ν,?_,?_,?_,kept⟩
    · simp only [_root_.ThreeSum.OutputDecodeOccurrenceCode.code,pow_zero]
      simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
      exact (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros [k,J,T,M,masks,dst,work,T*M,q,0,1,0] 1).symm
    · intro j _ hj
      have hr := _root_.ThreeSum.OutputDecodeOrder.indices_getD_reverse (T*M) J k hj
      have he := digits (J-1-j) (by omega)
      have ha : dst+(J-1-j)=dst+J-1-j := by omega
      simpa only [hr,ha] using he
    · intro j hj; omega
  case round =>
    rintro i _ hi _ ⟨x,ν',rfl,remaining,written,kept'⟩
    have hpow : T^i ≤ T^J := Nat.pow_le_pow_right hT (by omega)
    have hpowNext : T^(i+1) ≤ T^J := Nat.pow_le_pow_right hT (by omega)
    have hcode := _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode.code_lt hT hM i k
    have hcurrent : (k/(T*M)^i)%(T*M) ≤ V :=
      (Nat.mod_le _ _).trans ((Nat.div_le_self _ _).trans hk)
    have hcurrentWord : (((k/(T*M)^i)%(T*M) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr hcurrent).trans hVWord
    have haccWord : (_root_.ThreeSum.OutputDecodeOccurrenceCode.code T M i k : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (hcode.le.trans hpow)).trans hpowerWord
    have hpowWord : ((T^i : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr hpow).trans hpowerWord
    have hnextWord : ((T^(i+1) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr hpowNext).trans hpowerWord
    have hnextWord' : (T : ℤ)^i*(T : ℤ) ≤ lim.word := by
      rw [← pow_succ]
      exact_mod_cast hnextWord
    have hnextNonneg : (0 : ℤ) ≤ (T : ℤ)^i*(T : ℤ) := by positivity
    have hstepWord := hbudget
      (_root_.ThreeSum.LightOutputDecodeStep.word V T M (_root_.ThreeSum.OutputDecodeOccurrenceCode.code T M i k) (T^i) U)
      (by unfold _root_.ThreeSum.LightOutputDecodeStep.word _root_.ThreeSum.LightOutputDecode.word; rw [← pow_succ]; omega)
    have haddr : (dst : ℤ)+(J : ℤ)-1-(i : ℤ)=((dst+J-1-i : ℕ) : ℤ) := by omega
    have haddrMask : (dst : ℤ)+(J : ℤ)+(J : ℤ)-1-(i : ℤ)=
        ((dst+J+J-1-i : ℕ) : ℤ) := by omega
    have hmaskRead : ∀ s < M, ν' (masks+s)=(f s : ℤ) := by
      intro s hs
      rw [kept' _ (by omega)]
      exact hread s hs
    have hxRead := remaining i le_rfl hi
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen ((k / (T * M) ^ i) % (T * M) : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, haddr, hxRead]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [haddr, hxRead] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haddr, hxRead] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    have hcall := _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeStep.meets_code_step (d := d+1)
      (x := (k/(T*M)^i)%(T*M)) (acc := _root_.ThreeSum.OutputDecodeOccurrenceCode.code T M i k)
      (power := T^i) (outOcc := dst+J-1-i) (outMask := dst+J+J-1-i)
      S.step S.divide hw (by omega) hT hM rfl rfl rfl hcurrent
      (by omega) (by omega) (by omega) (by omega) hspace hstepWord hf hmaskRead
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcall ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, haddr, haddrMask]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [haddr, haddrMask] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haddr, haddrMask] <;> omega)
       on_goal -1 => (rintro value ν₁ ⟨hv, hocc, hout, hkept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (T ^ (i + 1) : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, pow_succ]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [pow_succ] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, pow_succ] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    refine ⟨by simp,((k/(T*M)^i)%(T*M) : ℕ),ν₁,?_,?_,?_,?_⟩
    · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal,hv]
    · intro j hij hj
      rw [hkept _ ⟨by omega,by omega,by omega⟩]
      exact remaining j (by omega) hj
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · constructor
        · rw [hkept _ ⟨by omega,by omega,by omega⟩]
          exact (written j hj).1
        · rw [hkept _ ⟨by omega,by omega,by omega⟩]
          exact (written j hj).2
      · exact ⟨hocc,hout⟩
    · intro a ha
      rw [hkept a ⟨by omega,by omega,by omega⟩,kept' a ha]
  case done =>
    rintro _ _ ⟨x,ν',rfl,remaining,written,kept'⟩
    exact ⟨x,ν',rfl,remaining,written,kept'⟩
  case bound =>
    rintro i _ _ _ ⟨x,ν',rfl,_,_,_⟩
    (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
  case finish =>
    rintro _ ⟨x,ν',rfl,_,written,kept'⟩
    have hc := _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode.code_lt hT hM J k
    have hcWord : (_root_.ThreeSum.OutputDecodeOccurrenceCode.code T M J k : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr hc.le).trans hpowerWord
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.OutputDecodeOccurrenceCode.code T M J k : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    refine ⟨rfl,?_,?_,kept'⟩
    · intro j hj
      have ht : J-1-j < J := by omega
      have hdigit := _root_.ThreeSum.OutputDecodeOrder.indices_getD_reverse (T*M) J k ht
      have he := (written (J-1-j) ht).1
      have hcoord : J-1-(J-1-j)=j := by omega
      have haddr : dst+J-1-(J-1-j)=dst+j := by omega
      rw [hcoord] at hdigit
      simpa only [haddr,hdigit] using he
    · intro j hj
      have ht : J-1-j < J := by omega
      have hdigit := _root_.ThreeSum.OutputDecodeOrder.indices_getD_reverse (T*M) J k ht
      have he := (written (J-1-j) ht).2
      have hcoord : J-1-(J-1-j)=j := by omega
      have haddr : dst+J+J-1-(J-1-j)=dst+J+j := by omega
      rw [hcoord] at hdigit
      simpa only [haddr,hdigit] using he
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightOutputDecode.Procs.meets__implementation_dcf315a21b) := (@ThreeSum1960614.Machine.ThreeSum.LightOutputDecode.Procs.meets__implementation_dcf315a21b)

#print axioms solution
