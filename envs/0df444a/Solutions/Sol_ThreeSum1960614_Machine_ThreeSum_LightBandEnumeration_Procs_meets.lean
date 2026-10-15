-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:44:34.806981+00:00
-- url     : https://prove2.me/submissions/12a343d7-58b7-4265-8872-b3a8131cbe26

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_clog2_meets
import Theorems.Thm_ThreeSum1960614_Machine_Light_powTable_ends
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandTable_meets
import Theorems.Thm_ThreeSum_KaratsubaInterface_capacity_lt_twice

namespace Light
end Light
namespace Light.PowTable
end Light.PowTable
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.LightBandEnumeration
end ThreeSum.LightBandEnumeration
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.PowTable
end ThreeSum1960614.Machine.Light.PowTable
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

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

/-!
# Tables of powers

powTable(dst, L, b) writes 1, b, b², …, b^(L-1) into the L cells from dst and changes nothing else,
within `powTableTime L` steps (`powTable_meets`).  The list of these powers is `powList b L`.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



@[simp] theorem length_powList (b L : ℕ) : (_root_.Light.powList b L).length = L := by simp [_root_.Light.powList]

@[simp] theorem getElem_powList {b L j : ℕ} (h : j < (_root_.Light.powList b L).length) :
    (_root_.Light.powList b L)[j] = ((b ^ j : ℕ) : ℤ) := by
  simp [_root_.Light.powList]

namespace PowTable
open _root_.Light.PowTable








end PowTable

open _root_.Light.PowTable
open _root_.ThreeSum1960614.Machine.Light.PowTable











/-- **powTable(dst, L, b)** writes the powers 1, b, …, b^(L-1) into the L cells from dst and changes
nothing else. -/
theorem powTable_meets {p : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody) {μ : ℕ → ℤ} {dst L b : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + L ≤ lim.space)
    (hpow : ∀ j ≤ L, ((b ^ j : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [(dst : ℤ), L, b] μ (_root_.Light.powTableTime L) fun _ μ' =>
      _root_.ThreeSum1960614.Machine.Light.Seg μ' dst (_root_.Light.powList b L) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst L :=
  -- the local variables that are no arguments hold 0
  _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros [(dst : ℤ), L, b] 2 ▸ _root_.ThreeSum1960614.Machine.Light.powTable_ends 0 0 [] hw hdst hpow)

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Machine evaluation of compact subset addresses

The current width decreases by one in each recursive call. Its highest
power of two is read from a table, so neither division nor a loop proportional
to the numeric bit-mask value occurs. Pascal coefficients are single reads
from the constructed rectangular table.
-/

namespace ThreeSum.LightSubsetAddress
open _root_.ThreeSum.LightSubsetAddress


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}



theorem powers_of_segment {μ : ℕ → ℤ} {base W : ℕ}
    (h : _root_.ThreeSum1960614.Machine.Light.Seg μ base (_root_.Light.powList 2 (W+1))) : _root_.ThreeSum.LightSubsetAddress.Powers μ base W := by
  intro i hi
  have hs := h i (by simp; omega)
  simpa only [_root_.ThreeSum1960614.Machine.Light.getElem_powList] using hs













end ThreeSum.LightSubsetAddress

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A closed machine program listing all relevant sorted-band candidates

The program computes its own binary width and power table, then executes
exactly the three rectangular owner tables. Every table cell contains an
interval lookup result (index plus one, zero for a miss). The source arrays
remain intact. The coverage theorem below connects these actual memory cells
to every relevant triple, and hence to every exact equation in the bands.
-/

namespace ThreeSum.LightBandEnumeration
open _root_.ThreeSum.LightBandEnumeration


set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}





theorem At.keep {μ μ' : ℕ → ℤ} {lo hi bound : ℕ} {A : _root_.ThreeSum.BandEnumeration.Family}
    (h : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.At μ lo hi A) (hk : _root_.ThreeSum1960614.Machine.Light.Kept μ μ' bound)
    (hlo : lo+A.size ≤ bound) (hhi : hi+A.size ≤ bound) : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.At μ' lo hi A := by
  constructor
  · intro i hi
    rw [hk (lo+i) (by omega)]
    exact h.1 i hi
  · intro i hi'
    rw [hk (hi+i) (by omega)]
    exact h.2 i hi'












































end ThreeSum.LightBandEnumeration

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration

set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Procs.meets__implementation_4d0d2d7504 {pMain al ah bl bh cl ch dst U d : ℕ} {μ : ℕ → ℤ}
    (R : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Procs P pMain) (A B C : _root_.ThreeSum.BandEnumeration.Family)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hal : al+A.size ≤ dst) (hah : ah+A.size ≤ dst)
    (hbl : bl+B.size ≤ dst) (hbh : bh+B.size ≤ dst)
    (hcl : cl+C.size ≤ dst) (hch : ch+C.size ≤ dst)
    (hspace : _root_.ThreeSum.LightBandEnumeration.space dst A.size B.size C.size ≤ lim.space)
    (hword : (_root_.ThreeSum.LightBandEnumeration.word A.size B.size C.size U : ℤ) ≤ lim.word)
    (hd : d+_root_.ThreeSum.LightBandEnumeration.width A.size B.size C.size+4 ≤ lim.depth)
    (hA : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.At μ al ah A) (hB : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.At μ bl bh B) (hC : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.At μ cl ch C)
    (hAU : _root_.ThreeSum.LightBandEnumeration.Bounded A U) (hBU : _root_.ThreeSum.LightBandEnumeration.Bounded B U) (hCU : _root_.ThreeSum.LightBandEnumeration.Bounded C U) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [al,ah,bl,bh,cl,ch,A.size,B.size,C.size,dst] μ
      (_root_.ThreeSum.LightBandEnumeration.time A.size B.size C.size)
      (fun r μ' => r = (_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Tables μ' dst A B C ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' dst) := by
  let N := A.size+B.size+C.size
  let W := _root_.ThreeSum.LightBandEnumeration.width A.size B.size C.size
  let bc := B.size*C.size
  let ab := A.size*B.size
  let ac := A.size*C.size
  let outAB := dst+bc
  let outAC := outAB+ab
  let powers := outAC+ac
  have hNdef : N = A.size+B.size+C.size := rfl
  have hWdef : W = Nat.clog 2 (N+1) := rfl
  have hspace' : powers+(W+1) ≤ lim.space := by
    simpa [powers,outAC,outAB,bc,ab,ac,W,_root_.ThreeSum.LightBandEnumeration.space,_root_.ThreeSum.LightBandEnumeration.count,Nat.add_assoc] using hspace
  have hWWord : ((_root_.ThreeSum.LightBandEnumeration.width A.size B.size C.size+1 : ℕ) : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (by change W+1 ≤ lim.space; omega)).trans hw
  have hwidthN : Nat.clog 2 (N+1) = _root_.ThreeSum.LightBandEnumeration.width A.size B.size C.size := rfl
  have hcapacity : 2^W < 2*(N+1) := by
    exact _root_.ThreeSum.KaratsubaInterface.capacity_lt_twice (p := N+1) (by omega)
  have hpow : 2^(W+1) < 4*(N+1) := by rw [pow_succ]; omega
  have hN : N < 2^W := by
    have hp : N+1 ≤ 2^W := Nat.le_pow_clog (by decide) _
    omega
  have hlookupWord : ((N+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word := by
    have hn : N+2^(W+1)+16 ≤ _root_.ThreeSum.LightBandEnumeration.word A.size B.size C.size U := by
      unfold _root_.ThreeSum.LightBandEnumeration.word N at *
      omega
    exact (Int.ofNat_le.mpr hn).trans hword
  have hwordA : ((A.size+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by dsimp [N]; omega)).trans hlookupWord
  have hwordB : ((B.size+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by dsimp [N]; omega)).trans hlookupWord
  have hwordC : ((C.size+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by dsimp [N]; omega)).trans hlookupWord
  have hqueryWord : 2*(U : ℤ) ≤ lim.word := by
    have hh : 2*U ≤ _root_.ThreeSum.LightBandEnumeration.word A.size B.size C.size U := by unfold _root_.ThreeSum.LightBandEnumeration.word; omega
    exact (by exact_mod_cast hh : 2*(U : ℤ) ≤ (word A.size B.size C.size U : ℤ)).trans hword
  have hlogWord : ((2*(N+1)+1 : ℕ) : ℤ) ≤ lim.word := by
    have hh : 2*(N+1)+1 ≤ _root_.ThreeSum.LightBandEnumeration.word A.size B.size C.size U := by unfold _root_.ThreeSum.LightBandEnumeration.word N; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hpowWord (j : ℕ) (hj : j ≤ W+1) : ((2^j : ℕ) : ℤ) ≤ lim.word := by
    have hh : 2^j ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) hj
    exact (Int.ofNat_le.mpr (by omega : 2^j ≤ N+2^(W+1)+16)).trans hlookupWord
  have hbcNonneg : (0 : ℤ) ≤ (B.size : ℤ)*(C.size : ℤ) := by positivity
  have habNonneg : (0 : ℤ) ≤ (A.size : ℤ)*(B.size : ℤ) := by positivity
  have hacNonneg : (0 : ℤ) ≤ (A.size : ℤ)*(C.size : ℤ) := by positivity
  have hbcWord : (B.size : ℤ)*(C.size : ℤ) ≤ lim.word := by
    exact (by exact_mod_cast (show bc ≤ lim.space by omega) :
      (B.size : ℤ)*(C.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  have habWord : (A.size : ℤ)*(B.size : ℤ) ≤ lim.word := by
    exact (by exact_mod_cast (show ab ≤ lim.space by omega) :
      (A.size : ℤ)*(B.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  have hacWord : (A.size : ℤ)*(C.size : ℤ) ≤ lim.word := by
    exact (by exact_mod_cast (show ac ≤ lim.space by omega) :
      (A.size : ℤ)*(C.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body R.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.body _root_.ThreeSum.LightBandEnumeration.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (N : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (bc : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, bc, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [bc, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, bc, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (ab : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ab, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [ab, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ab, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (ac : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ac, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [ac, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ac, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (outAB : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, outAB, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [outAB, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, outAB, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (outAC : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, outAC, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [outAC, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, outAC, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (powers : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powers, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [powers, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powers, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;> omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.Light.clog2_meets (d := d + 1) (x := N + 1) R.clog μ hlogWord) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.Light.clog2_meets (d := d + 1) (x := N + 1) R.clog μ hlogWord) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;> omega)
     on_goal -1 => (rintro wid μ₀ ⟨hwid, hmem₀⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₀
  rw [← hWdef] at hwid
  subst wid
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.Light.powTable_meets (d := d + 1) (dst := powers) (L := W + 1) (b := 2) R.powers hw hspace' hpowWord) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.Light.powTable_meets (d := d + 1) (dst := powers) (L := W + 1) (b := 2) R.powers hw hspace' hpowWord) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;> omega)
     on_goal -1 => (rintro unused μ₁ ⟨hpowersSeg, hkeep₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hkept₁ : _root_.ThreeSum1960614.Machine.Light.Kept μ μ₁ dst := fun a ha => hkeep₁ a (Or.inl (by omega))
  have hA₁ := hA.keep hkept₁ hal hah
  have hB₁ := hB.keep hkept₁ hbl hbh
  have hC₁ := hC.keep hkept₁ hcl hch
  have hpowers₁ := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress.powers_of_segment hpowersSeg
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBandTable.meets (d := d + 1) (dst := dst) (s := -1) R.table R.row R.lookup R.search μ₁ B.upper C.lower A.lower A.upper hw hbh hcl hal hah (by omega) hspace' hwordA hqueryWord hB₁.2 hC₁.1 hA₁.1 hA₁.2 hpowers₁ A.sorted (by dsimp [N] at hN; omega) (by norm_num) (fun i hi => (hBU i hi).2) (fun i hi => (hCU i hi).1) (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandTable.meets (d := d + 1) (dst := dst) (s := -1) R.table R.row R.lookup R.search μ₁ B.upper C.lower A.lower A.upper hw hbh hcl hal hah (by omega) hspace' hwordA hqueryWord hB₁.2 hC₁.1 hA₁.1 hA₁.2 hpowers₁ A.sorted (by dsimp [N] at hN; omega) (by norm_num) (fun i hi => (hBU i hi).2) (fun i hi => (hCU i hi).1) (by omega)) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, bc, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, bc, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, bc, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;> omega)
     on_goal -1 => (rintro unused μ₂ ⟨hBC, hkeep₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hkept₂ : _root_.ThreeSum1960614.Machine.Light.Kept μ μ₂ dst := fun a ha =>
    (hkeep₂ a (Or.inl ha)).trans (hkept₁ a ha)
  have hA₂ := hA.keep hkept₂ hal hah
  have hB₂ := hB.keep hkept₂ hbl hbh
  have hC₂ := hC.keep hkept₂ hcl hch
  have hpowers₂ : _root_.ThreeSum.LightSubsetAddress.Powers μ₂ powers W := by
    intro i hi
    rw [hkeep₂ (powers+i) (Or.inr (by omega))]
    exact hpowers₁ i hi
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBandTable.meets (d := d + 1) (dst := outAB) (s := 1) R.table R.row R.lookup R.search μ₂ A.lower B.lower C.lower C.upper hw (by omega) (by omega) (by omega) (by omega) (by omega) hspace' hwordC hqueryWord hA₂.1 hB₂.1 hC₂.1 hC₂.2 hpowers₂ C.sorted (by dsimp [N] at hN; omega) (by norm_num) (fun i hi => (hAU i hi).1) (fun i hi => (hBU i hi).1) (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandTable.meets (d := d + 1) (dst := outAB) (s := 1) R.table R.row R.lookup R.search μ₂ A.lower B.lower C.lower C.upper hw (by omega) (by omega) (by omega) (by omega) (by omega) hspace' hwordC hqueryWord hA₂.1 hB₂.1 hC₂.1 hC₂.2 hpowers₂ C.sorted (by dsimp [N] at hN; omega) (by norm_num) (fun i hi => (hAU i hi).1) (fun i hi => (hBU i hi).1) (by omega)) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, bc, ab, outAB, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, bc, ab, outAB, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, bc, ab, outAB, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;> omega)
     on_goal -1 => (rintro unused μ₃ ⟨hAB, hkeep₃⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hkept₃ : _root_.ThreeSum1960614.Machine.Light.Kept μ μ₃ dst := fun a ha =>
    (hkeep₃ a (Or.inl (by omega))).trans (hkept₂ a ha)
  have hA₃ := hA.keep hkept₃ hal hah
  have hB₃ := hB.keep hkept₃ hbl hbh
  have hC₃ := hC.keep hkept₃ hcl hch
  have hpowers₃ : _root_.ThreeSum.LightSubsetAddress.Powers μ₃ powers W := by
    intro i hi
    rw [hkeep₃ (powers+i) (Or.inr (by omega))]
    exact hpowers₂ i hi
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBandTable.meets (d := d + 1) (dst := outAC) (s := -1) R.table R.row R.lookup R.search μ₃ A.lower C.lower B.lower B.upper hw (by omega) (by omega) (by omega) (by omega) (by omega) hspace' hwordB hqueryWord hA₃.1 hC₃.1 hB₃.1 hB₃.2 hpowers₃ B.sorted (by dsimp [N] at hN; omega) (by norm_num) (fun i hi => (hAU i hi).1) (fun i hi => (hCU i hi).1) (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandTable.meets (d := d + 1) (dst := outAC) (s := -1) R.table R.row R.lookup R.search μ₃ A.lower C.lower B.lower B.upper hw (by omega) (by omega) (by omega) (by omega) (by omega) hspace' hwordB hqueryWord hA₃.1 hC₃.1 hB₃.1 hB₃.2 hpowers₃ B.sorted (by dsimp [N] at hN; omega) (by norm_num) (fun i hi => (hAU i hi).1) (fun i hi => (hCU i hi).1) (by omega)) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, bc, ab, ac, outAB, outAC, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, bc, ab, ac, outAB, outAC, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, bc, ab, ac, outAB, outAC, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;> omega)
     on_goal -1 => (rintro unused μ₄ ⟨hAC, hkeep₄⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBandEnumeration.count, bc, ab, ac, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBandEnumeration.count, bc, ab, ac, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBandEnumeration.count, bc, ab, ac, _root_.ThreeSum.LightBandEnumeration.width, ← hNdef, ← hWdef, _root_.ThreeSum.LightBandTable.time, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime, _root_.Light.powTableTime] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine ⟨rfl,⟨?_,?_,?_⟩,?_⟩
  · intro j hj k hk
    have hoff : j*C.size+k < bc := by
      have hh := Nat.mul_le_mul_right C.size (show j+1 ≤ B.size by omega)
      dsimp [bc]
      nlinarith
    change μ₄ (dst+j*C.size+k) = _
    rw [hkeep₄ _ (Or.inl (by omega)),hkeep₃ _ (Or.inl (by omega))]
    simpa [_root_.ThreeSum.LightBandTable.rowValue,sub_eq_add_neg,add_comm] using hBC j hj k hk
  · intro i hi j hj
    have hoff : i*B.size+j < ab := by
      have hh := Nat.mul_le_mul_right B.size (show i+1 ≤ A.size by omega)
      dsimp [ab]
      nlinarith
    change μ₄ (dst+bc+i*B.size+j) = _
    rw [hkeep₄ _ (Or.inl (by omega))]
    simpa [_root_.ThreeSum.LightBandTable.rowValue,outAB] using hAB i hi j hj
  · intro i hi k hk
    simpa [_root_.ThreeSum.LightBandTable.rowValue,outAC,outAB,bc,ab,sub_eq_add_neg,add_comm] using hAC i hi k hk
  · intro a ha
    change μ₄ a = μ a
    exact (hkeep₄ a (Or.inl (by omega))).trans (hkept₃ a ha)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Procs.meets__implementation_4d0d2d7504) := (@ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Procs.meets__implementation_4d0d2d7504)

#print axioms solution
