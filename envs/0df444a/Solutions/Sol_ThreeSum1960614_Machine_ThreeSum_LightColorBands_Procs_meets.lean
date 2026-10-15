-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightColorBands.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:46:16.216175+00:00
-- url     : https://prove2.me/submissions/3949eeaa-368e-4bd8-a07a-02ae33039689

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
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
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Bitwise
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
import Mathlib.Tactic.Push
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandPreprocessing_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightColorClasses_Procs_meets
import Theorems.Thm_ThreeSum_LightBandPreprocessing_time_bound

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.ColorBandBounds
end ThreeSum.ColorBandBounds
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.LightBandEnumeration
end ThreeSum.LightBandEnumeration
namespace ThreeSum.LightBandPreprocessing
end ThreeSum.LightBandPreprocessing
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightColorBands
end ThreeSum.LightColorBands
namespace ThreeSum.LightColorIndex
end ThreeSum.LightColorIndex
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.ColorBandBounds
end ThreeSum1960614.Machine.ThreeSum.ColorBandBounds
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing
end ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing
namespace ThreeSum1960614.Machine.ThreeSum.LightClassFilter
end ThreeSum1960614.Machine.ThreeSum.LightClassFilter
namespace ThreeSum1960614.Machine.ThreeSum.LightColorBands
end ThreeSum1960614.Machine.ThreeSum.LightColorBands
namespace ThreeSum1960614.Machine.ThreeSum.LightColorIndex
end ThreeSum1960614.Machine.ThreeSum.LightColorIndex
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

namespace ThreeSum1960614.Machine

/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition
open _root_.ThreeSum.BandPartition








theorem size_mono {n m g : ℕ} (h : n ≤ m) : _root_.ThreeSum.BandPartition.size n g ≤ _root_.ThreeSum.BandPartition.size m g := by
  by_cases hn : n = 0
  · simp [_root_.ThreeSum.BandPartition.size,hn]
  · have hm : m ≠ 0 := by omega
    have hd := Nat.div_le_div_right (c := g) (show n-1 ≤ m-1 by omega)
    simp only [_root_.ThreeSum.BandPartition.size,if_neg hn,if_neg hm]
    omega























end ThreeSum.BandPartition

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

/-- A specification holds with every larger bound on the time. -/
theorem Meets.mono_time (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T' := by omega) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R :=
  h.mono hT fun _ _ hR => hR





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












































theorem count_mono {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    _root_.ThreeSum.LightBandEnumeration.count a b c ≤ _root_.ThreeSum.LightBandEnumeration.count a' b' c' := by
  unfold _root_.ThreeSum.LightBandEnumeration.count
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul hb hc) (Nat.mul_le_mul ha hb))
    (Nat.mul_le_mul ha hc)

theorem width_mono {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    _root_.ThreeSum.LightBandEnumeration.width a b c ≤ _root_.ThreeSum.LightBandEnumeration.width a' b' c' := Nat.clog_mono_right 2 (by omega)



end ThreeSum.LightBandEnumeration

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Stable extraction of one color class from the original signed array

The program reads stored colors and original values. It writes a length
header followed by exactly the selected values, optionally negated. Repeated
values are preserved; deduplication belongs to the later normalization pass.
-/

namespace ThreeSum.LightClassFilter
open _root_.ThreeSum.LightClassFilter


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000



@[simp] theorem items_zero (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) :
    _root_.ThreeSum.LightClassFilter.items x color want scale 0 = [] := by simp [_root_.ThreeSum.LightClassFilter.items]

theorem items_succ (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) :
    _root_.ThreeSum.LightClassFilter.items x color want scale (n+1) =
      _root_.ThreeSum.LightClassFilter.items x color want scale n ++ (if color n = want then [scale*x n] else []) := by
  by_cases h : color n = want <;> simp [_root_.ThreeSum.LightClassFilter.items,List.range_succ,h]

theorem items_length_le (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) :
    (_root_.ThreeSum.LightClassFilter.items x color want scale n).length ≤ n := by
  simpa only [_root_.ThreeSum.LightClassFilter.items,List.length_map,List.length_range] using
    List.length_filter_le (p := fun i => decide (color i = want)) (l := List.range n)

theorem mem_items (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) (z : ℤ) :
    z ∈ _root_.ThreeSum.LightClassFilter.items x color want scale n ↔ ∃ i, i < n ∧ color i = want ∧ scale*x i = z := by
  simp [_root_.ThreeSum.LightClassFilter.items,and_assoc]









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







end ThreeSum.LightClassFilter

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual evaluation of one member of the deterministic coloring family

Two calls to the checked mask-coordinate routine inspect the selected bits
of an original array index. Four literal color arguments determine the map
from bit patterns to the three colors. The cost is linear in the binary
width and independent of the numeric index magnitude.
-/

namespace ThreeSum.LightColorIndex
open _root_.ThreeSum.LightColorIndex


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}





theorem color_lt {W : ℕ} (p : _root_.ThreeSum.Coloring.Parameter W) (m : ℕ) : _root_.ThreeSum.LightColorIndex.color p m < 3 :=
  (p.2 _).isLt













end ThreeSum.LightColorIndex

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Finite bounds and original-value witness coverage for band preprocessing

These corollaries refer to the memory written by the closed twenty-procedure
program. An exact equation between members of the three original classes
produces a positive owner-table cell and three bands containing the values.
-/

namespace ThreeSum.LightBandPreprocessing
open _root_.ThreeSum.LightBandPreprocessing


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition

















theorem count_square_bound (a b c g : ℕ) :
    _root_.ThreeSum.LightBandEnumeration.count (_root_.ThreeSum.BandPartition.size a g) (_root_.ThreeSum.BandPartition.size b g) (_root_.ThreeSum.BandPartition.size c g) ≤
      3*(_root_.ThreeSum.BandPartition.size (a+b+c) g)^2 := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.count_mono (_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono (g := g) (show a ≤ a+b+c by omega))
    (_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono (g := g) (show b ≤ a+b+c by omega)) (_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono (g := g) (show c ≤ a+b+c by omega))
  convert h using 1 <;> unfold _root_.ThreeSum.LightBandEnumeration.count <;> ring



end ThreeSum.LightBandPreprocessing

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact original-position semantics of the constructed color-class lists

The machine keeps repeated values within a class and negates the third
class. The list membership witnesses are original positions. Any binary
width large enough for the indices suffices for the deterministic family.
-/

namespace ThreeSum.ColorClassLists
open _root_.ThreeSum.ColorClassLists


open _root_.ThreeSum.LightClassFilter
open _root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter













theorem length_classList_le {n W : ℕ} (p : _root_.ThreeSum.Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) : (_root_.ThreeSum.ColorClassLists.classList p x c scale).length ≤ n :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter.items_length_le ..

theorem items_lengths_sum (x : ℕ → ℤ) (color : ℕ → ℕ) (hcolor : ∀ i, color i < 3) (n : ℕ) :
    (_root_.ThreeSum.LightClassFilter.items x color 0 1 n).length + (_root_.ThreeSum.LightClassFilter.items x color 1 1 n).length +
      (_root_.ThreeSum.LightClassFilter.items x color 2 (-1) n).length = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc := hcolor n
    have hc' : color n = 0 ∨ color n = 1 ∨ color n = 2 := by omega
    rcases hc' with he | he | he <;>
      simp only [_root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter.items_succ,he] <;> norm_num at * <;> omega

theorem class_lengths_sum {n W : ℕ} (p : _root_.ThreeSum.Coloring.Parameter W) (x : Fin n → ℤ) :
    (_root_.ThreeSum.ColorClassLists.classList p x 0 1).length + (_root_.ThreeSum.ColorClassLists.classList p x 1 1).length +
      (_root_.ThreeSum.ColorClassLists.classList p x 2 (-1)).length = n :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.items_lengths_sum _ _ (_root_.ThreeSum1960614.Machine.ThreeSum.LightColorIndex.color_lt p) n









end ThreeSum.ColorClassLists

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Uniform band resources for three classes whose lengths sum to n -/

namespace ThreeSum.ColorBandBounds
open _root_.ThreeSum.ColorBandBounds


open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition

set_option maxRecDepth 4000
set_option maxHeartbeats 800000








theorem count_le {a b c n g : ℕ} (hlen : a+b+c=n) :
    _root_.ThreeSum.LightBandEnumeration.count (_root_.ThreeSum.BandPartition.size a g) (_root_.ThreeSum.BandPartition.size b g) (_root_.ThreeSum.BandPartition.size c g) ≤ _root_.ThreeSum.ColorBandBounds.count n g := by
  simpa only [_root_.ThreeSum.ColorBandBounds.count,hlen] using _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.count_square_bound a b c g

theorem width_le {a b c n g : ℕ} (hlen : a+b+c=n) :
    _root_.ThreeSum.LightBandEnumeration.width (_root_.ThreeSum.BandPartition.size a g) (_root_.ThreeSum.BandPartition.size b g) (_root_.ThreeSum.BandPartition.size c g) ≤ _root_.ThreeSum.ColorBandBounds.width n g :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.width_mono (_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono (by omega : a ≤ n))
    (_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono (by omega : b ≤ n)) (_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono (by omega : c ≤ n))

theorem time_le {a b c n g : ℕ} (hlen : a+b+c=n) :
    _root_.ThreeSum.LightBandPreprocessing.time a b c g ≤ _root_.ThreeSum.ColorBandBounds.time n g := by
  have ht := _root_.ThreeSum.LightBandPreprocessing.time_bound a b c g
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.ColorBandBounds.count_le (g := g) hlen
  have hw := _root_.ThreeSum1960614.Machine.ThreeSum.ColorBandBounds.width_le (g := g) hlen
  have hp := Nat.mul_le_mul (Nat.mul_le_mul_left 1000
    (show _root_.ThreeSum.LightBandEnumeration.count (_root_.ThreeSum.BandPartition.size a g) (_root_.ThreeSum.BandPartition.size b g) (_root_.ThreeSum.BandPartition.size c g)+a+b+c+1 ≤
      _root_.ThreeSum.ColorBandBounds.count n g+n+1 by omega)) (Nat.add_le_add_right hw 1)
  unfold _root_.ThreeSum.ColorBandBounds.time
  rw [hlen] at ht
  omega

theorem space_le {a b c n g work : ℕ} (hlen : a+b+c=n) :
    _root_.ThreeSum.LightBandPreprocessing.space work a b c g ≤ _root_.ThreeSum.ColorBandBounds.space work n g := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.ColorBandBounds.count_le (g := g) hlen
  have hw := _root_.ThreeSum1960614.Machine.ThreeSum.ColorBandBounds.width_le (g := g) hlen
  unfold _root_.ThreeSum.LightBandPreprocessing.space _root_.ThreeSum.ColorBandBounds.space
  omega

theorem word_le {a b c n g U : ℕ} (hlen : a+b+c=n) :
    _root_.ThreeSum.LightBandPreprocessing.word a b c g U ≤ _root_.ThreeSum.ColorBandBounds.word n g U := by
  have ha := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono (g := g) (by omega : a ≤ n)
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono (g := g) (by omega : b ≤ n)
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono (g := g) (by omega : c ≤ n)
  unfold _root_.ThreeSum.LightBandPreprocessing.word _root_.ThreeSum.ColorBandBounds.word _root_.ThreeSum.LightBandEnumeration.word
  omega

theorem depth_le {a b c n g : ℕ} (hlen : a+b+c=n) :
    _root_.ThreeSum.LightBandPreprocessing.depth a b c g ≤ _root_.ThreeSum.ColorBandBounds.depth n g := by
  have hw := _root_.ThreeSum1960614.Machine.ThreeSum.ColorBandBounds.width_le (g := g) hlen
  unfold _root_.ThreeSum.LightBandPreprocessing.depth _root_.ThreeSum.ColorBandBounds.depth
  rw [hlen]
  omega

end ThreeSum.ColorBandBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original input to normalized color bands

This fixed program computes index colors, writes the three class arrays and
their headers, then reads those headers into the existing normalization and
owner-table program. All buffers and resource bounds depend on the original
input length, rather than on externally supplied color-class lengths.
-/

namespace ThreeSum.LightColorBands
open _root_.ThreeSum.LightColorBands


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000








theorem class_bounded {n W U : ℕ} (p : _root_.ThreeSum.Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) (hs : |scale| ≤ 1) (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    ∀ z ∈ _root_.ThreeSum.ColorClassLists.classList p x c scale, |z| ≤ (U : ℤ) := by
  intro z hz
  obtain ⟨i,hi,_,rfl⟩ :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter.mem_items (_root_.ThreeSum.ColorClassLists.value x) (_root_.ThreeSum.LightColorIndex.color p) c scale n z).mp hz
  have hv : |_root_.ThreeSum.ColorClassLists.value x i| ≤ (U : ℤ) := by
    simpa only [_root_.ThreeSum.ColorClassLists.value,hi,dite_true] using hx ⟨i,hi⟩
  rw [abs_mul]
  calc
    |scale| * |_root_.ThreeSum.ColorClassLists.value x i| ≤ 1 * (U : ℤ) :=
      mul_le_mul hs hv (abs_nonneg _) (by norm_num)
    _ = (U : ℤ) := one_mul _



variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}













end ThreeSum.LightColorBands

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightColorBands
open _root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightColorBands.Procs.meets__implementation_2fad783114 {pMain src n W colors dst0 dst1 dst2 g av ae bv be cv ce work U : ℕ}
    {μ : ℕ → ℤ} (R : _root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.Procs P pMain) (p : _root_.ThreeSum.Coloring.Parameter W) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2^W) (hg : 0 < g)
    (hsrc : src+n ≤ colors) (hcolors : colors+n ≤ dst0)
    (h0 : dst0+n+1 ≤ dst1) (h1 : dst1+n+1 ≤ dst2) (h2 : dst2+n+1 ≤ av)
    (hav : av+n ≤ ae) (hae : ae+2+2*n ≤ bv)
    (hbv : bv+n ≤ be) (hbe : be+2+2*n ≤ cv)
    (hcv : cv+n ≤ ce) (hce : ce+2+2*n ≤ work)
    (hspace : _root_.ThreeSum.LightColorBands.space work W n g ≤ lim.space)
    (hword : (_root_.ThreeSum.LightColorBands.word W n g U : ℤ) ≤ lim.word) (hd : d+_root_.ThreeSum.LightColorBands.depth W n g ≤ lim.depth)
    (hread : _root_.ThreeSum1960614.Machine.Light.Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,n,W,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,
      colors,dst0,dst1,dst2,g,av,ae,bv,be,cv,ce,work] μ (_root_.ThreeSum.LightColorBands.time W n g)
      (fun r ν => _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Output ν av ae bv be cv ce work g hg
        (_root_.ThreeSum.ColorClassLists.classList p x 0 1) (_root_.ThreeSum.ColorClassLists.classList p x 1 1) (_root_.ThreeSum.ColorClassLists.classList p x 2 (-1)) r ∧
          _root_.ThreeSum1960614.Machine.Light.Kept μ ν colors) := by
  have len0 := _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le p x 0 1
  have len1 := _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le p x 1 1
  have len2 := _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le p x 2 (-1)
  have lens := _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.class_lengths_sum p x
  have hs : work+(W+1) ≤ lim.space := by
    unfold _root_.ThreeSum.LightColorBands.space _root_.ThreeSum.ColorBandBounds.space at hspace
    omega
  have hp : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (show 2^(W+1) ≤ _root_.ThreeSum.LightColorBands.word W n g U by
      unfold _root_.ThreeSum.LightColorBands.word; omega)).trans hword
  have hU : (U : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (show U ≤ _root_.ThreeSum.LightColorBands.word W n g U by
      unfold _root_.ThreeSum.LightColorBands.word; omega)).trans hword
  have hcDepth : d+1+W+3 ≤ lim.depth := by unfold _root_.ThreeSum.LightColorBands.depth at hd; omega
  have hsBand : _root_.ThreeSum.LightBandPreprocessing.space work
      (_root_.ThreeSum.ColorClassLists.classList p x 0 1).length (_root_.ThreeSum.ColorClassLists.classList p x 1 1).length
      (_root_.ThreeSum.ColorClassLists.classList p x 2 (-1)).length g ≤ lim.space := by
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.ColorBandBounds.space_le (work := work) (g := g) lens
    unfold _root_.ThreeSum.LightColorBands.space at hspace
    omega
  have hwBand : (_root_.ThreeSum.LightBandPreprocessing.word
      (_root_.ThreeSum.ColorClassLists.classList p x 0 1).length (_root_.ThreeSum.ColorClassLists.classList p x 1 1).length
      (_root_.ThreeSum.ColorClassLists.classList p x 2 (-1)).length g U : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr ((_root_.ThreeSum1960614.Machine.ThreeSum.ColorBandBounds.word_le (g := g) (U := U) lens).trans
      (show _root_.ThreeSum.ColorBandBounds.word n g U ≤ _root_.ThreeSum.LightColorBands.word W n g U by unfold _root_.ThreeSum.LightColorBands.word; omega))).trans hword
  have hdBand : d+1+_root_.ThreeSum.LightBandPreprocessing.depth
      (_root_.ThreeSum.ColorClassLists.classList p x 0 1).length (_root_.ThreeSum.ColorClassLists.classList p x 1 1).length
      (_root_.ThreeSum.ColorClassLists.classList p x 2 (-1)).length g ≤ lim.depth := by
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.ColorBandBounds.depth_le (g := g) lens
    unfold _root_.ThreeSum.LightColorBands.depth at hd
    omega
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body R.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.body _root_.ThreeSum.LightColorBands.time
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((R.classes.meets (d := d + 1) p x hw hn hsrc hcolors (by omega) (by omega) (by omega) hs hp hU hcDepth hread hbound) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (R.classes.meets (d := d + 1) p x hw hn hsrc hcolors (by omega) (by omega) (by omega) hs hp hU hcDepth hread hbound) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightColorClasses.time, _root_.ThreeSum.LightColorArray.time, _root_.ThreeSum.LightColorIndex.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightClassFilter.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightColorClasses.time, _root_.ThreeSum.LightColorArray.time, _root_.ThreeSum.LightColorIndex.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightClassFilter.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightColorClasses.time, _root_.ThreeSum.LightColorArray.time, _root_.ThreeSum.LightColorIndex.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightClassFilter.time] <;> omega)
     on_goal -1 => (rintro r ν₁ hclasses; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have h0Read := hclasses.header0
  have h1Read := hclasses.header1
  have h2Read := hclasses.header2
  have hb := R.bands.meets (d := d+1) (srcA := dst0+1) (srcB := dst1+1) (srcC := dst2+1)
    (av := av) (ae := ae) (bv := bv) (be := be) (cv := cv) (ce := ce) (work := work)
    hw hg (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hsBand hwBand hdBand
    hclasses.values0 hclasses.values1 hclasses.values2
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.class_bounded p x 0 1 (by norm_num) hbound)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.class_bounded p x 1 1 (by norm_num) hbound)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.class_bounded p x 2 (-1) (by norm_num) hbound)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((hb.mono_time (_root_.ThreeSum1960614.Machine.ThreeSum.ColorBandBounds.time_le (g := g) lens)) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hb.mono_time (_root_.ThreeSum1960614.Machine.ThreeSum.ColorBandBounds.time_le (g := g) lens)) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, h0Read, h1Read, h2Read, _root_.ThreeSum.LightColorClasses.time, _root_.ThreeSum.LightColorArray.time, _root_.ThreeSum.LightColorIndex.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightClassFilter.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [h0Read, h1Read, h2Read, _root_.ThreeSum.LightColorClasses.time, _root_.ThreeSum.LightColorArray.time, _root_.ThreeSum.LightColorIndex.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightClassFilter.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, h0Read, h1Read, h2Read, _root_.ThreeSum.LightColorClasses.time, _root_.ThreeSum.LightColorArray.time, _root_.ThreeSum.LightColorIndex.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightClassFilter.time] <;> omega)
     on_goal -1 => (rintro result ν₂ ⟨hout, hkeep⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨hout,?_⟩
  intro a ha
  exact (hkeep a (by omega)).trans (hclasses.kept a ha)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightColorBands.Procs.meets__implementation_2fad783114) := (@ThreeSum1960614.Machine.ThreeSum.LightColorBands.Procs.meets__implementation_2fad783114)

#print axioms solution
