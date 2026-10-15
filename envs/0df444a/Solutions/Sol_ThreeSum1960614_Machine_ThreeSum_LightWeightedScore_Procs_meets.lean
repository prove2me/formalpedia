-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightWeightedScore.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:24:39.456976+00:00
-- url     : https://prove2.me/submissions/2f8e714e-4758-47ff-a6cb-a3d65c2c4014

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
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
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
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightModuloCounts_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightWeightedScore_meets_of_count_backend

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Arithmetic
end ThreeSum.Arithmetic
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightModuloCounts
end ThreeSum.LightModuloCounts
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightWeightedScore
end ThreeSum.LightWeightedScore
namespace ThreeSum.ModuloCounts
end ThreeSum.ModuloCounts
namespace ThreeSum.ModuloRuntime
end ThreeSum.ModuloRuntime
namespace ThreeSum.WeightedModuli
end ThreeSum.WeightedModuli
namespace ThreeSum.WeightedScore
end ThreeSum.WeightedScore
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Arithmetic
end ThreeSum1960614.Machine.ThreeSum.Arithmetic
namespace ThreeSum1960614.Machine.ThreeSum.CyclicFold
end ThreeSum1960614.Machine.ThreeSum.CyclicFold
namespace ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
end ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
namespace ThreeSum1960614.Machine.ThreeSum.LightModuloCounts
end ThreeSum1960614.Machine.ThreeSum.LightModuloCounts
namespace ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
end ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightWeightedScore
end ThreeSum1960614.Machine.ThreeSum.LightWeightedScore
namespace ThreeSum1960614.Machine.ThreeSum.ModuloCounts
end ThreeSum1960614.Machine.ThreeSum.ModuloCounts
namespace ThreeSum1960614.Machine.ThreeSum.ModuloRuntime
end ThreeSum1960614.Machine.ThreeSum.ModuloRuntime
namespace ThreeSum1960614.Machine.ThreeSum.WeightedModuli
end ThreeSum1960614.Machine.ThreeSum.WeightedModuli
namespace ThreeSum1960614.Machine.ThreeSum.WeightedScore
end ThreeSum1960614.Machine.ThreeSum.WeightedScore

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

/-!
# A complete modular triple-counting procedure

Starting with three arrays of original signed integers and a positive modulus,
this fixed procedure computes its own power-of-two capacity, builds two padded
histograms, multiplies them with Karatsuba, folds the product into a correlation,
and looks up the residues of the A array. The result is exactly the modular
triple count used by the prime-score construction, including all multiplicities.
-/

namespace ThreeSum.LightModuloCounts
open _root_.ThreeSum.LightModuloCounts


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open _root_.ThreeSum.LightResidueHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}













theorem Procs.meets {pMain : ℕ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightModuloCounts.Procs P pMain)
    {μ : ℕ → ℤ} {a b c nA nB nC p N free U : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : _root_.ThreeSum.LightModuloCounts.space free p N U ≤ lim.space)
    (hword : (_root_.ThreeSum.LightModuloCounts.word p N U : ℤ) ≤ lim.word)
    (hd : d + Nat.clog 2 p + 3 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [a,b,c,nA,nB,nC,p,N,free] μ (_root_.ThreeSum.LightModuloCounts.time p nA nB nC U)
      (fun r μ' =>
        r = (_root_.ThreeSum.ModuloCounts.count p nA nB nC
          (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) : ℤ) ∧
          _root_.ThreeSum1960614.Machine.Light.Kept μ μ' free) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightModuloCounts.meets C.main C.capacity C.hist C.residues C.emod C.histogram
    C.cyclic C.multiply C.lookup hw hp ha hb hc hnA hnB hnC hspace hword hd hA hB hC







end ThreeSum.LightModuloCounts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Array-order identities for the weighted modular score

The auxiliary primes are read in a fixed array order.  Every partial
correction is at most the initial `s * N_q`, so the corresponding machine
subtractions stay nonnegative.  Shared factors with `q` use `joint`.
-/

namespace ThreeSum.WeightedScore
open _root_.ThreeSum.WeightedScore


open _root_.Finset
open _root_.ThreeSum.Arithmetic
open _root_.ThreeSum1960614.Machine.ThreeSum.Arithmetic
open _root_.ThreeSum.ModuloCounts
open _root_.ThreeSum1960614.Machine.ThreeSum.ModuloCounts
open _root_.ThreeSum.WeightedModuli
open _root_.ThreeSum1960614.Machine.ThreeSum.WeightedModuli
open scoped _root_.BigOperators

































theorem count_congr {q nA nB nC : ℕ} {a a' b b' c c' : ℕ → ℤ}
    (ha : ∀ i < nA, a i = a' i) (hb : ∀ i < nB, b i = b' i)
    (hc : ∀ i < nC, c i = c' i) :
    _root_.ThreeSum.ModuloCounts.count q nA nB nC a b c = _root_.ThreeSum.ModuloCounts.count q nA nB nC a' b' c' := by
  unfold _root_.ThreeSum.ModuloCounts.count _root_.ThreeSum.Arithmetic.modCount
  apply sum_congr rfl
  intro t ht
  simp only [_root_.ThreeSum.ModuloCounts.triples, mem_product, mem_range] at ht
  simp only [_root_.ThreeSum.ModuloCounts.difference, ha _ ht.1, hb _ ht.2.1, hc _ ht.2.2]

end ThreeSum.WeightedScore

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Uniform bounds for repeated modular-counting calls

A caller may reserve resources for the largest modulus it will use. These
lemmas relate that reservation to the exact costed program contract.
-/

namespace ThreeSum.ModuloRuntime
open _root_.ThreeSum.ModuloRuntime


open _root_.ThreeSum.LightModuloCounts
open _root_.ThreeSum1960614.Machine.ThreeSum.LightModuloCounts
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface

theorem capacity_mono {p q : ℕ} (h : p ≤ q) : _root_.ThreeSum.KaratsubaInterface.capacity p ≤ _root_.ThreeSum.KaratsubaInterface.capacity q := by
  exact Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right 2 h)

theorem karatsuba_time_mono : Monotone _root_.ThreeSum.LightKaratsuba.time := by
  apply monotone_nat_of_le_succ
  intro k
  rw [_root_.ThreeSum.LightKaratsuba.time]
  omega

theorem time_mono {p q : ℕ} (h : p ≤ q) (nA nB nC U : ℕ) :
    _root_.ThreeSum.LightModuloCounts.time p nA nB nC U ≤ _root_.ThreeSum.LightModuloCounts.time q nA nB nC U := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.ModuloRuntime.capacity_mono h
  have hl := Nat.clog_mono_right 2 h
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.ModuloRuntime.karatsuba_time_mono hl
  unfold _root_.ThreeSum.LightModuloCounts.time _root_.ThreeSum.LightCapacity.time _root_.ThreeSum.LightResidueHistogram.time
    _root_.ThreeSum.LightHistogram.histogramTime _root_.ThreeSum.LightCyclic.combinedTime
  simp only [_root_.Light.fillTime, _root_.ThreeSum.LightArray.linearTime]
  omega

theorem space_mono {p q : ℕ} (h : p ≤ q) (free N U : ℕ) :
    _root_.ThreeSum.LightModuloCounts.space free p N U ≤ _root_.ThreeSum.LightModuloCounts.space free q N U := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.ModuloRuntime.capacity_mono h
  unfold _root_.ThreeSum.LightModuloCounts.space
  omega

theorem word_mono {p q : ℕ} (h : p ≤ q) (N U : ℕ) :
    _root_.ThreeSum.LightModuloCounts.word p N U ≤ _root_.ThreeSum.LightModuloCounts.word q N U := by
  have hc := Nat.pow_le_pow_left (_root_.ThreeSum1960614.Machine.ThreeSum.ModuloRuntime.capacity_mono h) 3
  have hk : _root_.ThreeSum.LightKaratsuba.wordBound (_root_.ThreeSum.KaratsubaInterface.capacity p) N ≤
      _root_.ThreeSum.LightKaratsuba.wordBound (_root_.ThreeSum.KaratsubaInterface.capacity q) N := by
    unfold _root_.ThreeSum.LightKaratsuba.wordBound
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 128 hc)
  unfold _root_.ThreeSum.LightModuloCounts.word
  omega

theorem depth_mono {p q : ℕ} (h : p ≤ q) (d : ℕ) :
    d+Nat.clog 2 p+3 ≤ d+Nat.clog 2 q+3 := by
  have hlog := Nat.clog_mono_right 2 h
  omega

/-- Uniform invocation of the actual modular-counting program. -/
theorem meets_bounded {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d pMain : ℕ}
    (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightModuloCounts.Procs P pMain)
    {μ : ℕ → ℤ} {a b c nA nB nC p maxMod N free U : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p) (hm : p ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : _root_.ThreeSum.LightModuloCounts.space free maxMod N U ≤ lim.space)
    (hword : (_root_.ThreeSum.LightModuloCounts.word maxMod N U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+3 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [a,b,c,nA,nB,nC,p,N,free] μ
      (_root_.ThreeSum.LightModuloCounts.time maxMod nA nB nC U)
      (fun r μ' =>
        r = (_root_.ThreeSum.ModuloCounts.count p nA nB nC
          (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) : ℤ) ∧
          _root_.ThreeSum1960614.Machine.Light.Kept μ μ' free) := by
  apply (C.meets hw hp ha hb hc hnA hnB hnC
    ((_root_.ThreeSum1960614.Machine.ThreeSum.ModuloRuntime.space_mono hm free N U).trans hspace)
    ((Int.ofNat_le.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.ModuloRuntime.word_mono hm N U)).trans hword)
    ((_root_.ThreeSum1960614.Machine.ThreeSum.ModuloRuntime.depth_mono hm d).trans hd) hA hB hC).mono (_root_.ThreeSum1960614.Machine.ThreeSum.ModuloRuntime.time_mono hm nA nB nC U)
  intro r μ' hpost
  exact hpost

end ThreeSum.ModuloRuntime

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightWeightedScore
open _root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedScore

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.WeightedModuli
open _root_.ThreeSum1960614.Machine.ThreeSum.WeightedModuli
open _root_.ThreeSum.WeightedScore
open _root_.ThreeSum1960614.Machine.ThreeSum.WeightedScore
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
section


/-- Execute the weighted score on the original signed input arrays. Every
counting premise is discharged by the fixed counting syntax in `C.count`.
The preserved prefix includes the original arrays and the auxiliary primes. -/
theorem ThreeSum1960614.Machine.ThreeSum.LightWeightedScore.Procs.meets__implementation_fc082c653b {pMain : ℕ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedScore.Procs P pMain)
    {μ : ℕ → ℤ} {a b c nA nB nC q N aux s free maxMod U : ℕ}
    (primes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hq : 0 < q) (hqmax : q ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (haux : aux+s ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : _root_.ThreeSum.LightWeightedScore.space free maxMod N U ≤ lim.space)
    (hword : (_root_.ThreeSum.LightWeightedScore.word maxMod N s U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+4 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i) = (primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hproduct : ∀ i < s, q*primes i ≤ maxMod) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [a,b,c,nA,nB,nC,q,N,aux,s,free] μ
      (_root_.ThreeSum.LightWeightedScore.runtimeTime maxMod nA nB nC s U)
      (fun r μ' => r = (_root_.ThreeSum.WeightedScore.score primes s q nA nB nC
        (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) : ℤ) ∧
          _root_.ThreeSum1960614.Machine.Light.Kept μ μ' free) := by
  have hcountSpace : _root_.ThreeSum.LightModuloCounts.space free maxMod N U ≤ lim.space :=
    (Nat.le_max_left _ _).trans hspace
  have hjointSpace : free+(Nat.log 2 (maxMod+1)+2) ≤ lim.space :=
    (Nat.le_max_right _ _).trans hspace
  have hN : N ≤ lim.space := by
    unfold _root_.ThreeSum.LightModuloCounts.space at hcountSpace
    omega
  have hcountWord : (_root_.ThreeSum.LightModuloCounts.word maxMod N U : ℤ) ≤ lim.word := by
    have hh : _root_.ThreeSum.LightModuloCounts.word maxMod N U ≤ _root_.ThreeSum.LightWeightedScore.word maxMod N s U := by
      unfold _root_.ThreeSum.LightWeightedScore.word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hscoreWord : ((s+1)*N^3+8*maxMod+16 : ℕ) ≤ lim.word := by
    have hh : (s+1)*N^3+8*maxMod+16 ≤ _root_.ThreeSum.LightWeightedScore.word maxMod N s U := by
      unfold _root_.ThreeSum.LightWeightedScore.word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  apply _root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedScore.meets_of_count_backend C.main C.joint C.count.emod primes hw (by omega)
    hq hqmax ha hb hc haux hN hnA hnB hnC hjointSpace hscoreWord
    hread hprime hinj hproduct
  intro ν p hkept hp hpmax
  have hAν : ∀ i < nA, |ν (a+i)| ≤ (U : ℤ) := by
    intro i hi
    rw [hkept _ (by omega)]
    exact hA i hi
  have hBν : ∀ i < nB, |ν (b+i)| ≤ (U : ℤ) := by
    intro i hi
    rw [hkept _ (by omega)]
    exact hB i hi
  have hCν : ∀ i < nC, |ν (c+i)| ≤ (U : ℤ) := by
    intro i hi
    rw [hkept _ (by omega)]
    exact hC i hi
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.ModuloRuntime.meets_bounded (d := d+1) C.count hw hp hpmax ha hb hc
    hnA hnB hnC hcountSpace hcountWord (by omega) hAν hBν hCν).mono le_rfl
  intro r ν' ⟨hr,hkeep⟩
  refine ⟨hr.trans ?_,hkeep⟩
  congr 1
  exact _root_.ThreeSum1960614.Machine.ThreeSum.WeightedScore.count_congr (fun i hi => hkept _ (by omega))
    (fun i hi => hkept _ (by omega)) (fun i hi => hkept _ (by omega))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightWeightedScore.Procs.meets__implementation_fc082c653b) := (@ThreeSum1960614.Machine.ThreeSum.LightWeightedScore.Procs.meets__implementation_fc082c653b)

#print axioms solution
