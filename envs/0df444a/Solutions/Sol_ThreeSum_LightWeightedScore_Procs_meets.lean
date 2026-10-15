-- Prove2me | solution 1 for ThreeSum.LightWeightedScore.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:41:07.120714+00:00
-- url     : https://prove2.me/submissions/4565d500-920c-427f-9c48-8187a7fa3daf

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
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
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
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_LightModuloCounts_meets
import Theorems.Thm_ThreeSum_LightWeightedScore_meets_of_count_backend


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
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
namespace ThreeSum.ModuloCounts
end ThreeSum.ModuloCounts
namespace ThreeSum.WeightedModuli
end ThreeSum.WeightedModuli
namespace ThreeSum.WeightedScore
end ThreeSum.WeightedScore

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



























































































































/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/




























/-! ## Simplification -/

attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame
















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








/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩

















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
# A complete modular triple-counting procedure

Starting with three arrays of original signed integers and a positive modulus,
this fixed procedure computes its own power-of-two capacity, builds two padded
histograms, multiplies them with Karatsuba, folds the product into a correlation,
and looks up the residues of the A array. The result is exactly the modular
triple count used by the prime-score construction, including all multiplicities.
-/

namespace ThreeSum.LightModuloCounts

open Light ThreeSum.LightResidues ThreeSum.LightResidueHistogram
open ThreeSum.KaratsubaInterface ThreeSum.CyclicFold

variable {lim : Limits} {P : Program} {d : ℕ}












































































































































































































theorem Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {a b c nA nB nC p N free U : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free p N U ≤ lim.space)
    (hword : (word p N U : ℤ) ≤ lim.word)
    (hd : d + Nat.clog 2 p + 3 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ)) :
    Meets lim P pMain d [a,b,c,nA,nB,nC,p,N,free] μ (time p nA nB nC U)
      (fun r μ' =>
        r = (ModuloCounts.count p nA nB nC
          (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) : ℤ) ∧
          Kept μ μ' free) :=
  LightModuloCounts.meets C.main C.capacity C.hist C.residues C.emod C.histogram
    C.cyclic C.multiply C.lookup hw hp ha hb hc hnA hnB hnC hspace hword hd hA hB hC















































end ThreeSum.LightModuloCounts

end

section


/-!
# Array-order identities for the weighted modular score

The auxiliary primes are read in a fixed array order.  Every partial
correction is at most the initial `s * N_q`, so the corresponding machine
subtractions stay nonnegative.  Shared factors with `q` use `joint`.
-/

namespace ThreeSum.WeightedScore

open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators






















































































































theorem count_congr {q nA nB nC : ℕ} {a a' b b' c c' : ℕ → ℤ}
    (ha : ∀ i < nA, a i = a' i) (hb : ∀ i < nB, b i = b' i)
    (hc : ∀ i < nC, c i = c' i) :
    count q nA nB nC a b c = count q nA nB nC a' b' c' := by
  unfold count modCount
  apply sum_congr rfl
  intro t ht
  simp only [triples, mem_product, mem_range] at ht
  simp only [difference, ha _ ht.1, hb _ ht.2.1, hc _ ht.2.2]

end ThreeSum.WeightedScore

end

section


/-!
# Uniform bounds for repeated modular-counting calls

A caller may reserve resources for the largest modulus it will use. These
lemmas relate that reservation to the exact costed program contract.
-/

namespace ThreeSum.ModuloRuntime

open LightModuloCounts KaratsubaInterface

theorem capacity_mono {p q : ℕ} (h : p ≤ q) : capacity p ≤ capacity q := by
  exact Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right 2 h)

theorem karatsuba_time_mono : Monotone LightKaratsuba.time := by
  apply monotone_nat_of_le_succ
  intro k
  rw [LightKaratsuba.time]
  omega

theorem time_mono {p q : ℕ} (h : p ≤ q) (nA nB nC U : ℕ) :
    time p nA nB nC U ≤ time q nA nB nC U := by
  have hc := capacity_mono h
  have hl := Nat.clog_mono_right 2 h
  have ht := karatsuba_time_mono hl
  unfold time LightCapacity.time LightResidueHistogram.time
    LightHistogram.histogramTime LightCyclic.combinedTime
  simp only [Light.fillTime, LightArray.linearTime]
  omega

theorem space_mono {p q : ℕ} (h : p ≤ q) (free N U : ℕ) :
    space free p N U ≤ space free q N U := by
  have hc := capacity_mono h
  unfold space
  omega

theorem word_mono {p q : ℕ} (h : p ≤ q) (N U : ℕ) :
    word p N U ≤ word q N U := by
  have hc := Nat.pow_le_pow_left (capacity_mono h) 3
  have hk : LightKaratsuba.wordBound (capacity p) N ≤
      LightKaratsuba.wordBound (capacity q) N := by
    unfold LightKaratsuba.wordBound
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 128 hc)
  unfold word
  omega

theorem depth_mono {p q : ℕ} (h : p ≤ q) (d : ℕ) :
    d+Nat.clog 2 p+3 ≤ d+Nat.clog 2 q+3 := by
  have hlog := Nat.clog_mono_right 2 h
  omega

/-- Uniform invocation of the actual modular-counting program. -/
theorem meets_bounded {lim : Light.Limits} {P : Light.Program} {d pMain : ℕ}
    (C : LightModuloCounts.Procs P pMain)
    {μ : ℕ → ℤ} {a b c nA nB nC p maxMod N free U : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p) (hm : p ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free maxMod N U ≤ lim.space)
    (hword : (word maxMod N U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+3 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ)) :
    Light.Meets lim P pMain d [a,b,c,nA,nB,nC,p,N,free] μ
      (time maxMod nA nB nC U)
      (fun r μ' =>
        r = (ModuloCounts.count p nA nB nC
          (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) : ℤ) ∧
          Light.Kept μ μ' free) := by
  apply (C.meets hw hp ha hb hc hnA hnB hnC
    ((space_mono hm free N U).trans hspace)
    ((Int.ofNat_le.mpr (word_mono hm N U)).trans hword)
    ((depth_mono hm d).trans hd) hA hB hC).mono (time_mono hm nA nB nC U)
  intro r μ' hpost
  exact hpost

end ThreeSum.ModuloRuntime

end

section


/-!
# Executing the weighted modular score

The joint-modulus helper uses the verified division-free remainder routine.
The score loop computes a base count, then visits the auxiliary-prime array
once.  All calls reuse the same scratch region and preserve the original
arrays.  Its intermediate scores are proved nonnegative.

The generic loop theorem exposes the modular-counting execution contract.
The concrete wrapper instantiates that contract with the checked fixed
modular-counting program; no counting operation is added to the machine.
-/

namespace ThreeSum.LightWeightedScore

open Light WeightedModuli WeightedScore LightResidues

variable {lim : Limits} {P : Program} {d : ℕ}

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
















































































































































































































/-- Execute the weighted score on the original signed input arrays. Every
counting premise is discharged by the fixed counting syntax in `C.count`.
The preserved prefix includes the original arrays and the auxiliary primes. -/
theorem Procs.meets_sourceProof {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {a b c nA nB nC q N aux s free maxMod U : ℕ}
    (primes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hq : 0 < q) (hqmax : q ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (haux : aux+s ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free maxMod N U ≤ lim.space)
    (hword : (word maxMod N s U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+4 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i) = (primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hproduct : ∀ i < s, q*primes i ≤ maxMod) :
    Meets lim P pMain d [a,b,c,nA,nB,nC,q,N,aux,s,free] μ
      (runtimeTime maxMod nA nB nC s U)
      (fun r μ' => r = (score primes s q nA nB nC
        (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) : ℤ) ∧
          Kept μ μ' free) := by
  have hcountSpace : LightModuloCounts.space free maxMod N U ≤ lim.space :=
    (Nat.le_max_left _ _).trans hspace
  have hjointSpace : free+(Nat.log 2 (maxMod+1)+2) ≤ lim.space :=
    (Nat.le_max_right _ _).trans hspace
  have hN : N ≤ lim.space := by
    unfold LightModuloCounts.space at hcountSpace
    omega
  have hcountWord : (LightModuloCounts.word maxMod N U : ℤ) ≤ lim.word := by
    have hh : LightModuloCounts.word maxMod N U ≤ word maxMod N s U := by
      unfold word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hscoreWord : ((s+1)*N^3+8*maxMod+16 : ℕ) ≤ lim.word := by
    have hh : (s+1)*N^3+8*maxMod+16 ≤ word maxMod N s U := by
      unfold word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  apply meets_of_count_backend C.main C.joint C.count.emod primes hw (by omega)
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
  apply (ModuloRuntime.meets_bounded (d := d+1) C.count hw hp hpmax ha hb hc
    hnA hnB hnC hcountSpace hcountWord (by omega) hAν hBν hCν).mono le_rfl
  intro r ν' ⟨hr,hkeep⟩
  refine ⟨hr.trans ?_,hkeep⟩
  congr 1
  exact WeightedScore.count_congr (fun i hi => hkept _ (by omega))
    (fun i hi => hkept _ (by omega)) (fun i hi => hkept _ (by omega))

































































end ThreeSum.LightWeightedScore

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (C : ThreeSum.LightWeightedScore.Procs P pMain)
  {μ : Nat → Int} {a b c nA nB nC q N aux s free maxMod U : Nat} (primes : Nat → Nat),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q →
      @LE.le.{0} Nat instLENat q maxMod →
        @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a nA) free →
          @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b nB) free →
            @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c nC) free →
              @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) aux s) free →
                @LE.le.{0} Nat instLENat nA N →
                  @LE.le.{0} Nat instLENat nB N →
                    @LE.le.{0} Nat instLENat nC N →
                      @LE.le.{0} Nat instLENat (ThreeSum.LightWeightedScore.space free maxMod N U) lim.space →
                        @LE.le.{0} Int Int.instLEInt
                            (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightWeightedScore.word maxMod N s U))
                            lim.word →
                          @LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                                  (Nat.clog (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) maxMod))
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                              lim.depth →
                            (∀ (i : Nat),
                                @LT.lt.{0} Nat instLTNat i nA →
                                  @LE.le.{0} Int Int.instLEInt
                                    (@abs.{0} Int instLatticeInt Int.instAddGroup
                                      (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a i)))
                                    (@Nat.cast.{0} Int instNatCastInt U)) →
                              (∀ (i : Nat),
                                  @LT.lt.{0} Nat instLTNat i nB →
                                    @LE.le.{0} Int Int.instLEInt
                                      (@abs.{0} Int instLatticeInt Int.instAddGroup
                                        (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b i)))
                                      (@Nat.cast.{0} Int instNatCastInt U)) →
                                (∀ (i : Nat),
                                    @LT.lt.{0} Nat instLTNat i nC →
                                      @LE.le.{0} Int Int.instLEInt
                                        (@abs.{0} Int instLatticeInt Int.instAddGroup
                                          (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c i)))
                                        (@Nat.cast.{0} Int instNatCastInt U)) →
                                  (∀ (i : Nat),
                                      @LT.lt.{0} Nat instLTNat i s →
                                        @Eq.{1} Int
                                          (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) aux i))
                                          (@Nat.cast.{0} Int instNatCastInt (primes i))) →
                                    (∀ (i : Nat), @LT.lt.{0} Nat instLTNat i s → Nat.Prime (primes i)) →
                                      (∀ (i : Nat),
                                          @LT.lt.{0} Nat instLTNat i s →
                                            ∀ (j : Nat),
                                              @LT.lt.{0} Nat instLTNat j s →
                                                @Eq.{1} Nat (primes i) (primes j) → @Eq.{1} Nat i j) →
                                        (∀ (i : Nat),
                                            @LT.lt.{0} Nat instLTNat i s →
                                              @LE.le.{0} Nat instLENat
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q
                                                  (primes i))
                                                maxMod) →
                                          Light.Meets lim P pMain d
                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt c)
                                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nA)
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nB)
                                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nC)
                                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt q)
                                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt N)
                                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt aux)
                                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt s)
                                                                (@List.cons.{0} Int
                                                                  (@Nat.cast.{0} Int instNatCastInt free)
                                                                  (@List.nil.{0} Int))))))))))))
                                            μ (ThreeSum.LightWeightedScore.runtimeTime maxMod nA nB nC s U)
                                            fun (r : Int) (μ' : Nat → Int) =>
                                            And
                                              (@Eq.{1} Int r
                                                (@Nat.cast.{0} Int instNatCastInt
                                                  (ThreeSum.WeightedScore.score primes s q nA nB nC
                                                    (fun (j : Nat) =>
                                                      μ
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          a j))
                                                    (fun (j : Nat) =>
                                                      μ
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          b j))
                                                    fun (j : Nat) =>
                                                    μ
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c
                                                        j))))
                                              (Light.Kept μ μ' free) := by
  exact @ThreeSum.LightWeightedScore.Procs.meets_sourceProof

#print axioms solution
