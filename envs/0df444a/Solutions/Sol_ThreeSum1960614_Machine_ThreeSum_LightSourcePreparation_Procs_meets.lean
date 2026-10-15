-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:22:05.941265+00:00
-- url     : https://prove2.me/submissions/50bef25e-957a-4c4f-a0b2-2ceee343f38c

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
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
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean
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
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
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
import Mathlib.Tactic
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBlockSourceHashes_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceFlagArray_Procs_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.LightSourcePreparation
end ThreeSum.LightSourcePreparation
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation
end ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation

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

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourcePreparation
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation.Procs.meets__implementation_7dfe054748 {pMain : ℕ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation.Procs P pMain)
    {μ : ℕ → ℤ} {J L h p cap occ maps candidates histL histR masks n coeff0 coeff1 rawLeft rawRight flags
      bitBase rowOut work U V M K : ℕ}
    (sel candidate mask : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*L+5 ≤ lim.depth)
    (hp : 0 < p) (hh : h ≤ L)
    (hocc : occ+J ≤ coeff0) (hmaps : maps+2*L*M ≤ coeff0)
    (hcandidates : candidates+M ≤ coeff0)
    (hleft : histL+K*p ≤ coeff0) (hright : histR+K*p ≤ coeff0)
    (hmasks : masks+n ≤ coeff0) (hc0 : coeff0+J*L ≤ coeff1)
    (hc1 : coeff1+J*L ≤ rawLeft) (hrawLeft : rawLeft+n ≤ rawRight)
    (hrawRight : rawRight+n ≤ flags) (hflags : flags+2*n+2 ≤ bitBase)
    (hbits : bitBase+J*L ≤ rowOut) (hrowOut : rowOut+2 ≤ work)
    (hspace : _root_.ThreeSum.LightSourcePreparation.space work J L U ≤ lim.space)
    (hword : (_root_.ThreeSum.LightSourcePreparation.word J L p U V cap : ℤ) ≤ lim.word)
    (hsel : ∀ j < J, sel j < M) (hcandidate : ∀ s < M, candidate s < K)
    (hoccRead : ∀ j < J, μ (occ+j) = (sel j : ℤ))
    (hcandidateRead : ∀ s < M, μ (candidates+s) = (candidate s : ℤ))
    (hread0 : ∀ s < M, ∀ a < L, μ (maps+2*L*s+a) = (w0 s a : ℤ))
    (hread1 : ∀ s < M, ∀ a < L, μ (maps+2*L*s+L+a) = (w1 s a : ℤ))
    (hbound0 : ∀ s < M, ∀ a < L, w0 s a ≤ U)
    (hbound1 : ∀ s < M, ∀ a < L, w1 s a ≤ U)
    (hcountL : ∀ k < K, ∀ r < p, μ (histL+k*p+r) = (leftCount k r : ℤ))
    (hcountR : ∀ k < K, ∀ r < p, μ (histR+k*p+r) = (rightCount k r : ℤ))
    (hcountBoundL : ∀ k < K, ∀ r < p, leftCount k r ≤ V)
    (hcountBoundR : ∀ k < K, ∀ r < p, rightCount k r ≤ V)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskBound : ∀ i < n, mask i < 2^(J*L)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [J,L,h,p,cap,occ,maps,candidates,histL,histR,masks,n,coeff0,coeff1,rawLeft,rawRight,
        flags,bitBase,rowOut,work]
      μ (_root_.ThreeSum.LightSourcePreparation.time n J L U) (fun _ ν =>
        (∀ i < n, ν (rawLeft+i) =
          (_root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w0) (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w1) (J*L) (mask i) : ℤ)) ∧
        (∀ i < n, ν (rawRight+i) =
          (_root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w1) (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w0) (J*L) (mask i) : ℤ)) ∧
        (∀ i < n, ν (flags+i) =
          (_root_.ThreeSum.LightSourceFlagArray.flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ)) ∧
        (∀ i < n, ν (flags+n+i) =
          (_root_.ThreeSum.LightSourceFlagArray.flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν coeff0) := by
  have hsHash : _root_.ThreeSum.LightBlockSourceHashes.space work J L ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hsFlag : _root_.ThreeSum.LightSourceMaskFlags.space work J L U ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hwHash : (_root_.ThreeSum.LightBlockSourceHashes.word J L p U : ℤ) ≤ lim.word := by
    have hh : _root_.ThreeSum.LightBlockSourceHashes.word J L p U ≤ _root_.ThreeSum.LightSourcePreparation.word J L p U V cap := by unfold _root_.ThreeSum.LightSourcePreparation.word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwFlag : (_root_.ThreeSum.LightSourceMaskFlags.word J L p U V cap : ℤ) ≤ lim.word := by
    have hh : _root_.ThreeSum.LightSourceMaskFlags.word J L p U V cap ≤ _root_.ThreeSum.LightSourcePreparation.word J L p U V cap := by unfold _root_.ThreeSum.LightSourcePreparation.word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body C.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation.body _root_.ThreeSum.LightSourcePreparation.time
  have hhash := C.hashes.meets (d := d+1) (μ := μ) (J := J) (L := L) (p := p)
    (occ := occ) (maps := maps) (coeff0 := coeff0) (coeff1 := coeff1) (masks := masks)
    (rawLeft := rawLeft) (rawRight := rawRight) (n := n) (work := work) (U := U) (M := M)
    sel mask w0 w1 hw hp (by omega) hsHash hocc hmaps hmasks hc0 hc1 hrawLeft (by omega)
    hwHash hsel hoccRead hread0 hread1 hbound0 hbound1 hmaskRead hmaskBound
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hhash _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hhash ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockSourceHashes.time, _root_.ThreeSum.LightBlockCoefficients.time, _root_.ThreeSum.LightBlockCoefficients.roundTime, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightScaleArray.time, _root_.ThreeSum.LightSourceFlagArray.time, _root_.ThreeSum.LightSourceMaskFlags.time, _root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockSourceHashes.time, _root_.ThreeSum.LightBlockCoefficients.time, _root_.ThreeSum.LightBlockCoefficients.roundTime, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightScaleArray.time, _root_.ThreeSum.LightSourceFlagArray.time, _root_.ThreeSum.LightSourceMaskFlags.time, _root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockSourceHashes.time, _root_.ThreeSum.LightBlockCoefficients.time, _root_.ThreeSum.LightBlockCoefficients.roundTime, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightScaleArray.time, _root_.ThreeSum.LightSourceFlagArray.time, _root_.ThreeSum.LightSourceMaskFlags.time, _root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time] <;> omega)
     on_goal -1 => (rintro r ν₁ ⟨rawL, rawR, rows, kept₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hocc' : ∀ j < J, ν₁ (occ+j) = (sel j : ℤ) := by
    intro j hj
    exact (kept₁ _ (by omega)).trans (hoccRead j hj)
  have hcan' : ∀ s < M, ν₁ (candidates+s) = (candidate s : ℤ) := by
    intro s hs
    exact (kept₁ _ (by omega)).trans (hcandidateRead s hs)
  have hread0' : ∀ s < M, ∀ a < L, ν₁ (maps+2*L*s+a) = (w0 s a : ℤ) := by
    intro s hs a ha
    have he := Nat.mul_le_mul_left (2*L) (show s+1 ≤ M by omega)
    exact (kept₁ _ (by nlinarith)).trans (hread0 s hs a ha)
  have hread1' : ∀ s < M, ∀ a < L, ν₁ (maps+2*L*s+L+a) = (w1 s a : ℤ) := by
    intro s hs a ha
    have he := Nat.mul_le_mul_left (2*L) (show s+1 ≤ M by omega)
    exact (kept₁ _ (by nlinarith)).trans (hread1 s hs a ha)
  have hcountL' : ∀ k < K, ∀ r < p, ν₁ (histL+k*p+r) = (leftCount k r : ℤ) := by
    intro k hk r hr
    have he := Nat.mul_le_mul_right p (show k+1 ≤ K by omega)
    exact (kept₁ _ (by nlinarith)).trans (hcountL k hk r hr)
  have hcountR' : ∀ k < K, ∀ r < p, ν₁ (histR+k*p+r) = (rightCount k r : ℤ) := by
    intro k hk r hr
    have he := Nat.mul_le_mul_right p (show k+1 ≤ K by omega)
    exact (kept₁ _ (by nlinarith)).trans (hcountR k hk r hr)
  have hmask' : ∀ i < n, ν₁ (masks+i) = (mask i : ℤ) := by
    intro i hi
    exact (kept₁ _ (by omega)).trans (hmaskRead i hi)
  have hf := C.flags.meets (d := d+1) (μ := ν₁) (J := J) (L := L) (h := h) (p := p)
    (cap := cap) (occ := occ) (maps := maps) (candidates := candidates)
    (histL := histL) (histR := histR) (masks := masks) (n := n) (dst := flags)
    (bitBase := bitBase) (rowOut := rowOut) (work := work) (U := U) (V := V) (M := M) (K := K)
    sel candidate mask w0 w1 leftCount rightCount hw (by omega) hp hh
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hflags hbits hrowOut hsFlag hwFlag hsel hcandidate hocc' hcan' hread0' hread1'
    hbound0 hbound1 hcountL' hcountR' hcountBoundL hcountBoundR hmask' hmaskBound
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hf _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hf ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockSourceHashes.time, _root_.ThreeSum.LightBlockCoefficients.time, _root_.ThreeSum.LightBlockCoefficients.roundTime, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightScaleArray.time, _root_.ThreeSum.LightSourceFlagArray.time, _root_.ThreeSum.LightSourceMaskFlags.time, _root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockSourceHashes.time, _root_.ThreeSum.LightBlockCoefficients.time, _root_.ThreeSum.LightBlockCoefficients.roundTime, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightScaleArray.time, _root_.ThreeSum.LightSourceFlagArray.time, _root_.ThreeSum.LightSourceMaskFlags.time, _root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockSourceHashes.time, _root_.ThreeSum.LightBlockCoefficients.time, _root_.ThreeSum.LightBlockCoefficients.roundTime, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightScaleArray.time, _root_.ThreeSum.LightSourceFlagArray.time, _root_.ThreeSum.LightSourceMaskFlags.time, _root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time] <;> omega)
     on_goal -1 => (rintro r ν₂ ⟨leftFlags, rightFlags, kept₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨?_,?_,leftFlags,rightFlags,?_⟩
  · intro i hi
    exact (kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (rawL i hi)
  · intro i hi
    exact (kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (rawR i hi)
  · intro a ha
    exact (kept₂ a ⟨by omega,Or.inl (by omega)⟩).trans (kept₁ a ha)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation.Procs.meets__implementation_7dfe054748) := (@ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation.Procs.meets__implementation_7dfe054748)

#print axioms solution
