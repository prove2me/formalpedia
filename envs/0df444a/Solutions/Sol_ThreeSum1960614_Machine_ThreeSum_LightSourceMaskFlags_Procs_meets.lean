-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSourceMaskFlags.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:56:18.850712+00:00
-- url     : https://prove2.me/submissions/12840073-56c4-48fd-9dcf-12e3e842bd71

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
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
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Tactic
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightMaskBits_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceTrim_Procs_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightMaskBits
end ThreeSum.LightMaskBits
namespace ThreeSum.LightSourceMaskFlags
end ThreeSum.LightSourceMaskFlags
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.SourceFlagProduct
end ThreeSum.SourceFlagProduct
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskBits
end ThreeSum1960614.Machine.ThreeSum.LightMaskBits
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceMaskFlags
end ThreeSum1960614.Machine.ThreeSum.LightSourceMaskFlags
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.MaskErase
end ThreeSum1960614.Machine.ThreeSum.MaskErase
namespace ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct
end ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct

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

/-! # A literal Boolean coordinate row for a subset mask -/

namespace ThreeSum.LightMaskBits
open _root_.ThreeSum.LightMaskBits


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase



theorem bit_le (L m j : ℕ) : _root_.ThreeSum.LightMaskBits.bit L m j ≤ 1 := by unfold _root_.ThreeSum.LightMaskBits.bit; split <;> omega













variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightMaskBits

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceMaskFlags
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceMaskFlags

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceFlagProduct
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightSourceMaskFlags.Procs.meets__implementation_3db9b6c296 {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceMaskFlags.Procs P pMain)
    {μ : ℕ → ℤ} {J L h p cap occ maps candidates histL histR mask dst bitBase rowOut work U V M K : ℕ}
    (sel candidate : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*L+3 ≤ lim.depth)
    (hp : 0 < p) (hh : h ≤ L)
    (hocc : occ+J ≤ bitBase) (hmaps : maps+2*L*M ≤ bitBase)
    (hcandidates : candidates+M ≤ bitBase)
    (hleft : histL+K*p ≤ bitBase) (hright : histR+K*p ≤ bitBase)
    (hdst : dst+2 ≤ bitBase) (hbits : bitBase+J*L ≤ rowOut) (hrowOut : rowOut+2 ≤ work)
    (hspace : _root_.ThreeSum.LightSourceMaskFlags.space work J L U ≤ lim.space)
    (hword : (_root_.ThreeSum.LightSourceMaskFlags.word J L p U V cap : ℤ) ≤ lim.word) (hmask : mask < 2^(J*L))
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
    (hcountBoundR : ∀ k < K, ∀ r < p, rightCount k r ≤ V) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [J,L,h,p,cap,occ,maps,candidates,histL,histR,mask,dst,bitBase,rowOut,work]
      μ (_root_.ThreeSum.LightSourceMaskFlags.time J L U) (fun _ ν =>
        ν dst = (_root_.ThreeSum.SourceFlagProduct.product (_root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate
          (_root_.ThreeSum.LightMaskBits.bit (J*L) mask) w0 w1 leftCount) J : ℤ) ∧
        ν (dst+1) = (_root_.ThreeSum.SourceFlagProduct.product (_root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate
          (_root_.ThreeSum.LightMaskBits.bit (J*L) mask) w1 w0 rightCount) J : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν bitBase dst 2) := by
  have hspaceBits : work+(J*L+1) ≤ lim.space :=
    (Nat.add_le_add_left (le_max_left _ _) work).trans hspace
  have hspaceTrim : _root_.ThreeSum.LightSourceRowFlag.space work L U ≤ lim.space := by
    have hh := (Nat.add_le_add_left (le_max_right (J*L+1) (3+(Nat.log 2 (L*U+1)+2))) work).trans hspace
    simpa only [_root_.ThreeSum.LightSourceRowFlag.space,Nat.add_assoc] using hh
  have hwordBits : ((2^(J*L+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : 2^(J*L+1) ≤ _root_.ThreeSum.LightSourceMaskFlags.word J L p U V cap := by unfold _root_.ThreeSum.LightSourceMaskFlags.word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwordTrim : (_root_.ThreeSum.LightSourceRowFlag.word L p U V cap : ℤ) ≤ lim.word := by
    have hh : _root_.ThreeSum.LightSourceRowFlag.word L p U V cap ≤ _root_.ThreeSum.LightSourceMaskFlags.word J L p U V cap := by unfold _root_.ThreeSum.LightSourceMaskFlags.word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwidth : (J : ℤ)*(L : ℤ) ≤ lim.word := by
    exact (by exact_mod_cast (show J*L ≤ lim.space by omega) :
      (J : ℤ)*(L : ℤ) ≤ lim.space).trans hw
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body S.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceMaskFlags.body _root_.ThreeSum.LightSourceMaskFlags.time
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskBits.meets (d := d+1) (μ := μ) (L := J*L) (m := mask)
    (dst := bitBase) (work := work) S.bits S.powers S.erase hw (by omega) hspaceBits
    (by omega) hwordBits hmask
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hb _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hb ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;> omega)
     on_goal -1 => (rintro r ν₁ ⟨bitsRead, _, kept₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hkeep : _root_.ThreeSum1960614.Machine.Light.Kept μ ν₁ bitBase := by
    intro a ha
    exact kept₁ a ⟨by omega,Or.inl ha⟩
  have hoccRead₁ : ∀ j < J, ν₁ (occ+j) = (sel j : ℤ) := by
    intro j hj
    exact (hkeep _ (by omega)).trans (hoccRead j hj)
  have hcandRead₁ : ∀ s < M, ν₁ (candidates+s) = (candidate s : ℤ) := by
    intro s hs
    exact (hkeep _ (by omega)).trans (hcandidateRead s hs)
  have hread0₁ : ∀ s < M, ∀ a < L, ν₁ (maps+2*L*s+a) = (w0 s a : ℤ) := by
    intro s hs a ha
    have he := Nat.mul_le_mul_left (2*L) (show s+1 ≤ M by omega)
    exact (hkeep _ (by nlinarith)).trans (hread0 s hs a ha)
  have hread1₁ : ∀ s < M, ∀ a < L, ν₁ (maps+2*L*s+L+a) = (w1 s a : ℤ) := by
    intro s hs a ha
    have he := Nat.mul_le_mul_left (2*L) (show s+1 ≤ M by omega)
    exact (hkeep _ (by nlinarith)).trans (hread1 s hs a ha)
  have hcountL₁ : ∀ k < K, ∀ r < p, ν₁ (histL+k*p+r) = (leftCount k r : ℤ) := by
    intro k hk r hr
    have he := Nat.mul_le_mul_right p (show k+1 ≤ K by omega)
    exact (hkeep _ (by nlinarith)).trans (hcountL k hk r hr)
  have hcountR₁ : ∀ k < K, ∀ r < p, ν₁ (histR+k*p+r) = (rightCount k r : ℤ) := by
    intro k hk r hr
    have he := Nat.mul_le_mul_right p (show k+1 ≤ K by omega)
    exact (hkeep _ (by nlinarith)).trans (hcountR k hk r hr)
  have ht := S.trim.meets (d := d+1) (μ := ν₁) (J := J) (L := L) (h := h)
    (p := p) (cap := cap) (occ := occ) (maps := maps) (candidates := candidates)
    (histL := histL) (histR := histR) (bitBase := bitBase) (rowOut := rowOut)
    (work := work) (dst := dst) (U := U) (V := V) (M := M) (K := K)
    sel candidate (_root_.ThreeSum.LightMaskBits.bit (J*L) mask) w0 w1 leftCount rightCount
    hw (by omega) hp hh (by omega) (by omega) (by omega) (by omega) (by omega)
    hbits hrowOut (by omega) hspaceTrim hwordTrim hsel hcandidate hoccRead₁ hcandRead₁
    bitsRead (fun i _ => _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskBits.bit_le _ _ i) hread0₁ hread1₁ hbound0 hbound1
    hcountL₁ hcountR₁ hcountBoundL hcountBoundR
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (ht _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ht ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;> omega)
     on_goal -1 => (rintro r ν₂ ⟨left, right, kept₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨left,right,?_⟩
  intro a ⟨ha,hout⟩
  exact (kept₂ a ⟨by omega,hout⟩).trans (hkeep a ha)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSourceMaskFlags.Procs.meets__implementation_3db9b6c296) := (@ThreeSum1960614.Machine.ThreeSum.LightSourceMaskFlags.Procs.meets__implementation_3db9b6c296)

#print axioms solution
