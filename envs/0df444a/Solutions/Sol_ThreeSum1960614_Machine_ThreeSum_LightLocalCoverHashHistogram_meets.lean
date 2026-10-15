-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHashHistogram.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:40:54.541812+00:00
-- url     : https://prove2.me/submissions/9fd949ef-9bfd-4a6e-978f-5ed800f0053d

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
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
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
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
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightHistogram_histogram_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightMaskHashes_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightResidues_residues_ends
import Theorems.Thm_ThreeSum_OneHotMask_eval_le

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightHashHistogram
end ThreeSum.LightHashHistogram
namespace ThreeSum.LightLocalCoverHashHistogram
end ThreeSum.LightLocalCoverHashHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightHashHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHashHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHashHistogram
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHashHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues

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













theorem residues_meets {pResidues pEmod : ℕ}
    (hres : P[pResidues]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residuesBody pEmod))
    (hem : P[pEmod]? = some _root_.ThreeSum1960614.Machine.Light.emodBody)
    {μ : ℕ → ℤ} {src dst n p work U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hp : 0 < p) (hsrc : src + n ≤ work) (hdst : dst + n ≤ work)
    (hspace : work + (Nat.log 2 (U + 1) + 2) ≤ lim.space)
    (hsep : _root_.Light.Apart src n dst n) (hc : |c| ≤ 1)
    (hword : (4 * U + 4 * p + 16 : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src + i)| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pResidues d [src, dst, n, p, work, c] μ (_root_.ThreeSum.LightResidues.residuesTime n U)
      fun _ μ' =>
        (∀ i < n, μ' (dst + i) = (_root_.ThreeSum.LightResidues.residue p c (μ (src + i)) : ℤ)) ∧
          _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work dst n := by
  exact _root_.ThreeSum1960614.Machine.Light.Meets.of_body hres (_root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residues_ends hem hw hd hp hsrc hdst hspace hsep hc hword hvalues)

end ThreeSum.LightResidues

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightLocalCoverHashHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHashHistogram

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightHashHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHashHistogram
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHashHistogram.meets__implementation_95dafa02de {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightHashHistogram.Procs P pMain)
    {μ : ℕ → ℤ} {L masks raw codes hist n src0 src1 p work U : ℕ}
    (mask w0 w1 : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+2 ≤ lim.depth)
    (hp : 0 < p) (hspace : _root_.ThreeSum.LightHashHistogram.space work L U ≤ lim.space)
    (hmasks : masks+n ≤ raw) (hsrc0 : src0+L ≤ raw) (hsrc1 : src1+L ≤ raw)
    (hraw : raw+n ≤ codes) (hcodes : codes+n ≤ hist) (hhist : hist+p ≤ work)
    (hword : (_root_.ThreeSum.LightHashHistogram.word L p U : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [L,masks,raw,codes,hist,n,src0,src1,p,work] μ (_root_.ThreeSum.LightHashHistogram.time L n p U)
      (fun _ μ' =>
        (∀ i < n, μ' (codes+i) = (_root_.ThreeSum.LightHashHistogram.code L p mask w0 w1 i : ℤ)) ∧
        (∀ r < p, μ' (hist+r) = (_root_.ThreeSum.LightHistogram.count (_root_.ThreeSum.LightHashHistogram.code L p mask w0 w1) r n : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ μ' raw ∧ _root_.ThreeSum.LightLocalCoverHashHistogram.Preserved μ μ' work raw codes hist n p) := by
  have hspow : work+(L+1) ≤ lim.space :=
    (Nat.add_le_add_left (le_max_left _ _) work).trans hspace
  have hsmod : work+(Nat.log 2 (L*U+1)+2) ≤ lim.space :=
    (Nat.add_le_add_left (le_max_right _ _) work).trans hspace
  have hsw : work ≤ lim.space := by omega
  have hhashWord : (_root_.ThreeSum.LightOneHot.word L U : ℤ) ≤ lim.word := by
    have hh : _root_.ThreeSum.LightOneHot.word L U ≤ _root_.ThreeSum.LightHashHistogram.word L p U := by unfold _root_.ThreeSum.LightHashHistogram.word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hmodWord : (4*(L*U : ℕ)+4*p+16 : ℤ) ≤ lim.word := by
    have hh : 4*(L*U)+4*p+16 ≤ _root_.ThreeSum.LightHashHistogram.word L p U := by unfold _root_.ThreeSum.LightHashHistogram.word; omega
    exact (by exact_mod_cast hh : (4*(L*U : ℕ)+4*p+16 : ℤ) ≤ (word L p U : ℤ)).trans hword
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body S.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightHashHistogram.body _root_.ThreeSum.LightHashHistogram.time
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskHashes.meets (d := d+1) (μ := μ) (L := L) (masks := masks)
    (dst := raw) (n := n) (src0 := src0) (src1 := src1) (work := work) (U := U)
    S.hashes S.powers S.onehot mask w0 w1 hw (by omega) hspow hmasks hsrc0 hsrc1
    (by omega) hhashWord hmaskRead hmaskLt hread0 hread1 hbound0 hbound1
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hh _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hh ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightResidues.residuesTime, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightResidues.residuesTime, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightResidues.residuesTime, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime] <;> omega)
     on_goal -1 => (rintro value₀ μ₁ ⟨rawValues, _, kept₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hrawBound : ∀ i < n, |μ₁ (raw+i)| ≤ ((L*U : ℕ) : ℤ) := by
    intro i hi
    rw [rawValues i hi,abs_of_nonneg (Int.natCast_nonneg _)]
    exact Int.ofNat_le.mpr (_root_.ThreeSum.OneHotMask.eval_le (m := mask i) hbound0 hbound1)
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residues_meets (d := d+1) (μ := μ₁)
    (src := raw) (dst := codes) (n := n) (p := p) (work := work) (U := L*U) (c := 1)
    S.residues S.emod hw (by omega) hp (by omega) (by omega) hsmod (Or.inl hraw)
    (by norm_num) hmodWord hrawBound
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightResidues.residuesTime, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightResidues.residuesTime, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightResidues.residuesTime, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime] <;> omega)
     on_goal -1 => (rintro value₁ μ₂ ⟨residueValues, kept₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hcodeValues : ∀ i < n, μ₂ (codes+i) = (_root_.ThreeSum.LightHashHistogram.code L p mask w0 w1 i : ℤ) := by
    intro i hi
    rw [residueValues i hi,rawValues i hi]
    rfl
  have hcodeLt : ∀ i < n, _root_.ThreeSum.LightHashHistogram.code L p mask w0 w1 i < p := by
    intro i hi
    exact _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_lt hp 1 _
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogram_meets (d := d+1) (μ := μ₂)
    (src := codes) (dst := hist) (n := n) (p := p) S.hist S.fill
    (_root_.ThreeSum.LightHashHistogram.code L p mask w0 w1) hw (by omega) (by omega) (by omega) (Or.inl hcodes)
    hcodeValues hcodeLt
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hh _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hh ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightResidues.residuesTime, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightResidues.residuesTime, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightResidues.residuesTime, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime] <;> omega)
     on_goal -1 => (rintro value₂ μ₃ ⟨counts, kept₃⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨?_,counts,?_,?_⟩
  · intro i hi
    change μ₃ (codes+i) = _
    rw [kept₃ _ (Or.inl (by omega))]
    exact hcodeValues i hi
  · intro a ha
    change μ₃ a = μ a
    rw [kept₃ _ (Or.inl (by omega)),kept₂ _ ⟨by omega,Or.inl (by omega)⟩]
    exact kept₁ a ⟨by omega,Or.inl ha⟩
  · intro a ha hrawOut hcodeOut hhistOut
    change μ₃ a = μ a
    rw [kept₃ a hhistOut,kept₂ a ⟨ha,hcodeOut⟩]
    exact kept₁ a ⟨ha,hrawOut⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHashHistogram.meets__implementation_95dafa02de) := (@ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHashHistogram.meets__implementation_95dafa02de)

#print axioms solution
