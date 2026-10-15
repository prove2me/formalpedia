-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:32:37.30235+00:00
-- url     : https://prove2.me/submissions/60b9ffce-853d-4168-9e1d-3ae6678953b9

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle08
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
import Mathlib.Data.Nat.Notation
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBlockCoefficients_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightMaskHashes_meets
import Theorems.Thm_ThreeSum_BlockCoefficientRows_rows_flat

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LightBlockCoefficients
end ThreeSum.LightBlockCoefficients
namespace ThreeSum.LightBlockSourceHashes
end ThreeSum.LightBlockSourceHashes
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients
end ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

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
# Constructing the positional one-hot coefficient arrays

The program reads one map occurrence per block. It copies both symbol rows
of that map and multiplies them by the block's radix power. The powers are
built internally. All original map and occurrence data are preserved.
-/

namespace ThreeSum.LightBlockCoefficients
open _root_.ThreeSum.LightBlockCoefficients


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}















theorem row_end_le {J L j : ℕ} (hj : j < J) : j*L+L ≤ J*L := by
  calc
    j*L+L = (j+1)*L := by ring
    _ ≤ J*L := Nat.mul_le_mul_right L (by omega)











end ThreeSum.LightBlockCoefficients

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Reading constructed block coefficients in the flat mask order

The imperative coefficient constructor writes rows. The mask evaluator reads
one flat array. These lemmas identify the two layouts, including empty ground
sets, and specialize them to the unchanged schedule-occurrence encoding.
-/

namespace ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.BlockCoefficientRows


open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds





theorem flat_le {J L p U M : ℕ} {sel : ℕ → ℕ} {w : ℕ → ℕ → ℕ}
    (hp : 1 ≤ p) (hsel : ∀ j < J, sel j < M)
    (hbound : ∀ s < M, ∀ i < L, w s i ≤ U) {i : ℕ} (hi : i < J*L) :
    _root_.ThreeSum.BlockCoefficientRows.flat J L p sel w i ≤ p^J*U := by
  let c := (_root_.ThreeSum.BlockIndex.coordEquiv J L).symm ⟨i,hi⟩
  change (if h : i < J*L then _ else 0) ≤ _
  rw [dif_pos hi]
  exact Nat.mul_le_mul (Nat.pow_le_pow_right hp (Nat.le_of_lt c.1.isLt))
    (hbound _ (hsel _ c.1.isLt) _ c.2.isLt)



















end ThreeSum.BlockCoefficientRows

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBlockSourceHashes
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes.Procs.meets__implementation_154d8313d5 {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes.Procs P pMain)
    {μ : ℕ → ℤ} {J L p occ maps coeff0 coeff1 masks rawLeft rawRight n work U M : ℕ}
    (sel mask : ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 1 ≤ p)
    (hd : d+J*L+2 ≤ lim.depth) (hspace : _root_.ThreeSum.LightBlockSourceHashes.space work J L ≤ lim.space)
    (hocc : occ+J ≤ coeff0) (hmaps : maps+2*L*M ≤ coeff0)
    (hmasks : masks+n ≤ coeff0) (hc0 : coeff0+J*L ≤ coeff1)
    (hc1 : coeff1+J*L ≤ rawLeft) (hleft : rawLeft+n ≤ rawRight)
    (hright : rawRight+n ≤ work) (hword : (_root_.ThreeSum.LightBlockSourceHashes.word J L p U : ℤ) ≤ lim.word)
    (hsel : ∀ j < J, sel j < M)
    (hselRead : ∀ j < J, μ (occ+j) = (sel j : ℤ))
    (hread0 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+i) = (w0 s i : ℤ))
    (hread1 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+L+i) = (w1 s i : ℤ))
    (hbound0 : ∀ s < M, ∀ i < L, w0 s i ≤ U)
    (hbound1 : ∀ s < M, ∀ i < L, w1 s i ≤ U)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^(J*L)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [J,L,p,occ,maps,coeff0,coeff1,masks,rawLeft,rawRight,n,work]
      μ (_root_.ThreeSum.LightBlockSourceHashes.time J L n) (fun _ ν =>
        (∀ i < n, ν (rawLeft+i) =
          (_root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w0) (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w1) (J*L) (mask i) : ℤ)) ∧
        (∀ i < n, ν (rawRight+i) =
          (_root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w1) (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w0) (J*L) (mask i) : ℤ)) ∧
        _root_.ThreeSum.LightBlockCoefficients.Rows ν coeff0 coeff1 L p sel w0 w1 J ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν coeff0) := by
  have hsc : work+(J+1) ≤ lim.space :=
    (Nat.add_le_add_left (le_max_left _ _) work).trans hspace
  have hsh : work+(J*L+1) ≤ lim.space :=
    (Nat.add_le_add_left (le_max_right _ _) work).trans hspace
  have hcw : (_root_.ThreeSum.LightBlockCoefficients.word J p U : ℤ) ≤ lim.word := by
    have hh : _root_.ThreeSum.LightBlockCoefficients.word J p U ≤ _root_.ThreeSum.LightBlockSourceHashes.word J L p U := by unfold _root_.ThreeSum.LightBlockSourceHashes.word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hhw : (_root_.ThreeSum.LightOneHot.word (J*L) (p^J*U) : ℤ) ≤ lim.word := by
    have hh : _root_.ThreeSum.LightOneHot.word (J*L) (p^J*U) ≤ _root_.ThreeSum.LightBlockSourceHashes.word J L p U := by unfold _root_.ThreeSum.LightBlockSourceHashes.word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwidth : (J : ℤ)*(L : ℤ) ≤ lim.word := by
    have hh : J*L ≤ lim.space := by omega
    exact (by exact_mod_cast hh : (J : ℤ)*(L : ℤ) ≤ lim.space).trans hw
  have hb0 : ∀ i < J*L, _root_.ThreeSum.BlockCoefficientRows.flat J L p sel w0 i ≤ p^J*U :=
    fun _ hi => _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.flat_le hp hsel hbound0 hi
  have hb1 : ∀ i < J*L, _root_.ThreeSum.BlockCoefficientRows.flat J L p sel w1 i ≤ p^J*U :=
    fun _ hi => _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.flat_le hp hsel hbound1 hi
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body S.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes.body _root_.ThreeSum.LightBlockSourceHashes.time
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients.meets (d := d+1) (μ := μ)
    (J := J) (L := L) (p := p) (occ := occ) (maps := maps)
    (dst0 := coeff0) (dst1 := coeff1) (work := work) (U := U) (M := M)
    S.coefficients S.powers S.scale sel w0 w1 hw hp hocc hmaps hc0 (by omega)
    hsc hcw (by omega) hsel hselRead hread0 hread1 hbound0 hbound1
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockCoefficients.time, _root_.ThreeSum.LightBlockCoefficients.roundTime, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightScaleArray.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockCoefficients.time, _root_.ThreeSum.LightBlockCoefficients.roundTime, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightScaleArray.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockCoefficients.time, _root_.ThreeSum.LightBlockCoefficients.roundTime, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightScaleArray.time] <;> omega)
     on_goal -1 => (rintro r μ₁ ⟨rows, kept₁, _⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  obtain ⟨rows0,rows1⟩ := _root_.ThreeSum.BlockCoefficientRows.rows_flat rows
  have masks₁ : ∀ i < n, μ₁ (masks+i) = (mask i : ℤ) := by
    intro i hi
    exact (kept₁ _ (by omega)).trans (hmaskRead i hi)
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskHashes.meets (d := d+1) (μ := μ₁)
    (L := J*L) (masks := masks) (dst := rawLeft) (n := n)
    (src0 := coeff0) (src1 := coeff1) (work := work) (U := p^J*U)
    S.hashes S.powers S.onehot mask (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w0) (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w1)
    hw (by omega) hsh (by omega) (by omega) hc1 (by omega) hhw masks₁ hmaskLt
    rows0 rows1 hb0 hb1
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hl _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hl ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockCoefficients.time, _root_.ThreeSum.LightBlockCoefficients.roundTime, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightScaleArray.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockCoefficients.time, _root_.ThreeSum.LightBlockCoefficients.roundTime, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightScaleArray.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockCoefficients.time, _root_.ThreeSum.LightBlockCoefficients.roundTime, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightScaleArray.time] <;> omega)
     on_goal -1 => (rintro r μ₂ ⟨leftValues, _, kept₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have masks₂ : ∀ i < n, μ₂ (masks+i) = (mask i : ℤ) := by
    intro i hi
    exact (kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (masks₁ i hi)
  have rows0₂ : ∀ i < J*L, μ₂ (coeff0+i) = (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w0 i : ℤ) := by
    intro i hi
    exact (kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (rows0 i hi)
  have rows1₂ : ∀ i < J*L, μ₂ (coeff1+i) = (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w1 i : ℤ) := by
    intro i hi
    exact (kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (rows1 i hi)
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskHashes.meets (d := d+1) (μ := μ₂)
    (L := J*L) (masks := masks) (dst := rawRight) (n := n)
    (src0 := coeff1) (src1 := coeff0) (work := work) (U := p^J*U)
    S.hashes S.powers S.onehot mask (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w1) (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w0)
    hw (by omega) hsh (by omega) (by omega) (by omega) hright hhw masks₂ hmaskLt
    rows1₂ rows0₂ hb1 hb0
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockCoefficients.time, _root_.ThreeSum.LightBlockCoefficients.roundTime, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightScaleArray.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockCoefficients.time, _root_.ThreeSum.LightBlockCoefficients.roundTime, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightScaleArray.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockCoefficients.time, _root_.ThreeSum.LightBlockCoefficients.roundTime, _root_.ThreeSum.LightMaskHashes.time, _root_.ThreeSum.LightOneHot.time, _root_.ThreeSum.LightScaleArray.time] <;> omega)
     on_goal -1 => (rintro r μ₃ ⟨rightValues, _, kept₃⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨?_,rightValues,?_,?_⟩
  · intro i hi
    exact (kept₃ _ ⟨by omega,Or.inl (by omega)⟩).trans (leftValues i hi)
  · intro a ha i hi
    have he := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients.row_end_le (L := L) ha
    constructor
    · exact (kept₃ _ ⟨by omega,Or.inl (by omega)⟩).trans
        ((kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (rows a ha i hi).1)
    · exact (kept₃ _ ⟨by omega,Or.inl (by omega)⟩).trans
        ((kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (rows a ha i hi).2)
  · intro a ha
    exact (kept₃ _ ⟨by omega,Or.inl (by omega)⟩).trans
      ((kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (kept₁ a ha))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes.Procs.meets__implementation_154d8313d5) := (@ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes.Procs.meets__implementation_154d8313d5)

#print axioms solution
