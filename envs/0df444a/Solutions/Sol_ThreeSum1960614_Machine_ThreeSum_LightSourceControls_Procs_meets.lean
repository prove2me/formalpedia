-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSourceControls.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:10:19.142367+00:00
-- url     : https://prove2.me/submissions/ee8f9fdd-e2f7-49c3-87f2-151fc8f62e9f

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
import Definitions.Def_ThreeSum1960614_Machine_Bundle029
import Definitions.Def_ThreeSum1960614_Machine_Bundle030
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
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
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
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_log2_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightDownsetSize_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightNatPower_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceControlsSpan_meets

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockSourceCatalogCosts
end ThreeSum.BlockSourceCatalogCosts
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightNatPower
end ThreeSum.LightNatPower
namespace ThreeSum.LightSourceControls
end ThreeSum.LightSourceControls
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceBandBankLayout
end ThreeSum.SourceBandBankLayout
namespace ThreeSum.SourceBandBanksCosts
end ThreeSum.SourceBandBanksCosts
namespace ThreeSum.SourceControlLayout
end ThreeSum.SourceControlLayout
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts
end ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
end ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightNatPower
end ThreeSum1960614.Machine.ThreeSum.LightNatPower
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceControls
end ThreeSum1960614.Machine.ThreeSum.LightSourceControls
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts
end ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceControlLayout
end ThreeSum1960614.Machine.ThreeSum.SourceControlLayout
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales

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
# Original-input histograms give the exact independently trimmed sources

The histogram keys retain the first modular reduction and the signed carry
offset. Looking up the endpoint's final residue therefore counts precisely
the original divisibility condition in `BlockEncoding`. An explicit finite
enumeration accounts for every original input incidence once.
-/

namespace ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.BlockSourceEncoding


open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
open scoped _root_.BigOperators

set_option maxHeartbeats 1000000











@[simp] theorem modulus_cast (h J : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J : ℤ) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus,Nat.cast_pow]

section OriginalSources

variable {β : Type*} [DecidableEq β]





end OriginalSources

end ThreeSum.BlockSourceEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Scalar integer powers in the benchmark language

The exponent is a size parameter, so a loop of that many multiplications
has polynomial-logarithmic cost in the applications below. No power table
or auxiliary memory is required.
-/

namespace ThreeSum.LightNatPower
open _root_.ThreeSum.LightNatPower


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem bounded_meets {p b e : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.body) (μ : ℕ → ℤ)
    (he : (e : ℤ) ≤ lim.word)
    (hword : (((b+1)^(e+1) : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [b,e] μ (_root_.ThreeSum.LightNatPower.time e)
      (fun r μ' => r = ((b^e : ℕ) : ℤ) ∧ μ' = μ) := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.meets hp μ he
  intro i hi
  have hbase := Nat.pow_le_pow_left (show b ≤ b+1 by omega) i
  have hexp : (b+1)^i ≤ (b+1)^(e+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hz : ((b^i : ℕ) : ℤ) ≤ (((b+1)^(e+1) : ℕ) : ℤ) := by
    exact_mod_cast hbase.trans hexp
  exact hz.trans hword





end ThreeSum.LightNatPower

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact shared-bank dimensions and charge of the actual catalog

There are two stage families for each original band and occurrence vector.
The decoder and bank-loop overhead are included. Neither the number of
complete output subsets nor the three-valued query lift multiplies this
construction.
-/

namespace ThreeSum.BlockSourceCatalogCosts
open _root_.ThreeSum.BlockSourceCatalogCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout



theorem work_address (base count W cut : ℕ) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut =
      base+count*(_root_.ThreeSum.LightBlockSourceBatchLayout.stride W cut+2)+_root_.ThreeSum.SubsetAddress.downsetCap W cut+W+2 := by
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.work _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut _root_.ThreeSum.LightBlockSourceBatchLayout.bitBase _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase _root_.ThreeSum.LightBlockSourceBatchLayout.slot _root_.ThreeSum.LightBlockSourceBatchLayout.banks
  ring





















end ThreeSum.BlockSourceCatalogCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Complete source banks per common band with preserved earlier banks -/

namespace ThreeSum.SourceBandBankLayout
open _root_.ThreeSum.SourceBandBankLayout


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder







theorem host_space_add (base free h J : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space (base+free) h J=
      base+_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space free h J := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space _root_.ThreeSum.LightSourcePreparation.space
    _root_.ThreeSum.LightBlockSourceHashes.space _root_.ThreeSum.LightSourceMaskFlags.space _root_.ThreeSum.LightSourceRetainedStages.space
  omega

















end ThreeSum.SourceBandBankLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact shared construction counts and finite encoder charge -/

namespace ThreeSum.SourceBandBanksCosts
open _root_.ThreeSum.SourceBandBanksCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress



















theorem span_eq (h J cut : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J cut=
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J*(_root_.ThreeSum.LightBlockSourceBatchLayout.stride (J*(464*h)) cut+2)+
      _root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut+J*(464*h)+2+_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space 0 h J := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.host_space_add
    (_root_.ThreeSum.LightBlockSourceBatchLayout.work 0 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut) 0 h J
  simp only [Nat.add_zero] at h
  rw [h,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts.work_address]
  omega











end ThreeSum.SourceBandBanksCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Arithmetic dimensions of the original shared source bank -/

namespace ThreeSum.SourceControlLayout
open _root_.ThreeSum.SourceControlLayout


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress









theorem scratch_eq (h J : ℕ) :
    _root_.ThreeSum.SourceControlLayout.scratch J (J*(464*h)) (Nat.log 2 ((464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+1))
      (Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J+1)) =
      _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space 0 h J := by
  unfold _root_.ThreeSum.SourceControlLayout.scratch _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space _root_.ThreeSum.LightSourcePreparation.space
    _root_.ThreeSum.LightBlockSourceHashes.space _root_.ThreeSum.LightSourceMaskFlags.space _root_.ThreeSum.LightSourceRetainedStages.space
    _root_.ThreeSum.LightPascal.tableSize
  omega

theorem stride_eq (W cut : ℕ) :
    _root_.ThreeSum.SourceControlLayout.stride W (_root_.ThreeSum.SubsetAddress.downsetCap W cut)=_root_.ThreeSum.LightBlockSourceBatchLayout.stride W cut+2 := by
  unfold _root_.ThreeSum.SourceControlLayout.stride _root_.ThreeSum.LightBlockSourceBatchLayout.stride _root_.ThreeSum.LightBlockSourceBatchLayout.family
  ring

theorem span_eq (h J cut : ℕ) :
    _root_.ThreeSum.SourceControlLayout.span J (J*(464*h)) (_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J)
      (Nat.log 2 ((464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+1)) (Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J+1)) =
      _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J cut := by
  unfold _root_.ThreeSum.SourceControlLayout.span
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceControlLayout.scratch_eq,_root_.ThreeSum1960614.Machine.ThreeSum.SourceControlLayout.stride_eq,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.span_eq]



end ThreeSum.SourceControlLayout

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightSourceControls.Procs.meets__implementation_3a43347ad9 {pMain : ℕ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.Procs P pMain)
    {μ : ℕ → ℤ} {h J cut dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(464*h)+5 ≤ lim.depth)
    (hcut : cut ≤ J*(464*h)) (hdst : dst+3 ≤ work)
    (hspace : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.space work h J ≤ lim.space) (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.word h J cut : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [J,464*h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,cut,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,dst,work]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.time h J) (fun r ν => r=(_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J cut : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.Seg ν dst (_root_.ThreeSum1960614.Machine.ThreeSum.SourceControlLayout.values h J cut) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst) := by
  have hall (x : ℕ) (hx : x ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.word h J cut) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hsSpan := hall (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.spanWord h J cut) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.word; omega)
  have hSpanAll (x : ℕ) (hx : x ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.spanWord h J cut) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hsSpan
  have hJ := hall J (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.word; omega)
  have hW := hall (J*(464*h)) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.word; omega)
  have hWZ : (J : ℤ)*(464*(h : ℤ)) ≤ lim.word := by exact_mod_cast hW
  have hWnonneg : (0 : ℤ) ≤ (J : ℤ)*(464*(h : ℤ)) := by positivity
  have hL := hall (464*h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.word; omega)
  have hLP := hall (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.word; omega)
  have hM := hall (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.word; omega)
  have hT := hall (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.word; omega)
  have hC := hall cut (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.word; omega)
  have hK := hSpanAll (_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.spanWord _root_.ThreeSum.SourceControlLayout.word; omega)
  have hS := hSpanAll (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.spanWord _root_.ThreeSum.SourceControlLayout.word; omega)
  have hSpanNat : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J cut ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.spanWord h J cut := by
    rw [← _root_.ThreeSum1960614.Machine.ThreeSum.SourceControlLayout.span_eq]
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.spanWord _root_.ThreeSum.SourceControlLayout.word
    omega
  have hSpan := hSpanAll (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J cut) hSpanNat
  have hPower := hall ((_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h+1)^(J+1)) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.word; omega)
  have hDownset := hall ((J*(464*h)+1)*2^(J*(464*h)+1)) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.word; omega)
  have hLogP := hall (2*((464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+1)+2) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.word; omega)
  have hLogPZ : 2*((464*(h : ℤ))*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ)+1)+2 ≤ lim.word := by exact_mod_cast hLogP
  have hLogE := hall (2*(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J+1)+2) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.word; omega)
  have hLogEZ : 2*((J*(464*h) : ℤ)*((_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ))+1)+2 ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hLogE
  have hMulP := hall ((464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.word; omega)
  have hMulPZ : (464*(h : ℤ))*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ) ≤ lim.word := by exact_mod_cast hMulP
  have hMulPNonneg : (0 : ℤ) ≤ (464*(h : ℤ))*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ) := by positivity
  have hMP := hall (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.word; omega)
  have hMPZ : (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ) ≤ lim.word := by exact_mod_cast hMP
  have hMPNonneg : (0 : ℤ) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ) := by positivity
  have hEndpoint := hall (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.word; omega)
  have hEndpointZ : (J*(464*h) : ℤ)*((_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ)) ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hEndpoint
  have hEndpointNonneg : (0 : ℤ) ≤ (J*(464*h) : ℤ)*((_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ)) := by positivity
  have hEndpointEq : (J*(464*h) : ℤ)*((_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ))+1 =
      ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J+1 : ℕ) : ℤ) := by
    simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus]
  have hMPG : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ) ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_cast] using hMPZ
  have hMPG0 : (0 : ℤ) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ) := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_cast] using hMPNonneg
  have hEndpointG : (J*(464*h) : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ)) ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_cast] using hEndpointZ
  have hEndpointG0 : (0 : ℤ) ≤ (J*(464*h) : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ)) := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_cast] using hEndpointNonneg
  have hLogEG : 2*((J*(464*h) : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ))+1)+2 ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_cast] using hLogEZ
  have hEndpointEqG : (J*(464*h) : ℤ)*(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ))+1 =
      ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J+1 : ℕ) : ℤ) := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_cast] using hEndpointEq
  have hhead : dst+3 ≤ lim.space := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.space at hspace; omega
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body C.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.body _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.time
  have hpowCall := _root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.bounded_meets (d := d+1) C.power μ hJ hPower
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hpowCall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hpowCall ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro rS ν₁ ⟨hrS, hν₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst ν₁
  have hrS' : rS=(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J : ℤ) := hrS
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (J * (464 * h) : ℕ) ?_ ?_ ?_
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
  have hsizeCall := _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.meets (d := d+1) (μ := μ) C.downset C.setup C.offset
    hw hspace hDownset hcut (by omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hsizeCall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hsizeCall ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro rK ν₂ ⟨hrK, kept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hlogCall₁ := _root_.ThreeSum1960614.Machine.Light.log2_meets (d := d+1) C.log ν₂ hLogP
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hlogCall₁ _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hlogCall₁ ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro rLogP ν₃ ⟨hrLogP, hν₃⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst ν₃
  have hlogCall₂ := _root_.ThreeSum1960614.Machine.Light.log2_meets (d := d+1) C.log ν₂ hLogE
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hlogCall₂ _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hlogCall₂ ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hEndpointEqG]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hEndpointEqG] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hEndpointEqG] <;> omega)
     on_goal -1 => (rintro rLogE ν₄ ⟨hrLogE, hν₄⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst ν₄
  have hspanCall := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsSpan.meets (d := d+1) C.span C.maximum ν₂ (by omega) hsSpan
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hspanCall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hspanCall ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrK, hrS', hrLogP, hrLogE, _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.spanWord]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hrK, hrS', hrLogP, hrLogE, _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.spanWord] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrK, hrS', hrLogP, hrLogE, _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.spanWord] <;> omega)
     on_goal -1 => (rintro rSpan ν₅ ⟨hrSpan, hν₅⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst ν₅
  have hrSpan' : rSpan=(_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J cut : ℤ) := by
    rw [← _root_.ThreeSum1960614.Machine.ThreeSum.SourceControlLayout.span_eq]
    exact hrSpan
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen dst (_root_.ThreeSum.SubsetAddress.downsetCap (J * (464 * h)) cut : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrK]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hrK] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrK] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 1) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrS']
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hrS'] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrS'] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 2) (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J cut : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrSpan']
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hrSpan'] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrSpan'] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J cut : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrSpan']
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hrSpan'] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrSpan'] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  dsimp only
  refine ⟨rfl,?_,?_⟩
  · intro i hi
    have hi' : i < 3 := by simpa [_root_.ThreeSum1960614.Machine.ThreeSum.SourceControlLayout.values] using hi
    interval_cases i <;> simp [_root_.ThreeSum1960614.Machine.ThreeSum.SourceControlLayout.values]
  · intro a ha
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact kept a (by omega)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSourceControls.Procs.meets__implementation_3a43347ad9) := (@ThreeSum1960614.Machine.ThreeSum.LightSourceControls.Procs.meets__implementation_3a43347ad9)

#print axioms solution
