-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.source_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:13:35.881765+00:00
-- url     : https://prove2.me/submissions/7dbeddfc-2c6e-470f-b624-0a470f5be646

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle031
import Definitions.Def_ThreeSum1960614_Machine_Bundle032
import Definitions.Def_ThreeSum1960614_Machine_Bundle033
import Definitions.Def_ThreeSum1960614_Machine_Bundle034
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
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
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
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
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

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceCatalogCosts
end ThreeSum.BlockSourceCatalogCosts
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightZetaStages
end ThreeSum.LightZetaStages
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankSources
end ThreeSum.SharedReportingBankSources
namespace ThreeSum.SourceBandBankLayout
end ThreeSum.SourceBandBankLayout
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts
end ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts
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
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaStages
end ThreeSum1960614.Machine.ThreeSum.LightZetaStages
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales

namespace ThreeSum1960614.Machine

/-!
# Packed retained source banks indexed by occurrence vectors

Each bank retains its compact masks, coefficients, endpoints, flags, and
both complete source-stage families. Shared temporary transform workspace
follows all banks. Two header cells per occurrence contain the stage bases.
This layout lets the next actual source call preserve every earlier bank.
-/

namespace ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum.LightBlockSourceBatchLayout


open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightZetaStages
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaStages

















theorem banks_le_slot (base count W cut i : ℕ) : _root_.ThreeSum.LightBlockSourceBatchLayout.banks base count ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut i :=
  Nat.le_add_right _ _

theorem slot_mono (base count W cut : ℕ) : Monotone (_root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _



theorem right_ge_left (base count W cut i : ℕ) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count W cut i ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count W cut i := Nat.le_add_right _ _

theorem right_end (base count W cut i : ℕ) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count W cut i+_root_.ThreeSum.LightBlockSourceBatchLayout.family W cut = _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut (i+1) := by
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase _root_.ThreeSum.LightBlockSourceBatchLayout.flags _root_.ThreeSum.LightBlockSourceBatchLayout.rawRight _root_.ThreeSum.LightBlockSourceBatchLayout.rawLeft _root_.ThreeSum.LightBlockSourceBatchLayout.coeff1 _root_.ThreeSum.LightBlockSourceBatchLayout.coeff0 _root_.ThreeSum.LightBlockSourceBatchLayout.slot _root_.ThreeSum.LightBlockSourceBatchLayout.stride
  ring

theorem right_end_le_masks {base count W cut i : ℕ} (hi : i < count) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count W cut i+_root_.ThreeSum.LightBlockSourceBatchLayout.family W cut ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase base count W cut := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.right_end]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.slot_mono base count W cut (by omega)



theorem banks_le_work (base count W cut : ℕ) : _root_.ThreeSum.LightBlockSourceBatchLayout.banks base count ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut := by
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_slot base count W cut count
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.work _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut _root_.ThreeSum.LightBlockSourceBatchLayout.bitBase _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase
  omega





theorem masks_le_work (base count W cut : ℕ) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase base count W cut ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut := by
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.work _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut _root_.ThreeSum.LightBlockSourceBatchLayout.bitBase
  omega

















end ThreeSum.LightBlockSourceBatchLayout

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





theorem work_add (base count W cut : ℕ) : _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut=base+_root_.ThreeSum.LightBlockSourceBatchLayout.work 0 count W cut := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts.work_address]
  omega

theorem host_space_add (base free h J : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space (base+free) h J=
      base+_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space free h J := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space _root_.ThreeSum.LightSourcePreparation.space
    _root_.ThreeSum.LightBlockSourceHashes.space _root_.ThreeSum.LightSourceMaskFlags.space _root_.ThreeSum.LightSourceRetainedStages.space
  omega

theorem complete_end (base h J cut i : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space
      (_root_.ThreeSum.LightBlockSourceBatchLayout.work (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt base h J cut i) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut) h J=
      _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt base h J cut (i+1) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.work_add,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.host_space_add]
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span
  ring

theorem baseAt_mono (base h J cut : ℕ) : Monotone (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt base h J cut) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _

theorem work_le_end (base h J cut i : ℕ) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.work (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt base h J cut i) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt base h J cut (i+1) := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.complete_end]
  exact (Nat.le_add_right _ _).trans (le_max_left _ _)











end ThreeSum.SourceBandBankLayout

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
section

theorem ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.source_bounds__implementation_5c560a8d86 {base NB NC g h J cut i s : ℕ}
    (hi : i < _root_.ThreeSum.SourceBandPairSlices.count NB NC g)
    (hs : s < _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.leftCell base h J cut i s < _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish base NB NC g h J cut ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.rightCell base h J cut i s < _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish base NB NC g h J cut ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.leftBase base h J cut i s+(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish base NB NC g h J cut ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.rightBase base h J cut i s+(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish base NB NC g h J cut := by
  have hend := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt_mono (_root_.ThreeSum.SourceBandBankData.first base) h J cut
    (show i+1 ≤ _root_.ThreeSum.SourceBandPairSlices.count NB NC g by omega)
  have hwork := (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.work_le_end (_root_.ThreeSum.SourceBandBankData.first base) h J cut i).trans hend
  change _root_.ThreeSum.LightBlockSourceBatchLayout.work (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.bankBase base h J cut i)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish base NB NC g h J cut at hwork
  have hhead := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_work (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.bankBase base h J cut i)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.banks at hhead
  have hright := (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.right_end_le_masks
    (base := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.bankBase base h J cut i) (W := J*(464*h)) (cut := cut) hs).trans
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.masks_le_work _ _ _ _)
  have hleft := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.right_ge_left (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.bankBase base h J cut i)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut s
  change _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.leftBase base h J cut i s ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.rightBase base h J cut i s at hleft
  change _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.rightBase base h J cut i s+(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤
    _root_.ThreeSum.LightBlockSourceBatchLayout.work (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.bankBase base h J cut i)
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut at hright
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.leftCell _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.rightCell
  omega
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.source_bounds__implementation_5c560a8d86) := (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.source_bounds__implementation_5c560a8d86)

#print axioms solution
