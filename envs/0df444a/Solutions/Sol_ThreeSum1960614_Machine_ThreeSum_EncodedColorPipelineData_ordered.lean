-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.ordered
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:41:40.769307+00:00
-- url     : https://prove2.me/submissions/89569c85-346a-4b85-a476-db94a17765d4

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle035
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
import Definitions.Def_ThreeSum1962Source_Bundle15
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
import Mathlib.Data.Finset.Image
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
import Mathlib.Data.Int.Basic
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
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
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

local instance platformRadixNonzero_be8565bf28 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.EncodedColorCoverData
end ThreeSum.EncodedColorCoverData
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorPipelineData
end ThreeSum.EncodedColorPipelineData
namespace ThreeSum.EncodedColorWantedData
end ThreeSum.EncodedColorWantedData
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightCoverKeyData
end ThreeSum.LightCoverKeyData
namespace ThreeSum.LightEncodedColorFiniteSources
end ThreeSum.LightEncodedColorFiniteSources
namespace ThreeSum.LightLocalCoverRetention
end ThreeSum.LightLocalCoverRetention
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceBandPairData
end ThreeSum.SourceBandPairData
namespace ThreeSum.SourceFiniteData
end ThreeSum.SourceFiniteData
namespace ThreeSum.WantedResidueKeys
end ThreeSum.WantedResidueKeys
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorCoverData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorCoverData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
end ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedData
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData
end ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData
namespace ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources
end ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
end ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
namespace ThreeSum1960614.Machine.ThreeSum.SourceFiniteData
end ThreeSum1960614.Machine.ThreeSum.SourceFiniteData
namespace ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs
end ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales
namespace ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys
end ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys

namespace ThreeSum1960614.Machine

/-! # One compact retained layout for a selected color -/

namespace ThreeSum.EncodedColorLayout
open _root_.ThreeSum.EncodedColorLayout























theorem free_le_normalizedEnd (free n g : ℕ) : free+8 ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g := by
  unfold _root_.ThreeSum.EncodedColorLayout.normalizedEnd _root_.ThreeSum.LightBandRawA.space _root_.ThreeSum.LightBandRawA.positionBase _root_.ThreeSum.LightBandRawA.ownerBase
    _root_.ThreeSum.LightBandRawA.capacity _root_.ThreeSum.EncodedColorLayout.vals _root_.ThreeSum.EncodedColorLayout.rec _root_.ThreeSum.EncodedColorLayout.tables _root_.ThreeSum.EncodedColorLayout.ce _root_.ThreeSum.EncodedColorLayout.cv _root_.ThreeSum.EncodedColorLayout.be _root_.ThreeSum.EncodedColorLayout.bv _root_.ThreeSum.EncodedColorLayout.ae _root_.ThreeSum.EncodedColorLayout.av _root_.ThreeSum.EncodedColorLayout.class2 _root_.ThreeSum.EncodedColorLayout.class1 _root_.ThreeSum.EncodedColorLayout.class0 _root_.ThreeSum.EncodedColorLayout.colors
  omega



theorem free_le_prime (free n g : ℕ) : free+8 ≤ _root_.ThreeSum.EncodedColorLayout.prime free n g := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout.free_le_normalizedEnd free n g
  unfold _root_.ThreeSum.EncodedColorLayout.prime
  omega

theorem prime_le_cover (free n g M y : ℕ) : _root_.ThreeSum.EncodedColorLayout.prime free n g+6 ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y := by
  unfold _root_.ThreeSum.EncodedColorLayout.cover _root_.ThreeSum.EncodedColorPrimeData.nextFree _root_.ThreeSum.EncodedColorPrimeData.prefixBase _root_.ThreeSum.EncodedColorPrimeData.poolBase
  omega



end ThreeSum.EncodedColorLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained local-cover tables survive reuse of the returned free region -/

namespace ThreeSum.LightLocalCoverRetention
open _root_.ThreeSum.LightLocalCoverRetention


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata

set_option maxHeartbeats 1000000

theorem base_le_nextFree (base h : ℕ) : base ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.bitPtr
    _root_.ThreeSum.LightCoverGreedy.total
  omega













end ThreeSum.LightLocalCoverRetention

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Two retained original-band catalogs and one shared empty histogram -/

namespace ThreeSum.SourceBandPairData
open _root_.ThreeSum.SourceBandPairData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition






theorem work_ge (base n g m : ℕ) : base ≤ _root_.ThreeSum.SourceBandLayout.work base n g m := by
  unfold _root_.ThreeSum.SourceBandLayout.work _root_.ThreeSum.SourceBandLayout.hist _root_.ThreeSum.SourceBandLayout.data
  omega

theorem ordered (base NL NR g m : ℕ) :
    _root_.ThreeSum.SourceBandPairData.leftBase base ≤ _root_.ThreeSum.SourceBandPairData.rightBase base NL g m ∧
    _root_.ThreeSum.SourceBandPairData.rightBase base NL g m ≤ _root_.ThreeSum.SourceBandPairData.zeroBase base NL NR g m ∧
    _root_.ThreeSum.SourceBandPairData.zeroBase base NL NR g m < _root_.ThreeSum.SourceBandPairData.next base NL NR g m := by
  exact ⟨_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.work_ge _ _ _ _,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.work_ge _ _ _ _,by unfold _root_.ThreeSum.SourceBandPairData.next; omega⟩















end ThreeSum.SourceBandPairData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The retained cover, output layers, and exact global key array

This bundle is produced by the actual cover/key host and remains valid when
later phases use its computed next free address. In particular the output
index decoder can read the original layer masks without reconstructing them.
-/

namespace ThreeSum.LightCoverKeyData
open _root_.ThreeSum.LightCoverKeyData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000





theorem layer_end_le_header (free h J : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover free h+_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.keyHeader free h J := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.keyHeader _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.scratch
  omega

theorem afterCover_le_keyEnd (free h J : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover free h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd free h J := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.layer_end_le_header free h J
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd
  omega











end ThreeSum.LightCoverKeyData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Read source controls from the actually constructed local-cover header -/

namespace ThreeSum.EncodedColorCoverData
open _root_.ThreeSum.EncodedColorCoverData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs

theorem header_end (free h J : ℕ) : free+20 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd free h J :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention.base_le_nextFree (_root_.ThreeSum.LightLocalCoverInit.base free) h).trans
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.afterCover_le_keyEnd free h J)



end ThreeSum.EncodedColorCoverData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Keep the complete finite source catalog below its exact returned end -/

namespace ThreeSum.SourceFiniteData
open _root_.ThreeSum.SourceFiniteData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

theorem source_ends (base NL NR g h J cut : ℕ) :
    base+3 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish base NL NR g h J cut ∧
    _root_.ThreeSum.SourceBandPairData.next (_root_.ThreeSum.LightSourceControlsHost.sourceBase base) NL NR g
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish base NL NR g h J cut ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.bankHeader (_root_.ThreeSum.LightSourceControlsHost.sourceBase base) NL NR g h J+5 ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish base NL NR g h J cut := by
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.ordered (_root_.ThreeSum.LightSourceControlsHost.sourceBase base)
    NL NR g (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.finish _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt _root_.ThreeSum.SourceBandBankData.first _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.bankHeader
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.occurrenceBase _root_.ThreeSum.LightSourceControlsHost.sourceBase
  unfold _root_.ThreeSum.SourceBandPairData.leftBase _root_.ThreeSum.LightSourceControlsHost.sourceBase at ho
  omega



end ThreeSum.SourceFiniteData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact reusable memory boundary after the actual wanted-pair output -/

namespace ThreeSum.EncodedColorWantedData
open _root_.ThreeSum.EncodedColorWantedData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.WantedResidueKeys
open _root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys



theorem header_le_nextFree (out M : ℕ) (left right : ℕ → ℤ) (NL NR : ℕ) (shift : ℤ) :
    out+4 ≤ _root_.ThreeSum.EncodedColorWantedData.nextFree out M left right NL NR shift := by
  unfold _root_.ThreeSum.EncodedColorWantedData.nextFree _root_.ThreeSum.LightWantedSetup.pairBase _root_.ThreeSum.LightSourceBucketSetup.next _root_.ThreeSum.LightWantedSetup.bucketBase
    _root_.ThreeSum.LightWantedSetup.rightCodes _root_.ThreeSum.LightWantedSetup.leftCodes
  omega





end ThreeSum.EncodedColorWantedData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained finite normalization and actual source controls in one contract -/

namespace ThreeSum.LightEncodedColorFiniteSources
open _root_.ThreeSum.LightEncodedColorFiniteSources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales





theorem free_le_base (free n p M : ℕ) [NeZero M] (xs : List ℤ) : free ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources.base free n p M xs := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedData.header_le_nextFree
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.wantedFree free (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) xs.length)
    M (_root_.ThreeSum.LightGuardedWanted.left p xs)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
    (3*xs.length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
    (_root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.selected M p xs (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) : ℤ)
  have hk := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorCoverData.header_end free (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))
  change _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources.base free n p M xs at h
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.wantedFree at h
  omega

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ}



end ThreeSum.LightEncodedColorFiniteSources

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
section

theorem ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.ordered__implementation_ac311fd362 (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    _root_.ThreeSum.EncodedColorLayout.prime free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)+6 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n ∧
    free+8 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n ∧ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.wantedHeader free n (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length+4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC+3 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC+5 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC := by
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout.prime_le_cover free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n)
  have hf := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout.free_le_prime free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources.free_le_base (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n) n
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC)
  have hw := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedData.header_le_nextFree
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.wantedHeader free n (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)
    (_root_.ThreeSum.LightGuardedWanted.left (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC))
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
    (3*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
    (_root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.selected (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
      (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC) (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) : ℤ)
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.source_ends (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC) B.length C.length
    (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)
  change _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n at hp
  change _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC at hc hw
  change _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC+3 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC ∧ _ ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC+5 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC at hs
  exact ⟨hp,by omega,hc,hw,hs.1,hs.2.2⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.ordered__implementation_ac311fd362) := (@ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.ordered__implementation_ac311fd362)

#print axioms solution
