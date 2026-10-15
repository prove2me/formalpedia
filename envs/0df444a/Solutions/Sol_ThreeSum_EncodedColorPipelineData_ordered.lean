-- Prove2me | solution 1 for ThreeSum.EncodedColorPipelineData.ordered
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:43:15.289018+00:00
-- url     : https://prove2.me/submissions/153849ab-1ccb-4290-80e5-62840b99c61a

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
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
import Mathlib.Algebra.Order.Field.Basic
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Data.Int.Cast.Lemmas
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
import Mathlib.Data.Nat.Cast.Order.Ring
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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverMetadata
end ThreeSum.LightLocalCoverMetadata
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceFiniteInputs
end ThreeSum.SourceFiniteInputs
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
namespace ThreeSum.WantedResidueKeys
end ThreeSum.WantedResidueKeys

section


/-! # Retained local-cover tables survive reuse of the returned free region -/

namespace ThreeSum.LightLocalCoverRetention

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMetadata

set_option maxHeartbeats 1000000

theorem base_le_nextFree (base h : ℕ) : base ≤ nextFree base h := by
  unfold nextFree scheduleMaps work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr
    LightCoverGreedy.total
  omega




















































end ThreeSum.LightLocalCoverRetention

end

section


/-!
# The retained cover, output layers, and exact global key array

This bundle is produced by the actual cover/key host and remains valid when
later phases use its computed next free address. In particular the output
index decoder can read the original layer masks without reconstructing them.
-/

namespace ThreeSum.LightCoverKeyData

open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000







theorem layer_end_le_header (free h J : ℕ) :
    LightCoverKeys.afterCover free h+outputCount (512*h) h ≤ LightCoverKeys.keyHeader free h J := by
  unfold LightCoverKeys.keyHeader LightGlobalKeys.scratch
  omega

theorem afterCover_le_keyEnd (free h J : ℕ) : LightCoverKeys.afterCover free h ≤ keyEnd free h J := by
  have hh := layer_end_le_header free h J
  unfold keyEnd
  omega






















































end ThreeSum.LightCoverKeyData

end

section


/-! # Two retained original-band catalogs and one shared empty histogram -/

namespace ThreeSum.SourceBandPairData

open Light BandPartition






theorem work_ge (base n g m : ℕ) : base ≤ SourceBandLayout.work base n g m := by
  unfold SourceBandLayout.work SourceBandLayout.hist SourceBandLayout.data
  omega

theorem ordered (base NL NR g m : ℕ) :
    leftBase base ≤ rightBase base NL g m ∧
    rightBase base NL g m ≤ zeroBase base NL NR g m ∧
    zeroBase base NL NR g m < next base NL NR g m := by
  exact ⟨work_ge _ _ _ _,work_ge _ _ _ _,by unfold next; omega⟩










































































end ThreeSum.SourceBandPairData

end

section


/-! # Read source controls from the actually constructed local-cover header -/

namespace ThreeSum.EncodedColorCoverData

open Light GlobalEncoding LocalCoverBounds SourceFiniteInputs

theorem header_end (free h J : ℕ) : free+20 ≤ LightCoverKeyData.keyEnd free h J :=
  (LightLocalCoverRetention.base_le_nextFree (LightLocalCoverInit.base free) h).trans
    (LightCoverKeyData.afterCover_le_keyEnd free h J)





























end ThreeSum.EncodedColorCoverData

end

section


/-! # One compact retained layout for a selected color -/

namespace ThreeSum.EncodedColorLayout































theorem free_le_normalizedEnd (free n g : ℕ) : free+8 ≤ normalizedEnd free n g := by
  unfold normalizedEnd LightBandRawA.space LightBandRawA.positionBase LightBandRawA.ownerBase
    LightBandRawA.capacity vals rec tables ce cv be bv ae av class2 class1 class0 colors
  omega











theorem free_le_prime (free n g : ℕ) : free+8 ≤ prime free n g := by
  have h := free_le_normalizedEnd free n g
  unfold prime
  omega

theorem prime_le_cover (free n g M y : ℕ) : prime free n g+6 ≤ cover free n g M y := by
  unfold cover EncodedColorPrimeData.nextFree EncodedColorPrimeData.prefixBase EncodedColorPrimeData.poolBase
  omega














end ThreeSum.EncodedColorLayout

end

section


/-! # Exact reusable memory boundary after the actual wanted-pair output -/

namespace ThreeSum.EncodedColorWantedData

open Light WantedResidueKeys




theorem header_le_nextFree (out M : ℕ) (left right : ℕ → ℤ) (NL NR : ℕ) (shift : ℤ) :
    out+4 ≤ nextFree out M left right NL NR shift := by
  unfold nextFree LightWantedSetup.pairBase LightSourceBucketSetup.next LightWantedSetup.bucketBase
    LightWantedSetup.rightCodes LightWantedSetup.leftCodes
  omega

















end ThreeSum.EncodedColorWantedData

end

section


/-! # Retained finite normalization and actual source controls in one contract -/

namespace ThreeSum.LightEncodedColorFiniteSources

open Light Scales TrimScales BandScales









theorem free_le_base (free n p M : ℕ) [NeZero M] (xs : List ℤ) : free ≤ base free n p M xs := by
  have h := EncodedColorWantedData.header_le_nextFree
    (LightGuardedWanted.wantedFree free (microHalf (inputBits n)) (blockCount (inputBits n)) xs.length)
    M (LightGuardedWanted.left p xs)
    (LightGuardedWanted.right (microHalf (inputBits n)) (blockCount (inputBits n)))
    (3*xs.length) (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)))
    (RawAKeyLists.selected M p xs (microHalf (inputBits n)) (blockCount (inputBits n)) : ℤ)
  have hk := EncodedColorCoverData.header_end free (microHalf (inputBits n)) (blockCount (inputBits n))
  change _ ≤ base free n p M xs at h
  unfold LightGuardedWanted.wantedFree at h
  omega

variable {lim : Limits} {d : ℕ}































































end ThreeSum.LightEncodedColorFiniteSources

end

section


/-! # Keep the complete finite source catalog below its exact returned end -/

namespace ThreeSum.SourceFiniteData

open Light

theorem source_ends (base NL NR g h J cut : ℕ) :
    base+3 ≤ LightSourceControlsHost.finish base NL NR g h J cut ∧
    SourceBandPairData.next (LightSourceControlsHost.sourceBase base) NL NR g
      (BlockSourceEncoding.modulus h J) ≤ LightSourceControlsHost.finish base NL NR g h J cut ∧
    LightSourceBandHost.bankHeader (LightSourceControlsHost.sourceBase base) NL NR g h J+5 ≤
      LightSourceControlsHost.finish base NL NR g h J cut := by
  have ho := SourceBandPairData.ordered (LightSourceControlsHost.sourceBase base)
    NL NR g (BlockSourceEncoding.modulus h J)
  unfold LightSourceControlsHost.finish LightSourceBandHost.finish SourceBandBankData.finish
    SourceBandBankLayout.baseAt SourceBandBankData.first LightSourceBandHost.bankHeader
    LightSourceBandHost.occurrenceBase LightSourceControlsHost.sourceBase
  unfold SourceBandPairData.leftBase LightSourceControlsHost.sourceBase at ho
  omega












end ThreeSum.SourceFiniteData

end

section


/-! # One retained selected-color payload, from original input to shared sources -/

namespace ThreeSum.EncodedColorPipelineData

open Light Scales BandScales ColorClassLists EncodedColorNormalizedData

attribute [local instance] _root_.ThreeSum.EncodedColorPipelineData.instNeZeroNatRadix







































































theorem ordered_sourceProof (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    EncodedColorLayout.prime free n (bandSize n)+6 ≤ coverBase free n ∧
    free+8 ≤ coverBase free n ∧ coverBase free n ≤ controls free n A B C hsA hsB hsC ∧
    wantedHeader free n (incidences n A B C hsA hsB hsC).length+4 ≤ controls free n A B C hsA hsB hsC ∧
    controls free n A B C hsA hsB hsC+3 ≤ finish free n A B C hsA hsB hsC ∧
    bankHeader free n A B C hsA hsB hsC+5 ≤ finish free n A B C hsA hsB hsC := by
  have hp := EncodedColorLayout.prime_le_cover free n (bandSize n) (radix n) (primeWindow n)
  have hf := EncodedColorLayout.free_le_prime free n (bandSize n)
  have hc := LightEncodedColorFiniteSources.free_le_base (coverBase free n) n
    (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (radix n) (incidences n A B C hsA hsB hsC)
  have hw := EncodedColorWantedData.header_le_nextFree
    (wantedHeader free n (incidences n A B C hsA hsB hsC).length) (radix n)
    (LightGuardedWanted.left (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (incidences n A B C hsA hsB hsC))
    (LightGuardedWanted.right (microHalf (inputBits n)) (blockCount (inputBits n)))
    (3*(incidences n A B C hsA hsB hsC).length)
    (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)))
    (RawAKeyLists.selected (radix n) (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
      (incidences n A B C hsA hsB hsC) (microHalf (inputBits n)) (blockCount (inputBits n)) : ℤ)
  have hs := SourceFiniteData.source_ends (controls free n A B C hsA hsB hsC) B.length C.length
    (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n)
  change _ ≤ coverBase free n at hp
  change _ ≤ controls free n A B C hsA hsB hsC at hc hw
  change controls free n A B C hsA hsB hsC+3 ≤ finish free n A B C hsA hsB hsC ∧ _ ∧
    bankHeader free n A B C hsA hsB hsC+5 ≤ finish free n A B C hsA hsB hsC at hs
  exact ⟨hp,by omega,hc,hw,hs.1,hs.2.2⟩

end ThreeSum.EncodedColorPipelineData

end


theorem solution : ∀ (free n : Nat) (A B C : List.{0} Int)
  (hsA : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) A)
  (hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B)
  (hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C),
  And
    (@LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (ThreeSum.EncodedColorLayout.prime free n (ThreeSum.BandScales.bandSize n))
        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
      (ThreeSum.EncodedColorPipelineData.coverBase free n))
    (And
      (@LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) free
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
        (ThreeSum.EncodedColorPipelineData.coverBase free n))
      (And
        (@LE.le.{0} Nat instLENat (ThreeSum.EncodedColorPipelineData.coverBase free n)
          (ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC))
        (And
          (@LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (ThreeSum.EncodedColorPipelineData.wantedHeader free n
                (@List.length.{0} Int (ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC)))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC))
          (And
            (@LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC))
            (@LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC)
                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC)))))) := by
  exact @ThreeSum.EncodedColorPipelineData.ordered_sourceProof

#print axioms solution
