-- Prove2me | solution 1 for ThreeSum.SharedReportingBankSources.source_bounds
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:58:26.209434+00:00
-- url     : https://prove2.me/submissions/259d86e6-f608-4e74-89b2-2a5c86bb7607

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle14
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
import Mathlib.Data.Int.Cast.Lemmas
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
import Mathlib.Data.Nat.Cast.Order.Ring
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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.BlockSourceSharing
end ThreeSum.BlockSourceSharing
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightZetaStages
end ThreeSum.LightZetaStages
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales

section


/-!
# Packed retained source banks indexed by occurrence vectors

Each bank retains its compact masks, coefficients, endpoints, flags, and
both complete source-stage families. Shared temporary transform workspace
follows all banks. Two header cells per occurrence contain the stage bases.
This layout lets the next actual source call preserve every earlier bank.
-/

namespace ThreeSum.LightBlockSourceBatchLayout

open SubsetAddress LightZetaStages

















theorem banks_le_slot (base count W cut i : ℕ) : banks base count ≤ slot base count W cut i :=
  Nat.le_add_right _ _

theorem slot_mono (base count W cut : ℕ) : Monotone (slot base count W cut) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _






theorem right_ge_left (base count W cut i : ℕ) :
    leftBase base count W cut i ≤ rightBase base count W cut i := Nat.le_add_right _ _

theorem right_end (base count W cut i : ℕ) :
    rightBase base count W cut i+family W cut = slot base count W cut (i+1) := by
  unfold rightBase leftBase flags rawRight rawLeft coeff1 coeff0 slot stride
  ring

theorem right_end_le_masks {base count W cut i : ℕ} (hi : i < count) :
    rightBase base count W cut i+family W cut ≤ maskBase base count W cut := by
  rw [right_end]
  exact slot_mono base count W cut (by omega)




theorem banks_le_work (base count W cut : ℕ) : banks base count ≤ work base count W cut := by
  have hm := banks_le_slot base count W cut count
  unfold work rowOut bitBase maskBase
  omega














theorem masks_le_work (base count W cut : ℕ) :
    maskBase base count W cut ≤ work base count W cut := by
  unfold work rowOut bitBase
  omega

































































end ThreeSum.LightBlockSourceBatchLayout

end

section


/-!
# Exact shared-bank dimensions and charge of the actual catalog

There are two stage families for each original band and occurrence vector.
The decoder and bank-loop overhead are included. Neither the number of
complete output subsets nor the three-valued query lift multiplies this
construction.
-/

namespace ThreeSum.BlockSourceCatalogCosts

open Scales TrimScales StageBounds CostLedger BlockSourceSharing SubsetAddress
open LightBlockSourceBatchLayout







theorem work_address (base count W cut : ℕ) :
    LightBlockSourceBatchLayout.work base count W cut =
      base+count*(stride W cut+2)+downsetCap W cut+W+2 := by
  unfold LightBlockSourceBatchLayout.work rowOut bitBase maskBase slot banks
  ring
























































































end ThreeSum.BlockSourceCatalogCosts

end

section


/-! # Complete source banks per common band with preserved earlier banks -/

namespace ThreeSum.SourceBandBankLayout

open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder







theorem work_add (base count W cut : ℕ) : work base count W cut=base+work 0 count W cut := by
  simp only [BlockSourceCatalogCosts.work_address]
  omega

theorem host_space_add (base free h J : ℕ) :
    LightBlockSourceRetainedHost.space (base+free) h J=
      base+LightBlockSourceRetainedHost.space free h J := by
  unfold LightBlockSourceRetainedHost.space LightSourcePreparation.space
    LightBlockSourceHashes.space LightSourceMaskFlags.space LightSourceRetainedStages.space
  omega

theorem complete_end (base h J cut i : ℕ) :
    LightBlockSourceRetainedHost.space
      (work (baseAt base h J cut i) (LightBlockSourceCatalog.count h J) (J*(512*h)) cut) h J=
      baseAt base h J cut (i+1) := by
  rw [work_add,host_space_add]
  unfold baseAt span
  ring

theorem baseAt_mono (base h J cut : ℕ) : Monotone (baseAt base h J cut) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _

theorem work_le_end (base h J cut i : ℕ) :
    work (baseAt base h J cut i) (LightBlockSourceCatalog.count h J) (J*(512*h)) cut ≤
      baseAt base h J cut (i+1) := by
  rw [← complete_end]
  exact (Nat.le_add_right _ _).trans (le_max_left _ _)



















































end ThreeSum.SourceBandBankLayout

end

section


/-! # Retained source pointers and complete source families precede the bank end -/

namespace ThreeSum.SharedReportingBankSources

open Light SubsetAddress BlockIndexedQuery GlobalEncoding

theorem source_bounds_sourceProof {base NB NC g h J cut i s : ℕ}
    (hi : i < SourceBandPairSlices.count NB NC g)
    (hs : s < LightBlockSourceCatalog.count h J) :
    leftCell base h J cut i s < SourceBandBankData.finish base NB NC g h J cut ∧
    rightCell base h J cut i s < SourceBandBankData.finish base NB NC g h J cut ∧
    leftBase base h J cut i s+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤
      SourceBandBankData.finish base NB NC g h J cut ∧
    rightBase base h J cut i s+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤
      SourceBandBankData.finish base NB NC g h J cut := by
  have hend := SourceBandBankLayout.baseAt_mono (SourceBandBankData.first base) h J cut
    (show i+1 ≤ SourceBandPairSlices.count NB NC g by omega)
  have hwork := (SourceBandBankLayout.work_le_end (SourceBandBankData.first base) h J cut i).trans hend
  change LightBlockSourceBatchLayout.work (bankBase base h J cut i)
    (LightBlockSourceCatalog.count h J) (J*(512*h)) cut ≤
      SourceBandBankData.finish base NB NC g h J cut at hwork
  have hhead := LightBlockSourceBatchLayout.banks_le_work (bankBase base h J cut i)
    (LightBlockSourceCatalog.count h J) (J*(512*h)) cut
  unfold LightBlockSourceBatchLayout.banks at hhead
  have hright := (LightBlockSourceBatchLayout.right_end_le_masks
    (base := bankBase base h J cut i) (W := J*(512*h)) (cut := cut) hs).trans
    (LightBlockSourceBatchLayout.masks_le_work _ _ _ _)
  have hleft := LightBlockSourceBatchLayout.right_ge_left (bankBase base h J cut i)
    (LightBlockSourceCatalog.count h J) (J*(512*h)) cut s
  change leftBase base h J cut i s ≤ rightBase base h J cut i s at hleft
  change rightBase base h J cut i s+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤
    LightBlockSourceBatchLayout.work (bankBase base h J cut i)
      (LightBlockSourceCatalog.count h J) (J*(512*h)) cut at hright
  unfold leftCell rightCell
  omega

















end ThreeSum.SharedReportingBankSources

end


theorem solution : ∀ {base NB NC g h J cut i s : Nat},
  @LT.lt.{0} Nat instLTNat i (ThreeSum.SourceBandPairSlices.count NB NC g) →
    @LT.lt.{0} Nat instLTNat s (ThreeSum.LightBlockSourceCatalog.count h J) →
      And
        (@LT.lt.{0} Nat instLTNat (ThreeSum.SharedReportingBankSources.leftCell base h J cut i s)
          (ThreeSum.SourceBandBankData.finish base NB NC g h J cut))
        (And
          (@LT.lt.{0} Nat instLTNat (ThreeSum.SharedReportingBankSources.rightCell base h J cut i s)
            (ThreeSum.SourceBandBankData.finish base NB NC g h J cut))
          (And
            (@LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (ThreeSum.SharedReportingBankSources.leftBase base h J cut i s)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (ThreeSum.SubsetAddress.downsetCap
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                    cut)))
              (ThreeSum.SourceBandBankData.finish base NB NC g h J cut))
            (@LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (ThreeSum.SharedReportingBankSources.rightBase base h J cut i s)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (ThreeSum.SubsetAddress.downsetCap
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                    cut)))
              (ThreeSum.SourceBandBankData.finish base NB NC g h J cut)))) := by
  exact @ThreeSum.SharedReportingBankSources.source_bounds_sourceProof

#print axioms solution
