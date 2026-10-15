-- Prove2me | solution 1 for ThreeSum.SourceBandBankData.Stored.of_kept
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:39:19.414145+00:00
-- url     : https://prove2.me/submissions/cb6ed5b1-4f8f-4331-b8a8-1d5e004ada70

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle14
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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_SourceBandBankLayout_bank_of_kept


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
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
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceBandBankLayout
end ThreeSum.SourceBandBankLayout
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales

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


































theorem At.of_kept {μ ν : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g h J cut i bound : ℕ}
    {p shift : ℤ} (H : At μ fL fR base NL NR g h J cut p shift i)
    (K : Kept μ ν bound) (hb : baseAt base h J cut (i+1) ≤ bound) :
    At ν fL fR base NL NR g h J cut p shift i := by
  intro k hk
  exact bank_of_kept (H k hk) hk K ((work_le_end base h J cut i).trans hb)











end ThreeSum.SourceBandBankLayout

end

section


/-! # Retained common-band source catalog with one occurrence table -/

namespace ThreeSum.SourceBandBankData

open Light GlobalEncoding SourceBandBankLayout OutputDecodeRecords


























theorem Stored.of_kept_sourceProof {μ ν : ℕ → ℤ} {fL fR : ℕ → ℤ}
    {base NL NR g h J cut occ bound : ℕ} {p shift : ℤ}
    (H : Stored μ fL fR base NL NR g h J cut occ p shift)
    (K : Kept μ ν bound) (hocc : occ+LightBlockSourceCatalog.count h J*J ≤ base)
    (hb : finish base NL NR g h J cut ≤ bound) :
    Stored ν fL fR base NL NR g h J cut occ p shift := by
  have hbase : base+5 ≤ finish base NL NR g h J cut := Nat.le_add_right _ _
  refine ⟨?_,?_,?_⟩
  · intro i hi
    have hi' : i < 5 := by simpa only [header,List.length_cons,List.length_nil] using hi
    exact (K _ (by omega)).trans (H.heads i hi)
  · intro i hi
    exact (H.banks i hi).of_kept K
      ((baseAt_mono (first base) h J cut (by omega)).trans hb)
  · intro k hk j hj
    have hp := Nat.mul_le_mul_right J (show k+1 ≤ LightBlockSourceCatalog.count h J by omega)
    exact (K _ (by nlinarith)).trans (H.rows k hk j hj)













end ThreeSum.SourceBandBankData

end


theorem solution : ∀ {μ ν fL fR : Nat → Int} {base NL NR g h J cut occ bound : Nat} {p shift : Int},
  ThreeSum.SourceBandBankData.Stored μ fL fR base NL NR g h J cut occ p shift →
    Light.Kept μ ν bound →
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (ThreeSum.LightBlockSourceCatalog.count h J) J))
          base →
        @LE.le.{0} Nat instLENat (ThreeSum.SourceBandBankData.finish base NL NR g h J cut) bound →
          ThreeSum.SourceBandBankData.Stored ν fL fR base NL NR g h J cut occ p shift := by
  exact @ThreeSum.SourceBandBankData.Stored.of_kept_sourceProof

#print axioms solution
