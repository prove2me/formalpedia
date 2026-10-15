-- Prove2me | solution 1 for ThreeSum.ReportingHostFrontierLayout.At.of_kept
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:53:05.742857+00:00
-- url     : https://prove2.me/submissions/8e4ef8ce-39fb-46ae-944d-557630078cc8

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
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
import Mathlib.Algebra.Order.Field.Basic
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
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
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
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
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
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-! # Exact physical frontier slots and a capacity computed from root raw mass -/

namespace ThreeSum.ReportingHostFrontierLayout

open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndex BlockIndexedQuery BlockForced StoredReporting GlobalEncoding LocalCoverBounds
open RawIncidences RawReporting LightBlockQuery ReportingHostMasks

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false






theorem slot_succ (base cap k : ℕ) : slot base cap (k+1)=slot base cap k+4+2*cap := by
  unfold slot; ring




theorem right_end (base cap k : ℕ) : right base cap k+cap=slot base cap (k+1) := by
  rw [slot_succ]
  unfold right left
  omega

















variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]










































@[simp] theorem leftMasks_length {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (k : ℕ) :
    (leftMasks I w k).length=(ReportingHostFrontier.frontier I w k).length := by simp [leftMasks]
@[simp] theorem rightMasks_length {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (k : ℕ) :
    (rightMasks I w k).length=(ReportingHostFrontier.frontier I w k).length := by simp [rightMasks]




















theorem At.of_kept_sourceProof {h J k base cap stop : ℕ} {μ ν : ℕ→ℤ}
    {I : Finset (RawItem h J α β γ)} {w : Wanted h J α}
    (H : At μ I w base cap k) (hcap : (ReportingHostFrontier.frontier I w k).length≤cap)
    (hend : slot base cap (k+1)≤stop) (hkeep : Kept μ ν stop) : At ν I w base cap k := by
  have he := right_end base cap k
  have hL : ReportingHostFrontierLayout.left base cap k+cap≤stop := by unfold ReportingHostFrontierLayout.right at he; omega
  have hR : ReportingHostFrontierLayout.right base cap k+cap≤stop := by omega
  constructor
  · exact (hkeep _ (by unfold ReportingHostFrontierLayout.left at hL; omega)).trans H.count
  · exact (hkeep _ (by unfold ReportingHostFrontierLayout.left at hL; omega)).trans H.query
  · intro i hi
    have hi' : i<(ReportingHostFrontier.frontier I w k).length := by simpa only [List.length_map,leftMasks_length] using hi
    exact (hkeep _ (by omega)).trans (H.left i hi)
  · intro i hi
    have hi' : i<(ReportingHostFrontier.frontier I w k).length := by simpa only [List.length_map,rightMasks_length] using hi
    exact (hkeep _ (by omega)).trans (H.right i hi)

end ThreeSum.ReportingHostFrontierLayout

end

universe u_1 u_2 u_3

theorem solution : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype.{u_1} α] [Fintype.{u_2} β] [Fintype.{u_3} γ]
  [inst : DecidableEq.{u_1 + 1} α] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ] {h J k base cap stop : Nat}
  {μ ν : Nat → Int} {I : Finset.{max (max u_3 u_2) u_1} (ThreeSum.RawIncidences.RawItem.{u_1, u_2, u_3} h J α β γ)}
  {w : ThreeSum.RawReporting.Wanted.{u_1} h J α},
  @ThreeSum.ReportingHostFrontierLayout.At.{u_1, u_2, u_3} α β γ inst h J μ I w base cap k →
    @LE.le.{0} Nat instLENat
        (@List.length.{0}
          (List.{0}
            (Finset.{0}
              (Fin
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
          (@ThreeSum.ReportingHostFrontier.frontier.{u_1, u_2, u_3} α β γ inst h J I w k))
        cap →
      @LE.le.{0} Nat instLENat
          (ThreeSum.ReportingHostFrontierLayout.slot base cap
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          stop →
        Light.Kept μ ν stop → @ThreeSum.ReportingHostFrontierLayout.At.{u_1, u_2, u_3} α β γ inst h J ν I w base cap k := by
  exact @ThreeSum.ReportingHostFrontierLayout.At.of_kept_sourceProof

#print axioms solution
