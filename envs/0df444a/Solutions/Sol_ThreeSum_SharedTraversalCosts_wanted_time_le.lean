-- Prove2me | solution 1 for ThreeSum.SharedTraversalCosts.wanted_time_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:18:28.998784+00:00
-- url     : https://prove2.me/submissions/71464fb2-a71f-4fda-8d42-7f52e76b92aa

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
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
import Definitions.Def_ThreeSum1962Source_Bundle17
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
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_RawReporting_partitionWord_length
import Theorems.Thm_ThreeSum_RawReporting_word_children
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_localRow
import Theorems.Thm_ThreeSum_ReportingHostMasks_localChildren_mem
import Theorems.Thm_ThreeSum_ReportingHostTerminalFrontier_frontier_time_le
import Theorems.Thm_ThreeSum_Reporting_frontier_length_le_mass


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
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
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
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Query-coordinate lists and weighted subset semantics

The coordinate list has one entry per set bit of the query. Its powers
form a compact weight table for the output-sensitive enumeration routine.
-/

namespace ThreeSum.QueryCoordinates

open Finset ThreeSum.SubsetAddress
open scoped BigOperators











































































theorem setLayer_nodup (xs : List ℕ) (hn : xs.Nodup) (k : ℕ) :
    (setLayer xs k).Nodup := by
  apply (List.nodup_sublistsLen k hn).map_on
  intro a ha b hb he
  have ha' := (List.mem_sublistsLen.mp ha).1
  have hb' := (List.mem_sublistsLen.mp hb).1
  apply (hn.perm_iff_eq_of_sublist ha' hb').mp
  exact List.perm_of_nodup_nodup_toFinset_eq (hn.sublist ha') (hn.sublist hb') he





















































































































theorem missingSets_nodup {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) :
    (missingSets Q k).Nodup := by
  unfold missingSets
  apply (setLayer_nodup _ (List.nodup_reverse.mpr (positions_nodup Q W)) k).map_on
  intro a ha b hb he
  have has := (mem_setLayer _ (List.nodup_reverse.mpr (positions_nodup Q W)) _ _).mp ha
  have hbs := (mem_setLayer _ (List.nodup_reverse.mpr (positions_nodup Q W)) _ _).mp hb
  rw [List.toFinset_reverse,positions_toFinset] at has hbs
  have h := congrArg natPositions he
  rw [decode_maskOf (has.1.trans (natPositions_subset Q)),
      decode_maskOf (hbs.1.trans (natPositions_subset Q))] at h
  exact h




























end ThreeSum.QueryCoordinates

end

section


/-!
# Exact next-block masks for the reporting host

The machine enumerates subsets directly in the global row-major ground set.
This file identifies those subsets with the balanced next-row children of
the original reporting tree, and proves the arithmetic mask transitions.
-/

namespace ThreeSum.ReportingHostMasks

open Finset BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open ThreeSum.SubsetAddress StoredReporting BlockForced



























































theorem globalChildren_nodup {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (globalChildren i Q h).Nodup := QueryCoordinates.missingSets_nodup _ _



















theorem localChildren_nodup {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (localChildren i Q h).Nodup := by
  apply (globalChildren_nodup i Q h).map_on
  intro S hS T hT he
  have hs := (QueryCoordinates.missingSets_mem _ _ _).mp hS
  have ht := (QueryCoordinates.missingSets_mem _ _ _).mp hT
  rw [← blockSet_localRow i Q hs.1,← blockSet_localRow i Q ht.1,he]



























































































































































end ThreeSum.ReportingHostMasks

end

section


/-!
# Coverage and raw-mass charging in the machine's actual child order

The output-sensitive enumerator uses its recursive coordinate order. The
reporting tree is instantiated with that exact order here; its positive
frontiers retain the original incidences and their multiplicities.
-/

namespace ThreeSum.ReportingHostFrontier

open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators




theorem mem_children_iff {h J : ℕ} (q : GlobalOutput h J) (k : ℕ)
    (S : Finset (Fin (512*h))) : S ∈ children q k ↔ S ∈ RawReporting.children q k := by
  unfold children RawReporting.children
  split
  · exact localChildren_mem _ _ _ _
  · rfl

theorem children_nodup {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) :
    (children q k).Nodup := by
  unfold children
  split
  · exact localChildren_nodup _ _ _
  · exact List.nodup_nil









section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]




theorem word_children {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (r : RawItem h J α β γ) (hr : r ∈ domain I w) (j : ℕ) (hj : j < J) :
    (word r)[j]'(by rw [word,partitionWord_length]; exact hj) ∈ children w.2.2 j :=
  (mem_children_iff _ _ _).mpr (RawReporting.word_children I w r hr j hj)





















theorem frontier_length_le_domain {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (hk : k ≤ J) : (frontier I w k).length ≤ (domain I w).card := by
  have h := Reporting.frontier_length_le_mass (domain I w) word (fun _ => 1)
    (children w.2.2) (prefixQuery I w) J k
    (fun r _ => partitionWord_length r.2.1) (word_children I w)
    (fun _ _ _ => rfl) (children_nodup w.2.2) hk
  simpa only [frontier,Finset.sum_const,smul_eq_mul,mul_one] using h
























































end Indices

end ThreeSum.ReportingHostFrontier

end

section


/-! # Exact physical frontier slots and a capacity computed from root raw mass -/

namespace ThreeSum.ReportingHostFrontierLayout

open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndex BlockIndexedQuery BlockForced StoredReporting GlobalEncoding LocalCoverBounds
open RawIncidences RawReporting LightBlockQuery ReportingHostMasks

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

































variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]




theorem rootMass_eq {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) :
    rootMass I w=(domain I w).card := by
  simp [rootMass,prefixQuery,Reporting.mass,Subset.fiberMass]












































































end ThreeSum.ReportingHostFrontierLayout

end

section


/-!
# Cost of the executed positive-frontier traversal

The expensive expansion remains multiplied by the number of actual positive
parents. Empty frontiers pay only the fixed level overhead. The terminal
scan is charged to the exact original bucket products, and the dense guard
removes this proportional charge from the branch which has already exceeded
the threshold.
-/

namespace ThreeSum.SharedTraversalCosts

open Finset GlobalEncoding RawIncidences RawReporting ReportingHostLevelData
open ReportingHostFrontierLayout
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false










variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem levels_time_eq {h J : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (D : ℕ → Catalog) (K : ℕ) :
    LightReportingLevels.time I w D K = 30+1300*K+
      ∑ k ∈ range K, (ReportingHostFrontier.frontier I w k).length*
        (LightReportingPositiveExpand.time h J k (D (k+1)).t+200) := by
  induction K with
  | zero => simp [LightReportingLevels.time]
  | succ K ih =>
      rw [LightReportingLevels.time,ih,sum_range_succ]
      unfold LightReportingStoredStep.time LightReportingFrontierStep.time
      omega

theorem levels_time_le {h J K : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (D : ℕ → Catalog) (hK : K ≤ J) :
    LightReportingLevels.time I w D K ≤
      (domain I w).card*levelUnit h J D K+1300*K+30 := by
  rw [levels_time_eq]
  have hs : (∑ k ∈ range K, (ReportingHostFrontier.frontier I w k).length*
      (LightReportingPositiveExpand.time h J k (D (k+1)).t+200)) ≤
      (domain I w).card*levelUnit h J D K := by
    unfold levelUnit
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    exact Nat.mul_le_mul_right _ (ReportingHostFrontier.frontier_length_le_domain I w
      ((mem_range.mp hk).le.trans hK))
  omega

theorem terminal_time_le {h J K NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (left right : ℕ → ℤ)
    (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i))
    (hvR : ∀ i : Fin NR, right i.val=c (eR i))
    (w : Wanted h J α) (hK : K ≤ J)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1%(p : ℤ)+lift w.2.1*(p : ℤ)+shift)-globalKey w.2.2) :
    let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
    LightReportingTerminalStored.time p shift left right NL NR I w K ≤
      (domain I w).card*(ReportingHostTerminalFrontier.charge h J K+240)+630 := by
  dsimp only
  let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  have ht := ReportingHostTerminalFrontier.frontier_time_le p shift A B C a b c
    left right eL eR hvL hvR w hK hkey
  have hm := Nat.mul_le_mul_left (ReportingHostTerminalFrontier.charge h J K)
    (ReportingHostFrontier.frontier_length_le_domain I w hK)
  change LightReportingTerminalStored.time p shift left right NL NR I w K ≤ _
  unfold LightReportingTerminalStored.time
  change ReportingHostTerminalFrontier.time p shift left right NL NR w.2.2 K
    (ReportingHostFrontier.frontier I w K) (ReportingHostFrontier.frontier I w K).length ≤
      240*(domain I w).card+ReportingHostTerminalFrontier.charge h J K*
        (ReportingHostFrontier.frontier I w K).length+30 at ht
  nlinarith

theorem search_time_le {h J K NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (left right : ℕ → ℤ)
    (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i))
    (hvR : ∀ i : Fin NR, right i.val=c (eR i))
    (w : Wanted h J α) (D : ℕ → Catalog) (hK : K ≤ J)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1%(p : ℤ)+lift w.2.1*(p : ℤ)+shift)-globalKey w.2.2) :
    let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
    LightReportingWantedSearch.time p shift left right NL NR I w D K ≤
      (domain I w).card*searchUnit h J D K+1300*K+1160 := by
  dsimp only
  let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  have hl := levels_time_le I w D hK
  have ht := terminal_time_le p shift A B C a b c left right eL eR hvL hvR w hK hkey
  change LightReportingTerminalStored.time p shift left right NL NR I w K ≤ _ at ht
  unfold LightReportingWantedSearch.time searchUnit
  nlinarith

theorem wanted_time_le_sourceProof {h J K NL NR old threshold : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (left right : ℕ → ℤ)
    (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i))
    (hvR : ∀ i : Fin NR, right i.val=c (eR i))
    (w : Wanted h J α) (D : ℕ → Catalog) (hK : K ≤ J)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1%(p : ℤ)+lift w.2.1*(p : ℤ)+shift)-globalKey w.2.2) :
    let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
    LightReportingWanted.time p shift left right NL NR old threshold I w D K ≤
      initialUnit h J D K+
        (if threshold < old+rootMass I w then 0 else rootMass I w*searchUnit h J D K) := by
  dsimp only
  let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  have hs := search_time_le p shift A B C a b c left right eL eR hvL hvR w D hK hkey
  change LightReportingWantedSearch.time p shift left right NL NR I w D K ≤
    (domain I w).card*searchUnit h J D K+1300*K+1160 at hs
  change LightReportingWanted.time p shift left right NL NR old threshold I w D K ≤
    initialUnit h J D K+
      (if threshold < old+rootMass I w then 0 else rootMass I w*searchUnit h J D K)
  unfold LightReportingWanted.time initialUnit
  by_cases hg : threshold < old+rootMass I w
  · simp only [if_pos hg]
    omega
  · simp only [if_neg hg]
    rw [rootMass_eq]
    omega

end ThreeSum.SharedTraversalCosts

end

universe u_1 u_2 u_3

theorem solution : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype.{u_1} α] [Fintype.{u_2} β] [Fintype.{u_3} γ]
  [inst : DecidableEq.{u_1 + 1} α] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ] {h J K NL NR old threshold : Nat}
  (p : Nat) (shift : Int) (A : Finset.{u_1} α) (B : Finset.{u_2} β) (C : Finset.{u_3} γ) (a : α → Int) (b : β → Int)
  (c : γ → Int) (left right : Nat → Int) (eL : Equiv.{1, u_2 + 1} (Fin NL) ↥B) (eR : Equiv.{1, u_3 + 1} (Fin NR) ↥C),
  (∀ (i : Fin NL),
      @Eq.{1} Int (left (@Fin.val NL i))
        (b
          (@Subtype.val.{u_2 + 1} β
            (fun (x : β) =>
              @Membership.mem.{u_2, u_2} β (Finset.{u_2} β)
                (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} β) β (@Finset.instSetLike.{u_2} β)) B x)
            (@DFunLike.coe.{u_2 + 1, 1, u_2 + 1} (Equiv.{1, u_2 + 1} (Fin NL) ↥B) (Fin NL) (fun (x : Fin NL) => ↥B)
              (@EquivLike.toFunLike.{u_2 + 1, 1, u_2 + 1} (Equiv.{1, u_2 + 1} (Fin NL) ↥B) (Fin NL) (↥B)
                (@Equiv.instEquivLike.{1, u_2 + 1} (Fin NL) ↥B))
              eL i)))) →
    (∀ (i : Fin NR),
        @Eq.{1} Int (right (@Fin.val NR i))
          (c
            (@Subtype.val.{u_3 + 1} γ
              (fun (x : γ) =>
                @Membership.mem.{u_3, u_3} γ (Finset.{u_3} γ)
                  (@SetLike.instMembership.{u_3, u_3} (Finset.{u_3} γ) γ (@Finset.instSetLike.{u_3} γ)) C x)
              (@DFunLike.coe.{u_3 + 1, 1, u_3 + 1} (Equiv.{1, u_3 + 1} (Fin NR) ↥C) (Fin NR) (fun (x : Fin NR) => ↥C)
                (@EquivLike.toFunLike.{u_3 + 1, 1, u_3 + 1} (Equiv.{1, u_3 + 1} (Fin NR) ↥C) (Fin NR) (↥C)
                  (@Equiv.instEquivLike.{1, u_3 + 1} (Fin NR) ↥C))
                eR i)))) →
      ∀ (w : ThreeSum.RawReporting.Wanted.{u_1} h J α) (D : Nat → ThreeSum.ReportingHostLevelData.Catalog),
        @LE.le.{0} Nat instLENat K J →
          And
              (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
                (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) A
                (@Prod.fst.{u_1, 0} α
                  (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (ThreeSum.GlobalEncoding.GlobalOutput h J))
                  w))
              (@Dvd.dvd.{0} Int Int.instDvd (ThreeSum.GlobalEncoding.globalModulus h J)
                (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                  (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                    (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                      (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod)
                        (a
                          (@Prod.fst.{u_1, 0} α
                            (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (ThreeSum.GlobalEncoding.GlobalOutput h J))
                            w))
                        (@Nat.cast.{0} Int instNatCastInt p))
                      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                        (ThreeSum.RawIncidences.lift
                          (@Prod.fst.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (ThreeSum.GlobalEncoding.GlobalOutput h J)
                            (@Prod.snd.{u_1, 0} α
                              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (ThreeSum.GlobalEncoding.GlobalOutput h J))
                              w)))
                        (@Nat.cast.{0} Int instNatCastInt p)))
                    shift)
                  (@ThreeSum.GlobalEncoding.globalKey h J
                    (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput h J)
                      (@Prod.snd.{u_1, 0} α
                        (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (ThreeSum.GlobalEncoding.GlobalOutput h J))
                        w))))) →
            have I :=
              @ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ h J (@Nat.cast.{0} Int instNatCastInt p) shift
                (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
                  (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
                  (Finset.{max (max u_2 u_3) u_1} (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
                  (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
                  (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β) (Finset.{u_3} γ)
                    (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ)) (@Finset.instSProd.{u_2, u_3} β γ) B C))
                a b c;
            @LE.le.{0} Nat instLENat
              (@ThreeSum.LightReportingWanted.time.{u_1, u_2, u_3} α β γ inst h J p shift left right NL NR old threshold
                I w D K)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (ThreeSum.SharedTraversalCosts.initialUnit h J D K)
                (@ite.{1} Nat
                  (@LT.lt.{0} Nat instLTNat threshold
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
                      (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3} α β γ inst h J I w)))
                  (threshold.decLt
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
                      (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3} α β γ inst h J I w)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3} α β γ inst h J I w)
                    (ThreeSum.SharedTraversalCosts.searchUnit h J D K)))) := by
  exact @ThreeSum.SharedTraversalCosts.wanted_time_le_sourceProof

#print axioms solution
