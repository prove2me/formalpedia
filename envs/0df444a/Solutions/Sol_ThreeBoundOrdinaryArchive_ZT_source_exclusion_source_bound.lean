-- Prove2me | solution 1 for ThreeBoundOrdinaryArchive.ZT.source_exclusion_source_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:38:41.463493+00:00
-- url     : https://prove2.me/submissions/a54bdae9-03fb-4581-9c13-ae22f615135c

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Sensitivity213303_ArchivedOrdinaryDefinitions

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundOrdinaryArchive.OAI.Paper320
end ThreeBoundOrdinaryArchive.OAI.Paper320
namespace ThreeBoundOrdinaryArchive.SensitivityQ
end ThreeBoundOrdinaryArchive.SensitivityQ
namespace ThreeBoundOrdinaryArchive.ZL
end ThreeBoundOrdinaryArchive.ZL
section
open OAI.Paper320
namespace ThreeBoundOrdinaryArchive
end ThreeBoundOrdinaryArchive
open ThreeBoundOrdinaryArchive
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
open scoped Classical BigOperators
namespace ThreeBoundOrdinaryArchive.ZT
end ThreeBoundOrdinaryArchive.ZT
open ThreeBoundOrdinaryArchive.ZT
open OAI.Paper320 ZL SensitivityQ
variable {k : ℕ}

theorem solution (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (a : ℕ)
    (h : ∀ I : SourceIndex T.Adj a,
      ¬ (sourceFamily T.Adj a).bad I (fun e => label e.1 e.2)) :
    SensitivitySourceZero.SourceBound T label (a+1) := by
  intro S color hsource hzero
  obtain ⟨s,hs,hdom⟩ := hsource
  by_contra hn
  have hsizing : a ≤ (S.erase s).card := by
    rw [Finset.card_erase_of_mem hs]
    omega
  obtain ⟨A,hA,hcard⟩ := Finset.exists_subset_card_eq hsizing
  have hAS : A ⊆ S := hA.trans (Finset.erase_subset s S)
  have hAout : A ⊆ outOn T.Adj Finset.univ s := by
    intro y hy
    have hey := Finset.mem_erase.mp (hA hy)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hdom y hey.2 hey.1⟩
  have hcoh : ∀ i ∈ S, ∀ j ∈ S, T.Adj i j → label i j = color j := by
    intro i hi j hj hij
    by_contra hne
    have hm : j ∈ S.filter (fun z => T.Adj i z ∧ label i z ≠ color z) :=
      Finset.mem_filter.mpr ⟨hj,hij,hne⟩
    have hp := Finset.card_pos.mpr ⟨j,hm⟩
    have hz := hzero i hi
    omega
  let I : SourceIndex T.Adj a := ⟨s,⟨A,Finset.mem_powersetCard.mpr ⟨hAout,hcard⟩⟩⟩
  apply h I
  refine ⟨color,?_⟩
  intro e he
  rcases Finset.mem_union.mp he with hi | hc
  · obtain ⟨hp,hr⟩ := Finset.mem_filter.mp hi
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    exact hcoh e.1 (hAS hx) e.2 (hAS hy) hr
  · obtain ⟨hp,hr⟩ := Finset.mem_filter.mp hc
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    have heq : e.1 = s := Finset.mem_singleton.mp hx
    exact hcoh e.1 (heq.symm ▸ hs) e.2 (hAS hy) hr
end
