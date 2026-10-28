-- Prove2me | solution 1 for ThreeBoundOrdinaryArchive.ZT.dominator_exclusion_double_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:38:00.017801+00:00
-- url     : https://prove2.me/submissions/32beb034-d315-4443-82b4-9e1cc72fb65c

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
/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/


open OAI.Paper320
namespace ThreeBoundOrdinaryArchive

/- selected_exists_labelCaps sections z8,z46 -/
set_option autoImplicit false
set_option Elab.async false
section z8

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]























end
end ZL
end
end z8

section z46

set_option maxHeartbeats 600000
open scoped Classical BigOperators
noncomputable section

namespace ZT
open OAI.Paper320 ZL SensitivityQ
variable {k : ℕ}





theorem coherent_restrict {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) (ell : V × V → Fin 2) (A A' M : Finset V)
    (hA : A' ⊆ A) (color : V → Fin 2) (hg : Coherent R ell A M color) :
    Coherent R ell A' M color := by
  intro e he
  apply hg e
  rcases Finset.mem_union.mp he with hi | hc
  · obtain ⟨hp,hr⟩ := Finset.mem_filter.mp hi
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hA hx,hA hy⟩,hr⟩)
  · obtain ⟨hp,hr⟩ := Finset.mem_filter.mp hc
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hx,hA hy⟩,hr⟩)





end ZT
end
end z46


end ThreeBoundOrdinaryArchive

end

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
    (h : ∀ I : DominatorIndex T.Adj a,
      ¬ (dominatorFamily T.Adj a).bad I (fun e => label e.1 e.2)) :
    DoubleCardBound T label a := by
  intro A M color hg
  by_contra hn
  obtain ⟨A',hA',hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
  have hdom : A' ⊆ dominatedBy T.Adj M := by
    intro y hy
    simp only [dominatedBy,Finset.mem_filter,Finset.mem_univ,true_and]
    exact fun x hx => hg.2.2.1 x hx y (hA' hy)
  let MI : (Finset.univ : Finset (Fin k)).powersetCard 2 :=
    ⟨M,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hg.2.1⟩⟩
  let I : DominatorIndex T.Adj a :=
    ⟨MI,⟨A',Finset.mem_powersetCard.mpr ⟨hdom,hcard⟩⟩⟩
  apply h I
  exact ⟨color,coherent_restrict T.Adj (fun e => label e.1 e.2) A A' M hA' color hg.2.2.2⟩
end
