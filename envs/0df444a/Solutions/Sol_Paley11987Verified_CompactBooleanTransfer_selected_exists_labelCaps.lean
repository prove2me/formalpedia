-- Prove2me | solution 1 for Paley11987Verified.CompactBooleanTransfer.selected_exists_labelCaps
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-23T04:45:23.221323+00:00
-- url     : https://prove2.me/submissions/b10b6545-1ee5-4160-b8e3-03e2b8ffe5e9

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
import Definitions.Def_Paley11987Support_036
import Definitions.Def_Paley11987Support_055
import Theorems.Thm_Paley11987Verified_CompactLabeling11987_exists_joint_exclusions

set_option autoImplicit false
set_option Elab.async false
section z8

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]





















theorem mismatch_mono (R : V → V → Prop) (ell : V × V → Fin 2)
    (A B : Finset V) (h : A ⊆ B) (color : V → Fin 2) (x : V) :
    mismatch R ell A color x ⊆ mismatch R ell B color x := by
  intro y hy
  exact Finset.mem_filter.mpr ⟨h (Finset.mem_filter.mp hy).1,
    (Finset.mem_filter.mp hy).2⟩

theorem ordinaryGood_mono (R : V → V → Prop) (ell : V × V → Fin 2)
    (A B : Finset V) (h : A ⊆ B) (q : ℕ) (color : V → Fin 2)
    (hg : OrdinaryGood R ell B q color) : OrdinaryGood R ell A q color := by
  intro x hx
  exact (Finset.card_le_card (mismatch_mono R ell A B h color x)).trans (hg x (h hx))

theorem markedGood_mono (R : V → V → Prop) (ell : V × V → Fin 2)
    (A A' M P P' : Finset V) (hA : A' ⊆ A) (hP : P' ⊆ P)
    (q B B' : ℕ) (hB : B ≤ B') (color : V → Fin 2)
    (hg : MarkedGood R ell A M P q B color) :
    MarkedGood R ell A' M P' q B' color := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact (Nat.add_le_add_right
      (Finset.card_le_card (mismatch_mono R ell A' A hA color x)) _).trans
      (hg.1 x (hA hx))
  · intro y hy
    have hm := Finset.card_le_card (mismatch_mono R ell A' A hA color y)
    have ho := hg.2.1 y hy
    by_cases hyP : y ∈ P'
    · simpa only [if_pos hyP, if_pos (hP hyP), Nat.add_zero] using
        (Nat.add_le_add_left hm (outOn R M y).card).trans ho
    · simp only [if_neg hyP]
      by_cases hyold : y ∈ P
      · simp only [if_pos hyold] at ho
        omega
      · simp only [if_neg hyold] at ho
        omega
  · calc
      ∑ y ∈ M, (mismatch R ell A' color y).card ≤
          ∑ y ∈ M, (mismatch R ell A color y).card :=
        Finset.sum_le_sum fun y _ => Finset.card_le_card
          (mismatch_mono R ell A' A hA color y)
      _ ≤ B' := hg.2.2.trans hB

























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

theorem ordinary_exclusion_defect_bound (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (q a : ℕ)
    (h : ∀ I : OrdinaryIndex (Fin k) a,
      ¬ (ordinaryFamily T.Adj q a).bad I (fun e => label e.1 e.2)) :
    DefectBound T label q a := by
  intro S color hg
  by_contra hn
  obtain ⟨A,hA,hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
  let I : OrdinaryIndex (Fin k) a :=
    ⟨A,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hcard⟩⟩
  apply h I
  exact ⟨color,ordinaryGood_mono T.Adj (fun e => label e.1 e.2) A S hA q color hg⟩

theorem marked_exclusion_card_bound (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (q a m B : ℕ)
    (h : ∀ I : MarkedIndex (Fin k) a m,
      ¬ (markedFamily T.Adj q a m B).bad I (fun e => label e.1 e.2)) :
    MarkedCardBound T label q m 0 B a := by
  intro A M P color hdis hPM hM hP hg
  have hpempty : P = ∅ := Finset.card_eq_zero.mp hP
  subst P
  by_contra hn
  obtain ⟨A',hA',hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
  have hcompl : A' ⊆ Mᶜ := by
    intro x hx
    exact Finset.mem_compl.mpr (fun hm => Finset.disjoint_left.mp hdis (hA' hx) hm)
  let MI : (Finset.univ : Finset (Fin k)).powersetCard m :=
    ⟨M,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hM⟩⟩
  let I : MarkedIndex (Fin k) a m :=
    ⟨MI,⟨A',Finset.mem_powersetCard.mpr ⟨hcompl,hcard⟩⟩⟩
  apply h I
  exact ⟨color,markedGood_mono T.Adj (fun e => label e.1 e.2)
    A A' M ∅ ∅ hA' (Finset.Subset.refl _) q B B le_rfl color hg⟩

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

theorem dominator_exclusion_double_bound (T : Tournament k)
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

theorem source_exclusion_source_bound (T : Tournament k)
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

end ZT
end
end z46

section z47

namespace CompactDRT
open Finset
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]






@[simp] theorem sum_mul_delta (f : V → ℤ) (x : V) :
    ∑ z : V, f z * delta x z = f x := by simp [delta, mul_ite]
@[simp] theorem sum_delta_mul (f : V → ℤ) (x : V) :
    ∑ z : V, delta x z * f z = f x := by simp [delta, ite_mul]



namespace Core
variable (C : Core V)

theorem skew_add (x y : V) : C.sign x y + C.sign y x = 0 := by rw [C.skew]; ring

















end Core
end CompactDRT
end z47

section z49

namespace CompactDRT
open Finset
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
namespace Core
variable (C : Core V)














theorem edge_identity (x y : V) : 2 * C.edge x y = 1 + C.sign x y - delta x y := by
  by_cases h : x = y
  · subst y; simp [edge, Adj, C.diag]
  · rcases C.off x y h with hs | hs <;> simp [edge, Adj, hs, delta, h]

theorem sum_edge (x : V) : ∑ z, C.edge x z = (C.outCount x : ℤ) := by
  simp [edge, outCount, Finset.sum_boole]

theorem sum_edge_mul (x y : V) :
    ∑ z, C.edge x z * C.edge y z = (C.commonOutCount x y : ℤ) := by
  have ht : ∀ z, C.edge x z * C.edge y z = if C.Adj x z ∧ C.Adj y z then 1 else 0 := by
    intro z
    by_cases hx : C.Adj x z <;> by_cases hy : C.Adj y z <;> simp [edge, hx, hy]
  simp_rw [ht]
  simp [commonOutCount, Finset.sum_boole]

theorem degree_identity (x : V) :
    2 * (C.outCount x : ℤ) = (Fintype.card V : ℤ) - 1 := by
  have hs := Finset.sum_congr (s₁ := (univ : Finset V)) rfl (fun z _ => C.edge_identity x z)
  simpa [← Finset.mul_sum, C.sum_edge, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, C.row] using hs

theorem common_identity (x y : V) (hxy : x ≠ y) :
    4 * (C.commonOutCount x y : ℤ) = (Fintype.card V : ℤ) - 3 := by
  have he : ∀ z, 4 * (C.edge x z * C.edge y z) =
      (1 + C.sign x z - delta x z) * (1 + C.sign y z - delta y z) := by
    intro z
    calc
      _ = (2 * C.edge x z) * (2 * C.edge y z) := by ring
      _ = _ := by rw [C.edge_identity, C.edge_identity]
  have hs := Finset.sum_congr (s₁ := (univ : Finset V)) rfl (fun z _ => he z)
  simp only [← Finset.mul_sum, C.sum_edge_mul] at hs
  simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_delta, sum_delta_mul,
    sum_mul_delta, C.row, C.gram] at hs
  have hk := C.skew_add x y
  simp [delta, hxy, hxy.symm] at hs
  linarith



theorem reverse_adj (x y : V) : C.reverse.Adj x y ↔ C.Adj y x := by
  change -C.sign x y = 1 ↔ C.sign y x = 1
  rw [C.skew]
  simp

theorem in_degree_identity (x : V) :
    2 * ((univ.filter fun z => C.Adj z x).card : ℤ) = (Fintype.card V : ℤ) - 1 := by
  have h := C.reverse.degree_identity x
  simpa [outCount, C.reverse_adj] using h

theorem common_in_identity (x y : V) (hxy : x ≠ y) :
    4 * ((univ.filter fun z => C.Adj z x ∧ C.Adj z y).card : ℤ) =
      (Fintype.card V : ℤ) - 3 := by
  have h := C.reverse.common_identity x y hxy
  simpa [commonOutCount, C.reverse_adj] using h

end Core

end
end CompactDRT
end z49

section z50

namespace CompactDRT
noncomputable section
open Finset









attribute [local irreducible] core11987




theorem outdegree11987 (x : Vertex11987) : (univ.filter (Adj11987 x)).card = 5993 := by
  have h := core11987.degree_identity x
  rw [vertex11987_card] at h
  change 2 * ((univ.filter (Adj11987 x)).card : ℤ) = _ at h
  omega

theorem indegree11987 (x : Vertex11987) :
    (univ.filter fun z => Adj11987 z x).card = 5993 := by
  have h := core11987.in_degree_identity x
  rw [vertex11987_card] at h
  change 2 * ((univ.filter fun z => Adj11987 z x).card : ℤ) = _ at h
  omega

theorem common_out11987 (x y : Vertex11987) (hxy : x ≠ y) :
    (univ.filter fun z => Adj11987 x z ∧ Adj11987 y z).card = 2996 := by
  have h := core11987.common_identity x y hxy
  rw [vertex11987_card] at h
  change 4 * ((univ.filter fun z => Adj11987 x z ∧ Adj11987 y z).card : ℤ) = _ at h
  omega

theorem common_in11987 (x y : Vertex11987) (hxy : x ≠ y) :
    (univ.filter fun z => Adj11987 z x ∧ Adj11987 z y).card = 2996 := by
  have h := core11987.common_in_identity x y hxy
  rw [vertex11987_card] at h
  change 4 * ((univ.filter fun z => Adj11987 z x ∧ Adj11987 z y).card : ℤ) = _ at h
  omega

end
end CompactDRT
end z50

section z51

set_option maxHeartbeats 300000
noncomputable section
open scoped Classical

namespace ZT
open CompactDRT OAI.Paper320
attribute [local irreducible] core11987



theorem card_filter_of_equiv {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (P : V → Prop) (Q : W → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ x, P x ↔ Q (e x)) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
  refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(h x).mp (Finset.mem_filter.mp hx).2⟩
  · intro x hx y hy he
    exact e.injective he
  · intro y hy
    refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,(h (e.symm y)).mpr ?_⟩
    simpa only [Equiv.apply_symm_apply] using (Finset.mem_filter.mp hy).2



theorem transported_outdegree {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (G : Core V) (e : Fin k ≃ V) (i : Fin k) :
    (Finset.univ.filter ((tournamentOfCore G e).Adj i)).card =
      (Finset.univ.filter (G.Adj (e i))).card := by
  exact card_filter_of_equiv e _ _ (fun _ => Iff.rfl)

theorem transported_indegree {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (G : Core V) (e : Fin k ≃ V) (i : Fin k) :
    (Finset.univ.filter fun z => (tournamentOfCore G e).Adj z i).card =
      (Finset.univ.filter fun z => G.Adj z (e i)).card := by
  exact card_filter_of_equiv e _ _ (fun _ => Iff.rfl)

theorem transported_common_out {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (G : Core V) (e : Fin k ≃ V) (i j : Fin k) :
    (Finset.univ.filter fun z => (tournamentOfCore G e).Adj i z ∧
      (tournamentOfCore G e).Adj j z).card =
    (Finset.univ.filter fun z => G.Adj (e i) z ∧ G.Adj (e j) z).card := by
  exact card_filter_of_equiv e _ _ (fun _ => Iff.rfl)

theorem transported_common_in {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (G : Core V) (e : Fin k ≃ V) (i j : Fin k) :
    (Finset.univ.filter fun z => (tournamentOfCore G e).Adj z i ∧
      (tournamentOfCore G e).Adj z j).card =
    (Finset.univ.filter fun z => G.Adj z (e i) ∧ G.Adj z (e j)).card := by
  exact card_filter_of_equiv e _ _ (fun _ => Iff.rfl)



theorem selected_outdegree (i : Fin 11987) :
    (Finset.univ.filter (selectedTournament.Adj i)).card = 5993 :=
  (transported_outdegree core11987 selectedEquiv i).trans (outdegree11987 (selectedEquiv i))

theorem selected_indegree (i : Fin 11987) :
    (Finset.univ.filter fun z => selectedTournament.Adj z i).card = 5993 :=
  (transported_indegree core11987 selectedEquiv i).trans (indegree11987 (selectedEquiv i))

theorem selected_common_out (i j : Fin 11987) (hij : i ≠ j) :
    (Finset.univ.filter fun z => selectedTournament.Adj i z ∧ selectedTournament.Adj j z).card = 2996 :=
  (transported_common_out core11987 selectedEquiv i j).trans
    (common_out11987 _ _ (selectedEquiv.injective.ne hij))

theorem selected_common_in (i j : Fin 11987) (hij : i ≠ j) :
    (Finset.univ.filter fun z => selectedTournament.Adj z i ∧ selectedTournament.Adj z j).card = 2996 :=
  (transported_common_in core11987 selectedEquiv i j).trans
    (common_in11987 _ _ (selectedEquiv.injective.ne hij))

end ZT
end
end z51

section z52

set_option maxHeartbeats 1000000
open scoped Classical
noncomputable section

namespace ZT
open OAI.Paper320 ZL CompactLabeling11987

theorem ordinaryA_eq_cutoff (q : Fin 9) :
    ordinaryA q = ZP.cutoff q.val := by
  fin_cases q <;> decide +kernel

theorem JointExclusions_labelCaps {k : ℕ} (T : Tournament k)
    (ell : Fin k × Fin k → Fin 2) (h : JointExclusions T.Adj ell) :
    LabelCaps T (fun i j => ell (i,j)) := by
  have ho (q : Fin 9) := ordinary_exclusion_defect_bound T
    (fun i j => ell (i,j)) q.val (ordinaryA q) (h.ordinary q)
  have hm (i : Fin 12) := marked_exclusion_card_bound T
    (fun u v => ell (u,v)) (marked i).q (marked i).a (marked i).m (marked i).B (h.marked i)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro q hq
    have hq' : q < 9 := by omega
    simpa only [ordinaryA_eq_cutoff] using ho ⟨q,hq'⟩
  · exact source_exclusion_source_bound T (fun i j => ell (i,j)) 21 h.source
  · exact dominator_exclusion_double_bound T (fun i j => ell (i,j)) 18 h.dominator
  · intro q hq1 hq4
    interval_cases q
    · exact hm 0
    · exact hm 1
    · exact hm 2
    · exact hm 3
  · exact hm 4
  · exact hm 5
  · exact hm 6
  · exact hm 7
  · exact hm 8
  · exact hm 9
  · exact hm 10
  · exact hm 11

theorem _root_.solution :
    ∃ label : Fin 11987 → Fin 11987 → Fin 2, LabelCaps selectedTournament label := by
  obtain ⟨ell,hell⟩ := _root_.Paley11987Verified.CompactLabeling11987.exists_joint_exclusions selectedTournament.Adj
    (by simp [N]) selectedTournament.loopless
    (fun x y hxy => selectedTournament.edge_compl hxy)
    (fun x => selected_outdegree x) (fun x => selected_indegree x)
    (fun x y hxy => selected_common_in x y hxy)
    (fun x y hxy => selected_common_out x y hxy)
  exact ⟨fun i j => ell (i,j),JointExclusions_labelCaps selectedTournament ell hell⟩

end ZT
end
end z52
