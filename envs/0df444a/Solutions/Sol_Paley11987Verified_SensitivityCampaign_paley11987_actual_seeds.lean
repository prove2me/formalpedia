-- Prove2me | solution 1 for Paley11987Verified.SensitivityCampaign.paley11987_actual_seeds
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-23T05:53:42.764264+00:00
-- url     : https://prove2.me/submissions/ecd18593-037f-40da-b2ba-7c63b0efaf6d

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
import Definitions.Def_Paley11987Support_054
import Definitions.Def_Paley11987Support_055
import Theorems.Thm_Paley11987Verified_CompactBooleanTransfer_selected_exists_labelCaps
import Theorems.Thm_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate
import Theorems.Thm_Paley11987Verified_CompactFiniteProfile11987_transition1
import Theorems.Thm_Paley11987Verified_CompactFiniteProfile11987_transition2
import Theorems.Thm_Paley11987Verified_CompactFiniteProfile11987_transition3

set_option autoImplicit false
set_option Elab.async false
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



theorem degree_identity (x : V) :
    2 * (C.outCount x : ℤ) = (Fintype.card V : ℤ) - 1 := by
  have hs := Finset.sum_congr (s₁ := (univ : Finset V)) rfl (fun z _ => C.edge_identity x z)
  simpa [← Finset.mul_sum, C.sum_edge, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, C.row] using hs











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









theorem selected_outdegree (i : Fin 11987) :
    (Finset.univ.filter (selectedTournament.Adj i)).card = 5993 :=
  (transported_outdegree core11987 selectedEquiv i).trans (outdegree11987 (selectedEquiv i))







end ZT
end
end z51

section z87
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000


theorem cases_1_0_eq : cases 1 0 = cases_1_0 := by decide +kernel

theorem cases_1_1_eq : cases 1 5 = cases_1_1 := by decide +kernel

theorem cases_2_0_eq : cases 2 0 = cases_2_0 := by decide +kernel

theorem cases_2_1_eq : cases 2 7 = cases_2_1 := by decide +kernel

theorem cases_3_0_eq : cases 3 0 = cases_3_0 := by decide +kernel

theorem cases_3_1_eq : cases 3 9 = cases_3_1 := by decide +kernel

theorem cases_4_0_eq : cases 4 0 = cases_4_0 := by decide +kernel

theorem cases_4_1_eq : cases 4 11 = cases_4_1 := by decide +kernel

theorem cases_5_0_eq : cases 5 0 = cases_5_0 := by decide +kernel

theorem cases_5_1_eq : cases 5 13 = cases_5_1 := by decide +kernel











theorem cases_8_1_eq : cases 8 19 = cases_8_1 := by decide +kernel
end ZP
end z87

section z88
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX0 : rawA witness recipe0 0 0 ≤ A stage1 0 0 := by
  change maximum ((cases 8 19).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 3073860634545 241680163775794 241680163775794)) ≤ 16144544029178739
  rw [cases_8_1_eq]
  decide +kernel
theorem zX1 : rawA witness recipe0 0 1 ≤ A stage1 0 1 := by
  change maximum ((cases 5 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 3073860634545 241680163775794 241680163775794)) ≤ 172136195534520
  rw [cases_5_0_eq]
  decide +kernel
theorem zX2 : rawA witness recipe0 0 2 ≤ A stage1 0 2 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 3073860634545 241680163775794 241680163775794)) ≤ 150619171092705
  rw [cases_4_0_eq]
  decide +kernel
theorem zX3 : rawA witness recipe0 0 3 ≤ A stage1 0 3 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 3073859773827 241680163775794 224827700310579)) ≤ 132175970274561
  rw [cases_3_0_eq]
  decide +kernel
theorem zX4 : rawA witness recipe0 0 4 ≤ A stage1 0 4 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 213500573516 241680163775794 6707373398223)) ≤ 9180524661188
  rw [cases_3_0_eq]
  decide +kernel
theorem zX5 : rawA witness recipe0 0 5 ≤ A stage1 0 5 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 213500573516 241680163775794 6707373398223)) ≤ 7899521220092
  rw [cases_2_0_eq]
  decide +kernel
theorem zX6 : rawA witness recipe0 0 6 ≤ A stage1 0 6 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 213500573516 241680163775794 6707373398223)) ≤ 6405017205480
  rw [cases_1_0_eq]
  decide +kernel
theorem zX7 : rawA witness recipe0 0 7 ≤ A stage1 0 7 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 211423598883 241680163775794 6700230963121)) ≤ 6342707966490
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z88

section z89
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX8 : rawA witness recipe0 1 1 ≤ A stage1 1 1 := by
  change maximum ((cases 5 13).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 3073860634545 241680163775794 241680163775794)) ≤ 8851105067021289
  rw [cases_5_1_eq]
  decide +kernel
theorem zX9 : rawA witness recipe0 1 2 ≤ A stage1 1 2 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 3073860634545 241680163775794 241680163775794)) ≤ 150619171092705
  rw [cases_4_0_eq]
  decide +kernel
theorem zX10 : rawA witness recipe0 1 3 ≤ A stage1 1 3 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 3073859773827 241680163775794 224827700310579)) ≤ 132175970274561
  rw [cases_3_0_eq]
  decide +kernel
theorem zX11 : rawA witness recipe0 1 4 ≤ A stage1 1 4 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 213500573516 241680163775794 6707373398223)) ≤ 9180524661188
  rw [cases_3_0_eq]
  decide +kernel
theorem zX12 : rawA witness recipe0 1 5 ≤ A stage1 1 5 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 213500573516 241680163775794 6707373398223)) ≤ 7899521220092
  rw [cases_2_0_eq]
  decide +kernel
end ZP
end z89

section z90
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX13 : rawA witness recipe0 1 6 ≤ A stage1 1 6 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 213500573516 241680163775794 6707373398223)) ≤ 6405017205480
  rw [cases_1_0_eq]
  decide +kernel
theorem zX14 : rawA witness recipe0 1 7 ≤ A stage1 1 7 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 211423598883 241680163775794 6700230963121)) ≤ 6342707966490
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z90

section z91
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX15 : rawA witness recipe0 2 2 ≤ A stage1 2 2 := by
  change maximum ((cases 4 11).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 3073860634545 241680163775794 241680163775794)) ≤ 6899220593007667
  rw [cases_4_1_eq]
  decide +kernel
theorem zX16 : rawA witness recipe0 2 3 ≤ A stage1 2 3 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 3073859773827 241680163775794 224827700310579)) ≤ 132175970274561
  rw [cases_3_0_eq]
  decide +kernel
theorem zX17 : rawA witness recipe0 2 4 ≤ A stage1 2 4 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 213500573516 241680163775794 6707373398223)) ≤ 9180524661188
  rw [cases_3_0_eq]
  decide +kernel
theorem zX18 : rawA witness recipe0 2 5 ≤ A stage1 2 5 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 213500573516 241680163775794 6707373398223)) ≤ 7899521220092
  rw [cases_2_0_eq]
  decide +kernel
theorem zX19 : rawA witness recipe0 2 6 ≤ A stage1 2 6 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 213500573516 241680163775794 6707373398223)) ≤ 6405017205480
  rw [cases_1_0_eq]
  decide +kernel
theorem zX20 : rawA witness recipe0 2 7 ≤ A stage1 2 7 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 211423598883 241680163775794 6700230963121)) ≤ 6342707966490
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z91

section z92
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX21 : rawA witness recipe0 3 3 ≤ A stage1 3 3 := by
  change maximum ((cases 3 9).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 11 then 0 else
      c.u*3073859773827+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 3073859773827 241680163775794 224827700310579)) ≤ 4962195811150077
  rw [cases_3_1_eq]
  decide +kernel
theorem zX22 : rawA witness recipe0 3 4 ≤ A stage1 3 4 := by
  change maximum ((cases 3 9).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 11 then 0 else
      c.u*213500573516+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 213500573516 241680163775794 6707373398223)) ≤ 2490493889519166
  rw [cases_3_1_eq]
  decide +kernel
theorem zX23 : rawA witness recipe0 3 5 ≤ A stage1 3 5 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 11 then 0 else
      c.u*213500573516+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 213500573516 241680163775794 6707373398223)) ≤ 7899521220092
  rw [cases_2_0_eq]
  decide +kernel
theorem zX24 : rawA witness recipe0 3 6 ≤ A stage1 3 6 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 11 then 0 else
      c.u*213500573516+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 213500573516 241680163775794 6707373398223)) ≤ 6405017205480
  rw [cases_1_0_eq]
  decide +kernel
theorem zX25 : rawA witness recipe0 3 7 ≤ A stage1 3 7 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 11 then 0 else
      c.u*211423598883+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 211423598883 241680163775794 6700230963121)) ≤ 6342707966490
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z92

section z93
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX26 : rawA witness recipe0 4 4 ≤ A stage1 4 4 := by
  change maximum ((cases 3 9).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 12 then 0 else
      c.u*2951939743177+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 213500573516 241680163775794 6707373398223)) ≤ 2490493889519166
  rw [cases_3_1_eq]
  decide +kernel
end ZP
end z93

section z94
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX27 : rawA witness recipe0 4 5 ≤ A stage1 4 5 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 12 then 0 else
      c.u*2951939743177+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 213500573516 241680163775794 6707373398223)) ≤ 21378216494881
  rw [cases_2_0_eq]
  decide +kernel
theorem zX28 : rawA witness recipe0 4 6 ≤ A stage1 4 6 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 12 then 0 else
      c.u*2951939743177+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 213500573516 241680163775794 6707373398223)) ≤ 13766332420399
  rw [cases_1_0_eq]
  decide +kernel
theorem zX29 : rawA witness recipe0 4 7 ≤ A stage1 4 7 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 12 then 0 else
      c.u*2949862768544+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 211423598883 241680163775794 6700230963121)) ≤ 13712331079941
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z94

section z95
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX30 : rawA witness recipe0 5 5 ≤ A stage1 5 5 := by
  change maximum ((cases 2 7).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 12 then 0 else
      c.u*2951939743177+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 213500573516 241680163775794 6707373398223)) ≤ 1496303239102550
  rw [cases_2_1_eq]
  decide +kernel
theorem zX31 : rawA witness recipe0 5 6 ≤ A stage1 5 6 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 12 then 0 else
      c.u*2951939743177+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 213500573516 241680163775794 6707373398223)) ≤ 13766332420399
  rw [cases_1_0_eq]
  decide +kernel
theorem zX32 : rawA witness recipe0 5 7 ≤ A stage1 5 7 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 12 then 0 else
      c.u*2949862768544+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 211423598883 241680163775794 6700230963121)) ≤ 13712331079941
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z95

section z96
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX33 : rawA witness recipe0 6 6 ≤ A stage1 6 6 := by
  change maximum ((cases 1 5).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 12 then 0 else
      c.u*2951939743177+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 213500573516 241680163775794 6707373398223)) ≤ 750073124712919
  rw [cases_1_1_eq]
  decide +kernel
theorem zX34 : rawA witness recipe0 6 7 ≤ A stage1 6 7 := by
  change maximum ((cases 1 5).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 12 then 0 else
      c.u*2949862768544+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 211423598883 241680163775794 6700230963121)) ≤ 750003926991054
  rw [cases_1_1_eq]
  decide +kernel
end ZP
end z96

section z97
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX35 : rawA witness recipe0 7 7 ≤ A stage1 7 7 := by
  change maximum ((cases 1 5).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 13 then 0 else
      c.u*2949862768544+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 211423598883 241680163775794 6700230963121)) ≤ 750003926991054
  rw [cases_1_1_eq]
  decide +kernel
end ZP
end z97

section z125
namespace ZP
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
theorem zY0 (j : Nat) (hij : 0 ≤ j) (hj : j < 20) :
    rawA witness recipe0 0 j ≤ A stage1 0 j := by
  interval_cases j
  · exact zX0
  · exact zX1
  · exact zX2
  · exact zX3
  · exact zX4
  · exact zX5
  · exact zX6
  · exact zX7
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
theorem zY1 (j : Nat) (hij : 1 ≤ j) (hj : j < 20) :
    rawA witness recipe0 1 j ≤ A stage1 1 j := by
  interval_cases j
  · exact zX8
  · exact zX9
  · exact zX10
  · exact zX11
  · exact zX12
  · exact zX13
  · exact zX14
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
theorem zY2 (j : Nat) (hij : 2 ≤ j) (hj : j < 20) :
    rawA witness recipe0 2 j ≤ A stage1 2 j := by
  interval_cases j
  · exact zX15
  · exact zX16
  · exact zX17
  · exact zX18
  · exact zX19
  · exact zX20
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
theorem zY3 (j : Nat) (hij : 3 ≤ j) (hj : j < 20) :
    rawA witness recipe0 3 j ≤ A stage1 3 j := by
  interval_cases j
  · exact zX21
  · exact zX22
  · exact zX23
  · exact zX24
  · exact zX25
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
theorem zY4 (j : Nat) (hij : 4 ≤ j) (hj : j < 20) :
    rawA witness recipe0 4 j ≤ A stage1 4 j := by
  interval_cases j
  · exact zX26
  · exact zX27
  · exact zX28
  · exact zX29
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
theorem zY5 (j : Nat) (hij : 5 ≤ j) (hj : j < 20) :
    rawA witness recipe0 5 j ≤ A stage1 5 j := by
  interval_cases j
  · exact zX30
  · exact zX31
  · exact zX32
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
theorem zY6 (j : Nat) (hij : 6 ≤ j) (hj : j < 20) :
    rawA witness recipe0 6 j ≤ A stage1 6 j := by
  interval_cases j
  · exact zX33
  · exact zX34
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
theorem zY7 (j : Nat) (hij : 7 ≤ j) (hj : j < 20) :
    rawA witness recipe0 7 j ≤ A stage1 7 j := by
  interval_cases j
  · exact zX35
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
theorem zY8 (j : Nat) (hij : 8 ≤ j) (hj : j < 20) :
    rawA witness recipe0 8 j ≤ A stage1 8 j := by
  interval_cases j <;> decide +kernel
theorem zY9 (j : Nat) (hij : 9 ≤ j) (hj : j < 20) :
    rawA witness recipe0 9 j ≤ A stage1 9 j := by
  interval_cases j <;> decide +kernel
theorem zY10 (j : Nat) (hij : 10 ≤ j) (hj : j < 20) :
    rawA witness recipe0 10 j ≤ A stage1 10 j := by
  interval_cases j <;> decide +kernel
theorem zY11 (j : Nat) (hij : 11 ≤ j) (hj : j < 20) :
    rawA witness recipe0 11 j ≤ A stage1 11 j := by
  interval_cases j <;> decide +kernel
theorem zY12 (j : Nat) (hij : 12 ≤ j) (hj : j < 20) :
    rawA witness recipe0 12 j ≤ A stage1 12 j := by
  interval_cases j <;> decide +kernel
theorem zY13 (j : Nat) (hij : 13 ≤ j) (hj : j < 20) :
    rawA witness recipe0 13 j ≤ A stage1 13 j := by
  interval_cases j <;> decide +kernel
theorem zY14 (j : Nat) (hij : 14 ≤ j) (hj : j < 20) :
    rawA witness recipe0 14 j ≤ A stage1 14 j := by
  interval_cases j <;> decide +kernel
theorem zY15 (j : Nat) (hij : 15 ≤ j) (hj : j < 20) :
    rawA witness recipe0 15 j ≤ A stage1 15 j := by
  interval_cases j <;> decide +kernel
theorem zY16 (j : Nat) (hij : 16 ≤ j) (hj : j < 20) :
    rawA witness recipe0 16 j ≤ A stage1 16 j := by
  interval_cases j <;> decide +kernel
theorem zY17 (j : Nat) (hij : 17 ≤ j) (hj : j < 20) :
    rawA witness recipe0 17 j ≤ A stage1 17 j := by
  interval_cases j <;> decide +kernel
theorem zY18 (j : Nat) (hij : 18 ≤ j) (hj : j < 20) :
    rawA witness recipe0 18 j ≤ A stage1 18 j := by
  interval_cases j <;> decide +kernel
theorem zY19 (j : Nat) (hij : 19 ≤ j) (hj : j < 20) :
    rawA witness recipe0 19 j ≤ A stage1 19 j := by
  interval_cases j <;> decide +kernel
theorem zY20 (i j : Nat) (hij : i ≤ j) (hj : j < 20) :
    rawA witness recipe0 i j ≤ A stage1 i j := by
  have hi : i < 20 := Nat.lt_of_le_of_lt hij hj
  interval_cases i
  · exact zY0 j hij hj
  · exact zY1 j hij hj
  · exact zY2 j hij hj
  · exact zY3 j hij hj
  · exact zY4 j hij hj
  · exact zY5 j hij hj
  · exact zY6 j hij hj
  · exact zY7 j hij hj
  · exact zY8 j hij hj
  · exact zY9 j hij hj
  · exact zY10 j hij hj
  · exact zY11 j hij hj
  · exact zY12 j hij hj
  · exact zY13 j hij hj
  · exact zY14 j hij hj
  · exact zY15 j hij hj
  · exact zY16 j hij hj
  · exact zY17 j hij hj
  · exact zY18 j hij hj
  · exact zY19 j hij hj
theorem zY21 (j : Nat) (hij : 0 ≤ j) (hj : j < 20) :
    rawB witness recipe0 0 j ≤ B stage1 0 j := by
  interval_cases j <;> decide +kernel
theorem zY22 (j : Nat) (hij : 1 ≤ j) (hj : j < 20) :
    rawB witness recipe0 1 j ≤ B stage1 1 j := by
  interval_cases j <;> decide +kernel
theorem zY23 (j : Nat) (hij : 2 ≤ j) (hj : j < 20) :
    rawB witness recipe0 2 j ≤ B stage1 2 j := by
  interval_cases j <;> decide +kernel
theorem zY24 (j : Nat) (hij : 3 ≤ j) (hj : j < 20) :
    rawB witness recipe0 3 j ≤ B stage1 3 j := by
  interval_cases j <;> decide +kernel
theorem zY25 (j : Nat) (hij : 4 ≤ j) (hj : j < 20) :
    rawB witness recipe0 4 j ≤ B stage1 4 j := by
  interval_cases j <;> decide +kernel
theorem zY26 (j : Nat) (hij : 5 ≤ j) (hj : j < 20) :
    rawB witness recipe0 5 j ≤ B stage1 5 j := by
  interval_cases j <;> decide +kernel
theorem zY27 (j : Nat) (hij : 6 ≤ j) (hj : j < 20) :
    rawB witness recipe0 6 j ≤ B stage1 6 j := by
  interval_cases j <;> decide +kernel
theorem zY28 (j : Nat) (hij : 7 ≤ j) (hj : j < 20) :
    rawB witness recipe0 7 j ≤ B stage1 7 j := by
  interval_cases j <;> decide +kernel
theorem zY29 (j : Nat) (hij : 8 ≤ j) (hj : j < 20) :
    rawB witness recipe0 8 j ≤ B stage1 8 j := by
  interval_cases j <;> decide +kernel
theorem zY30 (j : Nat) (hij : 9 ≤ j) (hj : j < 20) :
    rawB witness recipe0 9 j ≤ B stage1 9 j := by
  interval_cases j <;> decide +kernel
theorem zY31 (j : Nat) (hij : 10 ≤ j) (hj : j < 20) :
    rawB witness recipe0 10 j ≤ B stage1 10 j := by
  interval_cases j <;> decide +kernel
theorem zY32 (j : Nat) (hij : 11 ≤ j) (hj : j < 20) :
    rawB witness recipe0 11 j ≤ B stage1 11 j := by
  interval_cases j <;> decide +kernel
theorem zY33 (j : Nat) (hij : 12 ≤ j) (hj : j < 20) :
    rawB witness recipe0 12 j ≤ B stage1 12 j := by
  interval_cases j <;> decide +kernel
theorem zY34 (j : Nat) (hij : 13 ≤ j) (hj : j < 20) :
    rawB witness recipe0 13 j ≤ B stage1 13 j := by
  interval_cases j <;> decide +kernel
theorem zY35 (j : Nat) (hij : 14 ≤ j) (hj : j < 20) :
    rawB witness recipe0 14 j ≤ B stage1 14 j := by
  interval_cases j <;> decide +kernel
theorem zY36 (j : Nat) (hij : 15 ≤ j) (hj : j < 20) :
    rawB witness recipe0 15 j ≤ B stage1 15 j := by
  interval_cases j <;> decide +kernel
theorem zY37 (j : Nat) (hij : 16 ≤ j) (hj : j < 20) :
    rawB witness recipe0 16 j ≤ B stage1 16 j := by
  interval_cases j <;> decide +kernel
theorem zY38 (j : Nat) (hij : 17 ≤ j) (hj : j < 20) :
    rawB witness recipe0 17 j ≤ B stage1 17 j := by
  interval_cases j <;> decide +kernel
theorem zY39 (j : Nat) (hij : 18 ≤ j) (hj : j < 20) :
    rawB witness recipe0 18 j ≤ B stage1 18 j := by
  interval_cases j <;> decide +kernel
theorem zY40 (j : Nat) (hij : 19 ≤ j) (hj : j < 20) :
    rawB witness recipe0 19 j ≤ B stage1 19 j := by
  interval_cases j <;> decide +kernel
theorem zY41 (i j : Nat) (hij : i ≤ j) (hj : j < 20) :
    rawB witness recipe0 i j ≤ B stage1 i j := by
  have hi : i < 20 := Nat.lt_of_le_of_lt hij hj
  interval_cases i
  · exact zY21 j hij hj
  · exact zY22 j hij hj
  · exact zY23 j hij hj
  · exact zY24 j hij hj
  · exact zY25 j hij hj
  · exact zY26 j hij hj
  · exact zY27 j hij hj
  · exact zY28 j hij hj
  · exact zY29 j hij hj
  · exact zY30 j hij hj
  · exact zY31 j hij hj
  · exact zY32 j hij hj
  · exact zY33 j hij hj
  · exact zY34 j hij hj
  · exact zY35 j hij hj
  · exact zY36 j hij hj
  · exact zY37 j hij hj
  · exact zY38 j hij hj
  · exact zY39 j hij hj
  · exact zY40 j hij hj
theorem zY42 (j : Nat) (hij : 0 ≤ j) (hj : j < 19) :
    rawM witness recipe0 0 j ≤ M stage1 0 j := by
  interval_cases j <;> decide +kernel
theorem zY43 (j : Nat) (hij : 1 ≤ j) (hj : j < 19) :
    rawM witness recipe0 1 j ≤ M stage1 1 j := by
  interval_cases j <;> decide +kernel
theorem zY44 (j : Nat) (hij : 2 ≤ j) (hj : j < 19) :
    rawM witness recipe0 2 j ≤ M stage1 2 j := by
  interval_cases j <;> decide +kernel
theorem zY45 (j : Nat) (hij : 3 ≤ j) (hj : j < 19) :
    rawM witness recipe0 3 j ≤ M stage1 3 j := by
  interval_cases j <;> decide +kernel
theorem zY46 (j : Nat) (hij : 4 ≤ j) (hj : j < 19) :
    rawM witness recipe0 4 j ≤ M stage1 4 j := by
  interval_cases j <;> decide +kernel
theorem zY47 (j : Nat) (hij : 5 ≤ j) (hj : j < 19) :
    rawM witness recipe0 5 j ≤ M stage1 5 j := by
  interval_cases j <;> decide +kernel
theorem zY48 (j : Nat) (hij : 6 ≤ j) (hj : j < 19) :
    rawM witness recipe0 6 j ≤ M stage1 6 j := by
  interval_cases j <;> decide +kernel
theorem zY49 (j : Nat) (hij : 7 ≤ j) (hj : j < 19) :
    rawM witness recipe0 7 j ≤ M stage1 7 j := by
  interval_cases j <;> decide +kernel
theorem zY50 (j : Nat) (hij : 8 ≤ j) (hj : j < 19) :
    rawM witness recipe0 8 j ≤ M stage1 8 j := by
  interval_cases j <;> decide +kernel
theorem zY51 (j : Nat) (hij : 9 ≤ j) (hj : j < 19) :
    rawM witness recipe0 9 j ≤ M stage1 9 j := by
  interval_cases j <;> decide +kernel
theorem zY52 (j : Nat) (hij : 10 ≤ j) (hj : j < 19) :
    rawM witness recipe0 10 j ≤ M stage1 10 j := by
  interval_cases j <;> decide +kernel
theorem zY53 (j : Nat) (hij : 11 ≤ j) (hj : j < 19) :
    rawM witness recipe0 11 j ≤ M stage1 11 j := by
  interval_cases j <;> decide +kernel
theorem zY54 (j : Nat) (hij : 12 ≤ j) (hj : j < 19) :
    rawM witness recipe0 12 j ≤ M stage1 12 j := by
  interval_cases j <;> decide +kernel
theorem zY55 (j : Nat) (hij : 13 ≤ j) (hj : j < 19) :
    rawM witness recipe0 13 j ≤ M stage1 13 j := by
  interval_cases j <;> decide +kernel
theorem zY56 (j : Nat) (hij : 14 ≤ j) (hj : j < 19) :
    rawM witness recipe0 14 j ≤ M stage1 14 j := by
  interval_cases j <;> decide +kernel
theorem zY57 (j : Nat) (hij : 15 ≤ j) (hj : j < 19) :
    rawM witness recipe0 15 j ≤ M stage1 15 j := by
  interval_cases j <;> decide +kernel
theorem zY58 (j : Nat) (hij : 16 ≤ j) (hj : j < 19) :
    rawM witness recipe0 16 j ≤ M stage1 16 j := by
  interval_cases j <;> decide +kernel
theorem zY59 (j : Nat) (hij : 17 ≤ j) (hj : j < 19) :
    rawM witness recipe0 17 j ≤ M stage1 17 j := by
  interval_cases j <;> decide +kernel
theorem zY60 (j : Nat) (hij : 18 ≤ j) (hj : j < 19) :
    rawM witness recipe0 18 j ≤ M stage1 18 j := by
  interval_cases j <;> decide +kernel
theorem zY61 (i j : Nat) (hij : i ≤ j) (hj : j < 19) :
    rawM witness recipe0 i j ≤ M stage1 i j := by
  have hi : i < 19 := Nat.lt_of_le_of_lt hij hj
  interval_cases i
  · exact zY42 j hij hj
  · exact zY43 j hij hj
  · exact zY44 j hij hj
  · exact zY45 j hij hj
  · exact zY46 j hij hj
  · exact zY47 j hij hj
  · exact zY48 j hij hj
  · exact zY49 j hij hj
  · exact zY50 j hij hj
  · exact zY51 j hij hj
  · exact zY52 j hij hj
  · exact zY53 j hij hj
  · exact zY54 j hij hj
  · exact zY55 j hij hj
  · exact zY56 j hij hj
  · exact zY57 j hij hj
  · exact zY58 j hij hj
  · exact zY59 j hij hj
  · exact zY60 j hij hj
theorem zY62 (l : Nat) (hjl : 0 < l) (hl : l < 20) :
    rawP witness recipe0 0 l ≤ P stage1 0 l := by
  interval_cases l
  · change rawA witness recipe0 1 1 ≤ A stage1 1 1
    exact zX8
  · change rawA witness recipe0 1 2 ≤ A stage1 1 2
    exact zX9
  · change rawA witness recipe0 1 3 ≤ A stage1 1 3
    exact zX10
  · change rawA witness recipe0 1 4 ≤ A stage1 1 4
    exact zX11
  · change rawA witness recipe0 1 5 ≤ A stage1 1 5
    exact zX12
  · change rawA witness recipe0 1 6 ≤ A stage1 1 6
    exact zX13
  · change rawA witness recipe0 1 7 ≤ A stage1 1 7
    exact zX14
  · change rawA witness recipe0 1 8 ≤ A stage1 1 8
    decide +kernel
  · change rawA witness recipe0 1 9 ≤ A stage1 1 9
    decide +kernel
  · change rawA witness recipe0 1 10 ≤ A stage1 1 10
    decide +kernel
  · change rawA witness recipe0 1 11 ≤ A stage1 1 11
    decide +kernel
  · change rawA witness recipe0 1 12 ≤ A stage1 1 12
    decide +kernel
  · change rawA witness recipe0 1 13 ≤ A stage1 1 13
    decide +kernel
  · change rawA witness recipe0 1 14 ≤ A stage1 1 14
    decide +kernel
  · change rawA witness recipe0 1 15 ≤ A stage1 1 15
    decide +kernel
  · change rawA witness recipe0 1 16 ≤ A stage1 1 16
    decide +kernel
  · change rawA witness recipe0 1 17 ≤ A stage1 1 17
    decide +kernel
  · change rawA witness recipe0 1 18 ≤ A stage1 1 18
    decide +kernel
  · change rawA witness recipe0 1 19 ≤ A stage1 1 19
    decide +kernel
theorem zY63 (l : Nat) (hjl : 1 < l) (hl : l < 20) :
    rawP witness recipe0 1 l ≤ P stage1 1 l := by
  interval_cases l
  · change rawA witness recipe0 2 2 ≤ A stage1 2 2
    exact zX15
  · change rawA witness recipe0 2 3 ≤ A stage1 2 3
    exact zX16
  · change rawA witness recipe0 2 4 ≤ A stage1 2 4
    exact zX17
  · change rawA witness recipe0 2 5 ≤ A stage1 2 5
    exact zX18
  · change rawA witness recipe0 2 6 ≤ A stage1 2 6
    exact zX19
  · change rawA witness recipe0 2 7 ≤ A stage1 2 7
    exact zX20
  · change rawA witness recipe0 2 8 ≤ A stage1 2 8
    decide +kernel
  · change rawA witness recipe0 2 9 ≤ A stage1 2 9
    decide +kernel
  · change rawA witness recipe0 2 10 ≤ A stage1 2 10
    decide +kernel
  · change rawA witness recipe0 2 11 ≤ A stage1 2 11
    decide +kernel
  · change rawA witness recipe0 2 12 ≤ A stage1 2 12
    decide +kernel
  · change rawA witness recipe0 2 13 ≤ A stage1 2 13
    decide +kernel
  · change rawA witness recipe0 2 14 ≤ A stage1 2 14
    decide +kernel
  · change rawA witness recipe0 2 15 ≤ A stage1 2 15
    decide +kernel
  · change rawA witness recipe0 2 16 ≤ A stage1 2 16
    decide +kernel
  · change rawA witness recipe0 2 17 ≤ A stage1 2 17
    decide +kernel
  · change rawA witness recipe0 2 18 ≤ A stage1 2 18
    decide +kernel
  · change rawA witness recipe0 2 19 ≤ A stage1 2 19
    decide +kernel
theorem zY64 (l : Nat) (hjl : 2 < l) (hl : l < 20) :
    rawP witness recipe0 2 l ≤ P stage1 2 l := by
  interval_cases l
  · change rawA witness recipe0 3 3 ≤ A stage1 3 3
    exact zX21
  · change rawA witness recipe0 3 4 ≤ A stage1 3 4
    exact zX22
  · change rawA witness recipe0 3 5 ≤ A stage1 3 5
    exact zX23
  · change rawA witness recipe0 3 6 ≤ A stage1 3 6
    exact zX24
  · change rawA witness recipe0 3 7 ≤ A stage1 3 7
    exact zX25
  · change rawA witness recipe0 3 8 ≤ A stage1 3 8
    decide +kernel
  · change rawA witness recipe0 3 9 ≤ A stage1 3 9
    decide +kernel
  · change rawA witness recipe0 3 10 ≤ A stage1 3 10
    decide +kernel
  · change rawA witness recipe0 3 11 ≤ A stage1 3 11
    decide +kernel
  · change rawA witness recipe0 3 12 ≤ A stage1 3 12
    decide +kernel
  · change rawA witness recipe0 3 13 ≤ A stage1 3 13
    decide +kernel
  · change rawA witness recipe0 3 14 ≤ A stage1 3 14
    decide +kernel
  · change rawA witness recipe0 3 15 ≤ A stage1 3 15
    decide +kernel
  · change rawA witness recipe0 3 16 ≤ A stage1 3 16
    decide +kernel
  · change rawA witness recipe0 3 17 ≤ A stage1 3 17
    decide +kernel
  · change rawA witness recipe0 3 18 ≤ A stage1 3 18
    decide +kernel
  · change rawA witness recipe0 3 19 ≤ A stage1 3 19
    decide +kernel
theorem zY65 (l : Nat) (hjl : 3 < l) (hl : l < 20) :
    rawP witness recipe0 3 l ≤ P stage1 3 l := by
  interval_cases l
  · change rawA witness recipe0 4 4 ≤ A stage1 4 4
    exact zX26
  · change rawA witness recipe0 4 5 ≤ A stage1 4 5
    exact zX27
  · change rawA witness recipe0 4 6 ≤ A stage1 4 6
    exact zX28
  · change rawA witness recipe0 4 7 ≤ A stage1 4 7
    exact zX29
  · change rawA witness recipe0 4 8 ≤ A stage1 4 8
    decide +kernel
  · change rawA witness recipe0 4 9 ≤ A stage1 4 9
    decide +kernel
  · change rawA witness recipe0 4 10 ≤ A stage1 4 10
    decide +kernel
  · change rawA witness recipe0 4 11 ≤ A stage1 4 11
    decide +kernel
  · change rawA witness recipe0 4 12 ≤ A stage1 4 12
    decide +kernel
  · change rawA witness recipe0 4 13 ≤ A stage1 4 13
    decide +kernel
  · change rawA witness recipe0 4 14 ≤ A stage1 4 14
    decide +kernel
  · change rawA witness recipe0 4 15 ≤ A stage1 4 15
    decide +kernel
  · change rawA witness recipe0 4 16 ≤ A stage1 4 16
    decide +kernel
  · change rawA witness recipe0 4 17 ≤ A stage1 4 17
    decide +kernel
  · change rawA witness recipe0 4 18 ≤ A stage1 4 18
    decide +kernel
  · change rawA witness recipe0 4 19 ≤ A stage1 4 19
    decide +kernel
theorem zY66 (l : Nat) (hjl : 4 < l) (hl : l < 20) :
    rawP witness recipe0 4 l ≤ P stage1 4 l := by
  interval_cases l
  · change rawA witness recipe0 5 5 ≤ A stage1 5 5
    exact zX30
  · change rawA witness recipe0 5 6 ≤ A stage1 5 6
    exact zX31
  · change rawA witness recipe0 5 7 ≤ A stage1 5 7
    exact zX32
  · change rawA witness recipe0 5 8 ≤ A stage1 5 8
    decide +kernel
  · change rawA witness recipe0 5 9 ≤ A stage1 5 9
    decide +kernel
  · change rawA witness recipe0 5 10 ≤ A stage1 5 10
    decide +kernel
  · change rawA witness recipe0 5 11 ≤ A stage1 5 11
    decide +kernel
  · change rawA witness recipe0 5 12 ≤ A stage1 5 12
    decide +kernel
  · change rawA witness recipe0 5 13 ≤ A stage1 5 13
    decide +kernel
  · change rawA witness recipe0 5 14 ≤ A stage1 5 14
    decide +kernel
  · change rawA witness recipe0 5 15 ≤ A stage1 5 15
    decide +kernel
  · change rawA witness recipe0 5 16 ≤ A stage1 5 16
    decide +kernel
  · change rawA witness recipe0 5 17 ≤ A stage1 5 17
    decide +kernel
  · change rawA witness recipe0 5 18 ≤ A stage1 5 18
    decide +kernel
  · change rawA witness recipe0 5 19 ≤ A stage1 5 19
    decide +kernel
theorem zY67 (l : Nat) (hjl : 5 < l) (hl : l < 20) :
    rawP witness recipe0 5 l ≤ P stage1 5 l := by
  interval_cases l
  · change rawA witness recipe0 6 6 ≤ A stage1 6 6
    exact zX33
  · change rawA witness recipe0 6 7 ≤ A stage1 6 7
    exact zX34
  · change rawA witness recipe0 6 8 ≤ A stage1 6 8
    decide +kernel
  · change rawA witness recipe0 6 9 ≤ A stage1 6 9
    decide +kernel
  · change rawA witness recipe0 6 10 ≤ A stage1 6 10
    decide +kernel
  · change rawA witness recipe0 6 11 ≤ A stage1 6 11
    decide +kernel
  · change rawA witness recipe0 6 12 ≤ A stage1 6 12
    decide +kernel
  · change rawA witness recipe0 6 13 ≤ A stage1 6 13
    decide +kernel
  · change rawA witness recipe0 6 14 ≤ A stage1 6 14
    decide +kernel
  · change rawA witness recipe0 6 15 ≤ A stage1 6 15
    decide +kernel
  · change rawA witness recipe0 6 16 ≤ A stage1 6 16
    decide +kernel
  · change rawA witness recipe0 6 17 ≤ A stage1 6 17
    decide +kernel
  · change rawA witness recipe0 6 18 ≤ A stage1 6 18
    decide +kernel
  · change rawA witness recipe0 6 19 ≤ A stage1 6 19
    decide +kernel
theorem zY68 (l : Nat) (hjl : 6 < l) (hl : l < 20) :
    rawP witness recipe0 6 l ≤ P stage1 6 l := by
  interval_cases l
  · change rawA witness recipe0 7 7 ≤ A stage1 7 7
    exact zX35
  · change rawA witness recipe0 7 8 ≤ A stage1 7 8
    decide +kernel
  · change rawA witness recipe0 7 9 ≤ A stage1 7 9
    decide +kernel
  · change rawA witness recipe0 7 10 ≤ A stage1 7 10
    decide +kernel
  · change rawA witness recipe0 7 11 ≤ A stage1 7 11
    decide +kernel
  · change rawA witness recipe0 7 12 ≤ A stage1 7 12
    decide +kernel
  · change rawA witness recipe0 7 13 ≤ A stage1 7 13
    decide +kernel
  · change rawA witness recipe0 7 14 ≤ A stage1 7 14
    decide +kernel
  · change rawA witness recipe0 7 15 ≤ A stage1 7 15
    decide +kernel
  · change rawA witness recipe0 7 16 ≤ A stage1 7 16
    decide +kernel
  · change rawA witness recipe0 7 17 ≤ A stage1 7 17
    decide +kernel
  · change rawA witness recipe0 7 18 ≤ A stage1 7 18
    decide +kernel
  · change rawA witness recipe0 7 19 ≤ A stage1 7 19
    decide +kernel
theorem zY69 (l : Nat) (hjl : 7 < l) (hl : l < 20) :
    rawP witness recipe0 7 l ≤ P stage1 7 l := by
  interval_cases l
  · change rawA witness recipe0 8 8 ≤ A stage1 8 8
    decide +kernel
  · change rawA witness recipe0 8 9 ≤ A stage1 8 9
    decide +kernel
  · change rawA witness recipe0 8 10 ≤ A stage1 8 10
    decide +kernel
  · change rawA witness recipe0 8 11 ≤ A stage1 8 11
    decide +kernel
  · change rawA witness recipe0 8 12 ≤ A stage1 8 12
    decide +kernel
  · change rawA witness recipe0 8 13 ≤ A stage1 8 13
    decide +kernel
  · change rawA witness recipe0 8 14 ≤ A stage1 8 14
    decide +kernel
  · change rawA witness recipe0 8 15 ≤ A stage1 8 15
    decide +kernel
  · change rawA witness recipe0 8 16 ≤ A stage1 8 16
    decide +kernel
  · change rawA witness recipe0 8 17 ≤ A stage1 8 17
    decide +kernel
  · change rawA witness recipe0 8 18 ≤ A stage1 8 18
    decide +kernel
  · change rawA witness recipe0 8 19 ≤ A stage1 8 19
    decide +kernel
theorem zY70 (l : Nat) (hjl : 8 < l) (hl : l < 20) :
    rawP witness recipe0 8 l ≤ P stage1 8 l := by
  interval_cases l
  · change rawA witness recipe0 9 9 ≤ A stage1 9 9
    decide +kernel
  · change rawA witness recipe0 9 10 ≤ A stage1 9 10
    decide +kernel
  · change rawA witness recipe0 9 11 ≤ A stage1 9 11
    decide +kernel
  · change rawA witness recipe0 9 12 ≤ A stage1 9 12
    decide +kernel
  · change rawA witness recipe0 9 13 ≤ A stage1 9 13
    decide +kernel
  · change rawA witness recipe0 9 14 ≤ A stage1 9 14
    decide +kernel
  · change rawA witness recipe0 9 15 ≤ A stage1 9 15
    decide +kernel
  · change rawA witness recipe0 9 16 ≤ A stage1 9 16
    decide +kernel
  · change rawA witness recipe0 9 17 ≤ A stage1 9 17
    decide +kernel
  · change rawA witness recipe0 9 18 ≤ A stage1 9 18
    decide +kernel
  · change rawA witness recipe0 9 19 ≤ A stage1 9 19
    decide +kernel
theorem zY71 (l : Nat) (hjl : 9 < l) (hl : l < 20) :
    rawP witness recipe0 9 l ≤ P stage1 9 l := by
  interval_cases l
  · change rawA witness recipe0 10 10 ≤ A stage1 10 10
    decide +kernel
  · change rawA witness recipe0 10 11 ≤ A stage1 10 11
    decide +kernel
  · change rawA witness recipe0 10 12 ≤ A stage1 10 12
    decide +kernel
  · change rawA witness recipe0 10 13 ≤ A stage1 10 13
    decide +kernel
  · change rawA witness recipe0 10 14 ≤ A stage1 10 14
    decide +kernel
  · change rawA witness recipe0 10 15 ≤ A stage1 10 15
    decide +kernel
  · change rawA witness recipe0 10 16 ≤ A stage1 10 16
    decide +kernel
  · change rawA witness recipe0 10 17 ≤ A stage1 10 17
    decide +kernel
  · change rawA witness recipe0 10 18 ≤ A stage1 10 18
    decide +kernel
  · change rawA witness recipe0 10 19 ≤ A stage1 10 19
    decide +kernel
theorem zY72 (l : Nat) (hjl : 10 < l) (hl : l < 20) :
    rawP witness recipe0 10 l ≤ P stage1 10 l := by
  interval_cases l
  · change rawA witness recipe0 11 11 ≤ A stage1 11 11
    decide +kernel
  · change rawA witness recipe0 11 12 ≤ A stage1 11 12
    decide +kernel
  · change rawA witness recipe0 11 13 ≤ A stage1 11 13
    decide +kernel
  · change rawA witness recipe0 11 14 ≤ A stage1 11 14
    decide +kernel
  · change rawA witness recipe0 11 15 ≤ A stage1 11 15
    decide +kernel
  · change rawA witness recipe0 11 16 ≤ A stage1 11 16
    decide +kernel
  · change rawA witness recipe0 11 17 ≤ A stage1 11 17
    decide +kernel
  · change rawA witness recipe0 11 18 ≤ A stage1 11 18
    decide +kernel
  · change rawA witness recipe0 11 19 ≤ A stage1 11 19
    decide +kernel
theorem zY73 (l : Nat) (hjl : 11 < l) (hl : l < 20) :
    rawP witness recipe0 11 l ≤ P stage1 11 l := by
  interval_cases l
  · change rawA witness recipe0 12 12 ≤ A stage1 12 12
    decide +kernel
  · change rawA witness recipe0 12 13 ≤ A stage1 12 13
    decide +kernel
  · change rawA witness recipe0 12 14 ≤ A stage1 12 14
    decide +kernel
  · change rawA witness recipe0 12 15 ≤ A stage1 12 15
    decide +kernel
  · change rawA witness recipe0 12 16 ≤ A stage1 12 16
    decide +kernel
  · change rawA witness recipe0 12 17 ≤ A stage1 12 17
    decide +kernel
  · change rawA witness recipe0 12 18 ≤ A stage1 12 18
    decide +kernel
  · change rawA witness recipe0 12 19 ≤ A stage1 12 19
    decide +kernel
theorem zY74 (l : Nat) (hjl : 12 < l) (hl : l < 20) :
    rawP witness recipe0 12 l ≤ P stage1 12 l := by
  interval_cases l
  · change rawA witness recipe0 13 13 ≤ A stage1 13 13
    decide +kernel
  · change rawA witness recipe0 13 14 ≤ A stage1 13 14
    decide +kernel
  · change rawA witness recipe0 13 15 ≤ A stage1 13 15
    decide +kernel
  · change rawA witness recipe0 13 16 ≤ A stage1 13 16
    decide +kernel
  · change rawA witness recipe0 13 17 ≤ A stage1 13 17
    decide +kernel
  · change rawA witness recipe0 13 18 ≤ A stage1 13 18
    decide +kernel
  · change rawA witness recipe0 13 19 ≤ A stage1 13 19
    decide +kernel
theorem zY75 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawP witness recipe0 13 l ≤ P stage1 13 l := by
  interval_cases l
  · change rawA witness recipe0 14 14 ≤ A stage1 14 14
    decide +kernel
  · change rawA witness recipe0 14 15 ≤ A stage1 14 15
    decide +kernel
  · change rawA witness recipe0 14 16 ≤ A stage1 14 16
    decide +kernel
  · change rawA witness recipe0 14 17 ≤ A stage1 14 17
    decide +kernel
  · change rawA witness recipe0 14 18 ≤ A stage1 14 18
    decide +kernel
  · change rawA witness recipe0 14 19 ≤ A stage1 14 19
    decide +kernel
theorem zY76 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawP witness recipe0 14 l ≤ P stage1 14 l := by
  interval_cases l
  · change rawA witness recipe0 15 15 ≤ A stage1 15 15
    decide +kernel
  · change rawA witness recipe0 15 16 ≤ A stage1 15 16
    decide +kernel
  · change rawA witness recipe0 15 17 ≤ A stage1 15 17
    decide +kernel
  · change rawA witness recipe0 15 18 ≤ A stage1 15 18
    decide +kernel
  · change rawA witness recipe0 15 19 ≤ A stage1 15 19
    decide +kernel
theorem zY77 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawP witness recipe0 15 l ≤ P stage1 15 l := by
  interval_cases l
  · change rawA witness recipe0 16 16 ≤ A stage1 16 16
    decide +kernel
  · change rawA witness recipe0 16 17 ≤ A stage1 16 17
    decide +kernel
  · change rawA witness recipe0 16 18 ≤ A stage1 16 18
    decide +kernel
  · change rawA witness recipe0 16 19 ≤ A stage1 16 19
    decide +kernel
theorem zY78 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawP witness recipe0 16 l ≤ P stage1 16 l := by
  interval_cases l
  · change rawA witness recipe0 17 17 ≤ A stage1 17 17
    decide +kernel
  · change rawA witness recipe0 17 18 ≤ A stage1 17 18
    decide +kernel
  · change rawA witness recipe0 17 19 ≤ A stage1 17 19
    decide +kernel
theorem zY79 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawP witness recipe0 17 l ≤ P stage1 17 l := by
  interval_cases l
  · change rawA witness recipe0 18 18 ≤ A stage1 18 18
    decide +kernel
  · change rawA witness recipe0 18 19 ≤ A stage1 18 19
    decide +kernel
theorem zY80 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawP witness recipe0 18 l ≤ P stage1 18 l := by
  interval_cases l
  · change rawA witness recipe0 19 19 ≤ A stage1 19 19
    decide +kernel
theorem zY81 (j l : Nat) (hjl : j < l) (hl : l < 20) :
    rawP witness recipe0 j l ≤ P stage1 j l := by
  have hj : j < 19 := by omega
  interval_cases j
  · exact zY62 l hjl hl
  · exact zY63 l hjl hl
  · exact zY64 l hjl hl
  · exact zY65 l hjl hl
  · exact zY66 l hjl hl
  · exact zY67 l hjl hl
  · exact zY68 l hjl hl
  · exact zY69 l hjl hl
  · exact zY70 l hjl hl
  · exact zY71 l hjl hl
  · exact zY72 l hjl hl
  · exact zY73 l hjl hl
  · exact zY74 l hjl hl
  · exact zY75 l hjl hl
  · exact zY76 l hjl hl
  · exact zY77 l hjl hl
  · exact zY78 l hjl hl
  · exact zY79 l hjl hl
  · exact zY80 l hjl hl

theorem nonzero_tolerance_0 : ∀ i : Fin 8,
    (recipe0[i.val]?.getD default).tol ≠ 0 := by decide +kernel

theorem nonzero_d_sum_0 : ∀ (i : Fin 8) (j l : Fin 20),
    i.val ≤ j.val → j.val < l.val →
    D stage1 i.val j.val l.val = M stage1 i.val j.val + P stage1 j.val l.val := by
  decide +kernel

theorem zY82 (l : Nat) (hjl : 8 < l) (hl : l < 20) :
    rawD witness recipe0 8 8 l ≤ D stage1 8 8 l := by
  interval_cases l <;> decide +kernel
theorem zY83 (i l : Nat)
    (hi : 8 ≤ i) (hij : i ≤ 8) (hjl : 8 < l) (hl : l < 20) :
    rawD witness recipe0 i 8 l ≤ D stage1 i 8 l := by
  interval_cases i
  · exact zY82 l hjl hl
theorem zY84 (l : Nat) (hjl : 9 < l) (hl : l < 20) :
    rawD witness recipe0 8 9 l ≤ D stage1 8 9 l := by
  interval_cases l <;> decide +kernel
theorem zY85 (l : Nat) (hjl : 9 < l) (hl : l < 20) :
    rawD witness recipe0 9 9 l ≤ D stage1 9 9 l := by
  interval_cases l <;> decide +kernel
theorem zY86 (i l : Nat)
    (hi : 8 ≤ i) (hij : i ≤ 9) (hjl : 9 < l) (hl : l < 20) :
    rawD witness recipe0 i 9 l ≤ D stage1 i 9 l := by
  interval_cases i
  · exact zY84 l hjl hl
  · exact zY85 l hjl hl
theorem zY87 (l : Nat) (hjl : 10 < l) (hl : l < 20) :
    rawD witness recipe0 8 10 l ≤ D stage1 8 10 l := by
  interval_cases l <;> decide +kernel
theorem zY88 (l : Nat) (hjl : 10 < l) (hl : l < 20) :
    rawD witness recipe0 9 10 l ≤ D stage1 9 10 l := by
  interval_cases l <;> decide +kernel
theorem zY89 (l : Nat) (hjl : 10 < l) (hl : l < 20) :
    rawD witness recipe0 10 10 l ≤ D stage1 10 10 l := by
  interval_cases l <;> decide +kernel
theorem zY90 (i l : Nat)
    (hi : 8 ≤ i) (hij : i ≤ 10) (hjl : 10 < l) (hl : l < 20) :
    rawD witness recipe0 i 10 l ≤ D stage1 i 10 l := by
  interval_cases i
  · exact zY87 l hjl hl
  · exact zY88 l hjl hl
  · exact zY89 l hjl hl
theorem zY91 (l : Nat) (hjl : 11 < l) (hl : l < 20) :
    rawD witness recipe0 8 11 l ≤ D stage1 8 11 l := by
  interval_cases l <;> decide +kernel
theorem zY92 (l : Nat) (hjl : 11 < l) (hl : l < 20) :
    rawD witness recipe0 9 11 l ≤ D stage1 9 11 l := by
  interval_cases l <;> decide +kernel
theorem zY93 (l : Nat) (hjl : 11 < l) (hl : l < 20) :
    rawD witness recipe0 10 11 l ≤ D stage1 10 11 l := by
  interval_cases l <;> decide +kernel
theorem zY94 (l : Nat) (hjl : 11 < l) (hl : l < 20) :
    rawD witness recipe0 11 11 l ≤ D stage1 11 11 l := by
  interval_cases l <;> decide +kernel
theorem zY95 (i l : Nat)
    (hi : 8 ≤ i) (hij : i ≤ 11) (hjl : 11 < l) (hl : l < 20) :
    rawD witness recipe0 i 11 l ≤ D stage1 i 11 l := by
  interval_cases i
  · exact zY91 l hjl hl
  · exact zY92 l hjl hl
  · exact zY93 l hjl hl
  · exact zY94 l hjl hl
theorem zY96 (l : Nat) (hjl : 12 < l) (hl : l < 20) :
    rawD witness recipe0 8 12 l ≤ D stage1 8 12 l := by
  interval_cases l <;> decide +kernel
theorem zY97 (l : Nat) (hjl : 12 < l) (hl : l < 20) :
    rawD witness recipe0 9 12 l ≤ D stage1 9 12 l := by
  interval_cases l <;> decide +kernel
theorem zY98 (l : Nat) (hjl : 12 < l) (hl : l < 20) :
    rawD witness recipe0 10 12 l ≤ D stage1 10 12 l := by
  interval_cases l <;> decide +kernel
theorem zY99 (l : Nat) (hjl : 12 < l) (hl : l < 20) :
    rawD witness recipe0 11 12 l ≤ D stage1 11 12 l := by
  interval_cases l <;> decide +kernel
theorem zY100 (l : Nat) (hjl : 12 < l) (hl : l < 20) :
    rawD witness recipe0 12 12 l ≤ D stage1 12 12 l := by
  interval_cases l <;> decide +kernel
theorem zY101 (i l : Nat)
    (hi : 8 ≤ i) (hij : i ≤ 12) (hjl : 12 < l) (hl : l < 20) :
    rawD witness recipe0 i 12 l ≤ D stage1 i 12 l := by
  interval_cases i
  · exact zY96 l hjl hl
  · exact zY97 l hjl hl
  · exact zY98 l hjl hl
  · exact zY99 l hjl hl
  · exact zY100 l hjl hl
theorem zY102 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawD witness recipe0 8 13 l ≤ D stage1 8 13 l := by
  interval_cases l <;> decide +kernel
theorem zY103 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawD witness recipe0 9 13 l ≤ D stage1 9 13 l := by
  interval_cases l <;> decide +kernel
theorem zY104 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawD witness recipe0 10 13 l ≤ D stage1 10 13 l := by
  interval_cases l <;> decide +kernel
theorem zY105 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawD witness recipe0 11 13 l ≤ D stage1 11 13 l := by
  interval_cases l <;> decide +kernel
theorem zY106 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawD witness recipe0 12 13 l ≤ D stage1 12 13 l := by
  interval_cases l <;> decide +kernel
theorem zY107 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawD witness recipe0 13 13 l ≤ D stage1 13 13 l := by
  interval_cases l <;> decide +kernel
theorem zY108 (i l : Nat)
    (hi : 8 ≤ i) (hij : i ≤ 13) (hjl : 13 < l) (hl : l < 20) :
    rawD witness recipe0 i 13 l ≤ D stage1 i 13 l := by
  interval_cases i
  · exact zY102 l hjl hl
  · exact zY103 l hjl hl
  · exact zY104 l hjl hl
  · exact zY105 l hjl hl
  · exact zY106 l hjl hl
  · exact zY107 l hjl hl
theorem zY109 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD witness recipe0 8 14 l ≤ D stage1 8 14 l := by
  interval_cases l <;> decide +kernel
theorem zY110 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD witness recipe0 9 14 l ≤ D stage1 9 14 l := by
  interval_cases l <;> decide +kernel
theorem zY111 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD witness recipe0 10 14 l ≤ D stage1 10 14 l := by
  interval_cases l <;> decide +kernel
theorem zY112 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD witness recipe0 11 14 l ≤ D stage1 11 14 l := by
  interval_cases l <;> decide +kernel
theorem zY113 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD witness recipe0 12 14 l ≤ D stage1 12 14 l := by
  interval_cases l <;> decide +kernel
theorem zY114 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD witness recipe0 13 14 l ≤ D stage1 13 14 l := by
  interval_cases l <;> decide +kernel
theorem zY115 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD witness recipe0 14 14 l ≤ D stage1 14 14 l := by
  interval_cases l <;> decide +kernel
theorem zY116 (i l : Nat)
    (hi : 8 ≤ i) (hij : i ≤ 14) (hjl : 14 < l) (hl : l < 20) :
    rawD witness recipe0 i 14 l ≤ D stage1 i 14 l := by
  interval_cases i
  · exact zY109 l hjl hl
  · exact zY110 l hjl hl
  · exact zY111 l hjl hl
  · exact zY112 l hjl hl
  · exact zY113 l hjl hl
  · exact zY114 l hjl hl
  · exact zY115 l hjl hl
theorem zY117 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD witness recipe0 8 15 l ≤ D stage1 8 15 l := by
  interval_cases l <;> decide +kernel
theorem zY118 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD witness recipe0 9 15 l ≤ D stage1 9 15 l := by
  interval_cases l <;> decide +kernel
theorem zY119 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD witness recipe0 10 15 l ≤ D stage1 10 15 l := by
  interval_cases l <;> decide +kernel
theorem zY120 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD witness recipe0 11 15 l ≤ D stage1 11 15 l := by
  interval_cases l <;> decide +kernel
theorem zY121 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD witness recipe0 12 15 l ≤ D stage1 12 15 l := by
  interval_cases l <;> decide +kernel
theorem zY122 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD witness recipe0 13 15 l ≤ D stage1 13 15 l := by
  interval_cases l <;> decide +kernel
theorem zY123 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD witness recipe0 14 15 l ≤ D stage1 14 15 l := by
  interval_cases l <;> decide +kernel
theorem zY124 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD witness recipe0 15 15 l ≤ D stage1 15 15 l := by
  interval_cases l <;> decide +kernel
theorem zY125 (i l : Nat)
    (hi : 8 ≤ i) (hij : i ≤ 15) (hjl : 15 < l) (hl : l < 20) :
    rawD witness recipe0 i 15 l ≤ D stage1 i 15 l := by
  interval_cases i
  · exact zY117 l hjl hl
  · exact zY118 l hjl hl
  · exact zY119 l hjl hl
  · exact zY120 l hjl hl
  · exact zY121 l hjl hl
  · exact zY122 l hjl hl
  · exact zY123 l hjl hl
  · exact zY124 l hjl hl
theorem zY126 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD witness recipe0 8 16 l ≤ D stage1 8 16 l := by
  interval_cases l <;> decide +kernel
theorem zY127 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD witness recipe0 9 16 l ≤ D stage1 9 16 l := by
  interval_cases l <;> decide +kernel
theorem zY128 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD witness recipe0 10 16 l ≤ D stage1 10 16 l := by
  interval_cases l <;> decide +kernel
theorem zY129 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD witness recipe0 11 16 l ≤ D stage1 11 16 l := by
  interval_cases l <;> decide +kernel
theorem zY130 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD witness recipe0 12 16 l ≤ D stage1 12 16 l := by
  interval_cases l <;> decide +kernel
theorem zY131 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD witness recipe0 13 16 l ≤ D stage1 13 16 l := by
  interval_cases l <;> decide +kernel
theorem zY132 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD witness recipe0 14 16 l ≤ D stage1 14 16 l := by
  interval_cases l <;> decide +kernel
theorem zY133 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD witness recipe0 15 16 l ≤ D stage1 15 16 l := by
  interval_cases l <;> decide +kernel
theorem zY134 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD witness recipe0 16 16 l ≤ D stage1 16 16 l := by
  interval_cases l <;> decide +kernel
theorem zY135 (i l : Nat)
    (hi : 8 ≤ i) (hij : i ≤ 16) (hjl : 16 < l) (hl : l < 20) :
    rawD witness recipe0 i 16 l ≤ D stage1 i 16 l := by
  interval_cases i
  · exact zY126 l hjl hl
  · exact zY127 l hjl hl
  · exact zY128 l hjl hl
  · exact zY129 l hjl hl
  · exact zY130 l hjl hl
  · exact zY131 l hjl hl
  · exact zY132 l hjl hl
  · exact zY133 l hjl hl
  · exact zY134 l hjl hl
theorem zY136 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD witness recipe0 8 17 l ≤ D stage1 8 17 l := by
  interval_cases l <;> decide +kernel
theorem zY137 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD witness recipe0 9 17 l ≤ D stage1 9 17 l := by
  interval_cases l <;> decide +kernel
theorem zY138 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD witness recipe0 10 17 l ≤ D stage1 10 17 l := by
  interval_cases l <;> decide +kernel
theorem zY139 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD witness recipe0 11 17 l ≤ D stage1 11 17 l := by
  interval_cases l <;> decide +kernel
theorem zY140 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD witness recipe0 12 17 l ≤ D stage1 12 17 l := by
  interval_cases l <;> decide +kernel
theorem zY141 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD witness recipe0 13 17 l ≤ D stage1 13 17 l := by
  interval_cases l <;> decide +kernel
theorem zY142 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD witness recipe0 14 17 l ≤ D stage1 14 17 l := by
  interval_cases l <;> decide +kernel
theorem zY143 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD witness recipe0 15 17 l ≤ D stage1 15 17 l := by
  interval_cases l <;> decide +kernel
theorem zY144 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD witness recipe0 16 17 l ≤ D stage1 16 17 l := by
  interval_cases l <;> decide +kernel
theorem zY145 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD witness recipe0 17 17 l ≤ D stage1 17 17 l := by
  interval_cases l <;> decide +kernel
theorem zY146 (i l : Nat)
    (hi : 8 ≤ i) (hij : i ≤ 17) (hjl : 17 < l) (hl : l < 20) :
    rawD witness recipe0 i 17 l ≤ D stage1 i 17 l := by
  interval_cases i
  · exact zY136 l hjl hl
  · exact zY137 l hjl hl
  · exact zY138 l hjl hl
  · exact zY139 l hjl hl
  · exact zY140 l hjl hl
  · exact zY141 l hjl hl
  · exact zY142 l hjl hl
  · exact zY143 l hjl hl
  · exact zY144 l hjl hl
  · exact zY145 l hjl hl
theorem zY147 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD witness recipe0 8 18 l ≤ D stage1 8 18 l := by
  interval_cases l <;> decide +kernel
theorem zY148 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD witness recipe0 9 18 l ≤ D stage1 9 18 l := by
  interval_cases l <;> decide +kernel
theorem zY149 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD witness recipe0 10 18 l ≤ D stage1 10 18 l := by
  interval_cases l <;> decide +kernel
theorem zY150 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD witness recipe0 11 18 l ≤ D stage1 11 18 l := by
  interval_cases l <;> decide +kernel
theorem zY151 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD witness recipe0 12 18 l ≤ D stage1 12 18 l := by
  interval_cases l <;> decide +kernel
theorem zY152 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD witness recipe0 13 18 l ≤ D stage1 13 18 l := by
  interval_cases l <;> decide +kernel
theorem zY153 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD witness recipe0 14 18 l ≤ D stage1 14 18 l := by
  interval_cases l <;> decide +kernel
theorem zY154 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD witness recipe0 15 18 l ≤ D stage1 15 18 l := by
  interval_cases l <;> decide +kernel
theorem zY155 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD witness recipe0 16 18 l ≤ D stage1 16 18 l := by
  interval_cases l <;> decide +kernel
theorem zY156 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD witness recipe0 17 18 l ≤ D stage1 17 18 l := by
  interval_cases l <;> decide +kernel
theorem zY157 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD witness recipe0 18 18 l ≤ D stage1 18 18 l := by
  interval_cases l <;> decide +kernel
theorem zY158 (i l : Nat)
    (hi : 8 ≤ i) (hij : i ≤ 18) (hjl : 18 < l) (hl : l < 20) :
    rawD witness recipe0 i 18 l ≤ D stage1 i 18 l := by
  interval_cases i
  · exact zY147 l hjl hl
  · exact zY148 l hjl hl
  · exact zY149 l hjl hl
  · exact zY150 l hjl hl
  · exact zY151 l hjl hl
  · exact zY152 l hjl hl
  · exact zY153 l hjl hl
  · exact zY154 l hjl hl
  · exact zY155 l hjl hl
  · exact zY156 l hjl hl
  · exact zY157 l hjl hl

end ZP
end z125

section z126

namespace ZP

theorem rawD_eq_sum_of_nonzero {v : Profile} {r : Recipe} {i j l : Nat}
    (h : (r[i]?.getD default).tol ≠ 0) :
    rawD v r i j l = rawM v r i j + rawP v r j l := by
  cases hi : r[i]?.getD default
  cases hj : r[j]?.getD default
  cases hk : r[j+1]?.getD default
  cases hl : r[l]?.getD default
  simp only [hi] at h
  simp [rawD,hi,hj,hk,hl,h]

end ZP
end z126

section z127
namespace ZP
set_option maxHeartbeats 3000000

theorem zY159 (i j l : Nat) (hij : i ≤ j) (hjl : j < l) (hl : l < 20) :
    rawD witness recipe0 i j l ≤ D stage1 i j l := by
  by_cases hi : i < 8
  · have hqi := nonzero_tolerance_0 ⟨i,hi⟩
    rw [rawD_eq_sum_of_nonzero hqi]
    rw [nonzero_d_sum_0 ⟨i,hi⟩ ⟨j,by omega⟩ ⟨l,hl⟩ hij hjl]
    exact Nat.add_le_add (zY61 i j hij (by omega))
      (zY81 j l hjl hl)
  · have hi' : 8 ≤ i := by omega
    have hj : 8 ≤ j := by omega
    have hj' : j < 19 := by omega
    interval_cases j
    · exact zY83 i l hi' hij hjl hl
    · exact zY86 i l hi' hij hjl hl
    · exact zY90 i l hi' hij hjl hl
    · exact zY95 i l hi' hij hjl hl
    · exact zY101 i l hi' hij hjl hl
    · exact zY108 i l hi' hij hjl hl
    · exact zY116 i l hi' hij hjl hl
    · exact zY125 i l hi' hij hjl hl
    · exact zY135 i l hi' hij hjl hl
    · exact zY146 i l hi' hij hjl hl
    · exact zY158 i l hi' hij hjl hl

theorem transition0 : TransitionCertificate witness recipe0 stage1 where
  a i j hij := zY20 i.val j.val hij j.isLt
  b i j hij := zY41 i.val j.val hij j.isLt
  m i j hij hn := zY61 i.val j.val hij (by omega)
  p j l hjl := zY81 j.val l.val hjl l.isLt
  d i j l hij hjl := zY159 i.val j.val l.val hij hjl l.isLt
end ZP
end z127

section z233

noncomputable section
open scoped Classical
open OAI.Paper320 ZT
namespace ZP

theorem checked_period : PeriodCertificate :=
  ⟨transition0,_root_.Paley11987Verified.CompactFiniteProfile11987.transition1,_root_.Paley11987Verified.CompactFiniteProfile11987.transition2,_root_.Paley11987Verified.CompactFiniteProfile11987.transition3⟩

theorem actual_seeds_of_label (T : Tournament 11987)
    (label : Fin 11987 → Fin 11987 → Fin 2) (hCaps : LabelCaps T label)
    (hd : ∀ v, (Finset.univ.filter (T.Adj v)).card = 5993) : ActualSeedStatement :=
  _root_.Paley11987Verified.CompactFiniteProfile11987.actual_seeds_of_label_and_certificate T label hCaps hd checked_period

end ZP
end
end z233

section z234

noncomputable section

namespace SensitivityCampaign
open OAI.Paper320 ZT ZP

theorem _root_.solution : ZP.ActualSeedStatement := by
  obtain ⟨label,hlabel⟩ := _root_.Paley11987Verified.CompactBooleanTransfer.selected_exists_labelCaps
  exact ZP.actual_seeds_of_label
    ZT.selectedTournament label hlabel
    ZT.selected_outdegree







end SensitivityCampaign


end
end z234
