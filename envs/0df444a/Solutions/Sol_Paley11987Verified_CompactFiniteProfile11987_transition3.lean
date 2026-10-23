-- Prove2me | solution 1 for Paley11987Verified.CompactFiniteProfile11987.transition3
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-23T05:49:12.820012+00:00
-- url     : https://prove2.me/submissions/2ef0af55-26e8-4f2c-8873-f3e1aa708dd8

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
import Definitions.Def_Paley11987Support_053
import Definitions.Def_Paley11987Support_054
import Definitions.Def_Paley11987Support_055

set_option autoImplicit false
set_option Elab.async false
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

theorem cases_6_0_eq : cases 6 0 = cases_6_0 := by decide +kernel

theorem cases_6_1_eq : cases 6 15 = cases_6_1 := by decide +kernel

theorem cases_7_0_eq : cases 7 0 = cases_7_0 := by decide +kernel

theorem cases_7_1_eq : cases 7 17 = cases_7_1 := by decide +kernel



theorem cases_8_1_eq : cases 8 19 = cases_8_1 := by decide +kernel
end ZP
end z87

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

section z199
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX136 : rawA stage3 recipe3 0 0 ≤ A stage4 0 0 := by
  change maximum ((cases 8 19).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1694765706419682802 142311673061587469545 142311673061587469545)) ≤ 9499340661569213006496
  rw [cases_8_1_eq]
  decide +kernel
theorem zX137 : rawA stage3 recipe3 0 1 ≤ A stage4 0 1 := by
  change maximum ((cases 7 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1694765706419682802 142311673061587469545 142311673061587469545)) ≤ 115244068036538430536
  rw [cases_7_0_eq]
  decide +kernel
theorem zX138 : rawA stage3 recipe3 0 2 ≤ A stage4 0 2 := by
  change maximum ((cases 6 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 142311673061587469545 141841998928197303497)) ≤ 103309205968484467829
  rw [cases_6_0_eq]
  decide +kernel
theorem zX139 : rawA stage3 recipe3 0 3 ≤ A stage4 0 3 := by
  change maximum ((cases 5 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 142311673061587469545 141841998928197303497)) ≤ 94841238266149675384
  rw [cases_5_0_eq]
  decide +kernel
theorem zX140 : rawA stage3 recipe3 0 4 ≤ A stage4 0 4 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 142311673061587469545 141841998928197303497)) ≤ 82986083482880965961
  rw [cases_4_0_eq]
  decide +kernel
theorem zX141 : rawA stage3 recipe3 0 5 ≤ A stage4 0 5 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 10 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 124541985698095207659 124072311564705041611)) ≤ 82986083482880965961
  rw [cases_4_0_eq]
  decide +kernel
theorem zX142 : rawA stage3 recipe3 0 6 ≤ A stage4 0 6 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 10 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 124541985698095207659 124072311564705041611)) ≤ 72824522240079215027
  rw [cases_3_0_eq]
  decide +kernel
theorem zX143 : rawA stage3 recipe3 0 7 ≤ A stage4 0 7 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 10 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 124541985698095207659 124072311564705041611)) ≤ 62662960997277464093
  rw [cases_2_0_eq]
  decide +kernel
theorem zX144 : rawA stage3 recipe3 0 8 ≤ A stage4 0 8 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 10 then 0 else
      c.u*116880497462914519+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 116880497462914519 124541985698095207659 3701756409344116469)) ≤ 4324578406127837203
  rw [cases_2_0_eq]
  decide +kernel
theorem zX145 : rawA stage3 recipe3 0 9 ≤ A stage4 0 9 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 10 then 0 else
      c.u*116880497462914519+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 116880497462914519 124541985698095207659 3701756409344116469)) ≤ 3506414923887435570
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z199

section z200
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX146 : rawA stage3 recipe3 1 1 ≤ A stage4 1 1 := by
  change maximum ((cases 7 17).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1694765706419682802 142311673061587469545 142311673061587469545)) ≤ 7927133195066072110293
  rw [cases_7_1_eq]
  decide +kernel
theorem zX147 : rawA stage3 recipe3 1 2 ≤ A stage4 1 2 := by
  change maximum ((cases 6 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 142311673061587469545 141841998928197303497)) ≤ 103309205968484467829
  rw [cases_6_0_eq]
  decide +kernel
theorem zX148 : rawA stage3 recipe3 1 3 ≤ A stage4 1 3 := by
  change maximum ((cases 5 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 142311673061587469545 141841998928197303497)) ≤ 94841238266149675384
  rw [cases_5_0_eq]
  decide +kernel
theorem zX149 : rawA stage3 recipe3 1 4 ≤ A stage4 1 4 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 142311673061587469545 141841998928197303497)) ≤ 82986083482880965961
  rw [cases_4_0_eq]
  decide +kernel
theorem zX150 : rawA stage3 recipe3 1 5 ≤ A stage4 1 5 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 10 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 124541985698095207659 124072311564705041611)) ≤ 82986083482880965961
  rw [cases_4_0_eq]
  decide +kernel
end ZP
end z200

section z201
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX151 : rawA stage3 recipe3 1 6 ≤ A stage4 1 6 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 10 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 124541985698095207659 124072311564705041611)) ≤ 72824522240079215027
  rw [cases_3_0_eq]
  decide +kernel
theorem zX152 : rawA stage3 recipe3 1 7 ≤ A stage4 1 7 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 10 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 124541985698095207659 124072311564705041611)) ≤ 62662960997277464093
  rw [cases_2_0_eq]
  decide +kernel
theorem zX153 : rawA stage3 recipe3 1 8 ≤ A stage4 1 8 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 10 then 0 else
      c.u*116880497462914519+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 116880497462914519 124541985698095207659 3701756409344116469)) ≤ 4324578406127837203
  rw [cases_2_0_eq]
  decide +kernel
theorem zX154 : rawA stage3 recipe3 1 9 ≤ A stage4 1 9 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 10 then 0 else
      c.u*116880497462914519+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 116880497462914519 124541985698095207659 3701756409344116469)) ≤ 3506414923887435570
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z201

section z202
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX155 : rawA stage3 recipe3 2 2 ≤ A stage4 2 2 := by
  change maximum ((cases 6 15).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 142311673061587469545 141841998928197303497)) ≤ 6485331611015161940578
  rw [cases_6_1_eq]
  decide +kernel
theorem zX156 : rawA stage3 recipe3 2 3 ≤ A stage4 2 3 := by
  change maximum ((cases 5 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 142311673061587469545 141841998928197303497)) ≤ 94841238266149675384
  rw [cases_5_0_eq]
  decide +kernel
theorem zX157 : rawA stage3 recipe3 2 4 ≤ A stage4 2 4 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 142311673061587469545 141841998928197303497)) ≤ 82986083482880965961
  rw [cases_4_0_eq]
  decide +kernel
theorem zX158 : rawA stage3 recipe3 2 5 ≤ A stage4 2 5 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 124541985698095207659 124072311564705041611)) ≤ 82986083482880965961
  rw [cases_4_0_eq]
  decide +kernel
theorem zX159 : rawA stage3 recipe3 2 6 ≤ A stage4 2 6 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 124541985698095207659 124072311564705041611)) ≤ 72824522240079215027
  rw [cases_3_0_eq]
  decide +kernel
theorem zX160 : rawA stage3 recipe3 2 7 ≤ A stage4 2 7 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 124541985698095207659 124072311564705041611)) ≤ 62662960997277464093
  rw [cases_2_0_eq]
  decide +kernel
theorem zX161 : rawA stage3 recipe3 2 8 ≤ A stage4 2 8 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*116880497462914519+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 116880497462914519 124541985698095207659 3701756409344116469)) ≤ 4324578406127837203
  rw [cases_2_0_eq]
  decide +kernel
theorem zX162 : rawA stage3 recipe3 2 9 ≤ A stage4 2 9 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*116880497462914519+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 116880497462914519 124541985698095207659 3701756409344116469)) ≤ 3506414923887435570
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z202

section z203
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX163 : rawA stage3 recipe3 3 3 ≤ A stage4 3 3 := by
  change maximum ((cases 5 13).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 142311673061587469545 141841998928197303497)) ≤ 5198691527565787212813
  rw [cases_5_1_eq]
  decide +kernel
theorem zX164 : rawA stage3 recipe3 3 4 ≤ A stage4 3 4 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 142311673061587469545 141841998928197303497)) ≤ 82986083482880965961
  rw [cases_4_0_eq]
  decide +kernel
theorem zX165 : rawA stage3 recipe3 3 5 ≤ A stage4 3 5 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 124541985698095207659 124072311564705041611)) ≤ 82986083482880965961
  rw [cases_4_0_eq]
  decide +kernel
theorem zX166 : rawA stage3 recipe3 3 6 ≤ A stage4 3 6 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 124541985698095207659 124072311564705041611)) ≤ 72824522240079215027
  rw [cases_3_0_eq]
  decide +kernel
theorem zX167 : rawA stage3 recipe3 3 7 ≤ A stage4 3 7 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 124541985698095207659 124072311564705041611)) ≤ 62662960997277464093
  rw [cases_2_0_eq]
  decide +kernel
theorem zX168 : rawA stage3 recipe3 3 8 ≤ A stage4 3 8 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*116880497462914519+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 116880497462914519 124541985698095207659 3701756409344116469)) ≤ 4324578406127837203
  rw [cases_2_0_eq]
  decide +kernel
end ZP
end z203

section z204
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX169 : rawA stage3 recipe3 3 9 ≤ A stage4 3 9 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*116880497462914519+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 116880497462914519 124541985698095207659 3701756409344116469)) ≤ 3506414923887435570
  rw [cases_1_0_eq]
  decide +kernel
theorem zX170 : rawA stage3 recipe3 4 4 ≤ A stage4 4 4 := by
  change maximum ((cases 4 11).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 142311673061587469545 141841998928197303497)) ≤ 4050975930097066037615
  rw [cases_4_1_eq]
  decide +kernel
end ZP
end z204

section z205
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX171 : rawA stage3 recipe3 4 5 ≤ A stage4 4 5 := by
  change maximum ((cases 4 11).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 124541985698095207659 124072311564705041611)) ≤ 3553424683919282704807
  rw [cases_4_1_eq]
  decide +kernel
theorem zX172 : rawA stage3 recipe3 4 6 ≤ A stage4 4 6 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 124541985698095207659 124072311564705041611)) ≤ 72824522240079215027
  rw [cases_3_0_eq]
  decide +kernel
theorem zX173 : rawA stage3 recipe3 4 7 ≤ A stage4 4 7 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 124541985698095207659 124072311564705041611)) ≤ 62662960997277464093
  rw [cases_2_0_eq]
  decide +kernel
theorem zX174 : rawA stage3 recipe3 4 8 ≤ A stage4 4 8 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*116880497462914519+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 116880497462914519 124541985698095207659 3701756409344116469)) ≤ 4324578406127837203
  rw [cases_2_0_eq]
  decide +kernel
theorem zX175 : rawA stage3 recipe3 4 9 ≤ A stage4 4 9 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*116880497462914519+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 116880497462914519 124541985698095207659 3701756409344116469)) ≤ 3506414923887435570
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z205

section z206
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX176 : rawA stage3 recipe3 5 5 ≤ A stage4 5 5 := by
  change maximum ((cases 4 11).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 133367358910513352379 124072311564705041611)) ≤ 3676979908893136730887
  rw [cases_4_1_eq]
  decide +kernel
theorem zX177 : rawA stage3 recipe3 5 6 ≤ A stage4 5 6 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 133367358910513352379 124072311564705041611)) ≤ 72824522240079215027
  rw [cases_3_0_eq]
  decide +kernel
theorem zX178 : rawA stage3 recipe3 5 7 ≤ A stage4 5 7 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 133367358910513352379 124072311564705041611)) ≤ 62662960997277464093
  rw [cases_2_0_eq]
  decide +kernel
theorem zX179 : rawA stage3 recipe3 5 8 ≤ A stage4 5 8 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*116880497462914519+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 116880497462914519 133367358910513352379 3701756409344116469)) ≤ 4324578406127837203
  rw [cases_2_0_eq]
  decide +kernel
theorem zX180 : rawA stage3 recipe3 5 9 ≤ A stage4 5 9 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*116880497462914519+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 116880497462914519 133367358910513352379 3701756409344116469)) ≤ 3506414923887435570
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z206

section z207
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX181 : rawA stage3 recipe3 6 6 ≤ A stage4 6 6 := by
  change maximum ((cases 3 9).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 133367358910513352379 124072311564705041611)) ≤ 2738288181644622466924
  rw [cases_3_1_eq]
  decide +kernel
theorem zX182 : rawA stage3 recipe3 6 7 ≤ A stage4 6 7 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 133367358910513352379 124072311564705041611)) ≤ 62662960997277464093
  rw [cases_2_0_eq]
  decide +kernel
theorem zX183 : rawA stage3 recipe3 6 8 ≤ A stage4 6 8 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*116880497462914519+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 116880497462914519 133367358910513352379 3701756409344116469)) ≤ 4324578406127837203
  rw [cases_2_0_eq]
  decide +kernel
theorem zX184 : rawA stage3 recipe3 6 9 ≤ A stage4 6 9 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*116880497462914519+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 116880497462914519 133367358910513352379 3701756409344116469)) ≤ 3506414923887435570
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z207

section z208
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX185 : rawA stage3 recipe3 7 7 ≤ A stage4 7 7 := by
  change maximum ((cases 2 7).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*1693593540466958489+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1693593540466958489 133367358910513352379 124072311564705041611)) ≤ 1963448497035026808142
  rw [cases_2_1_eq]
  decide +kernel
theorem zX186 : rawA stage3 recipe3 7 8 ≤ A stage4 7 8 := by
  change maximum ((cases 2 7).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*116880497462914519+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 116880497462914519 133367358910513352379 3701756409344116469)) ≤ 825687345848106419620
  rw [cases_2_1_eq]
  decide +kernel
theorem zX187 : rawA stage3 recipe3 7 9 ≤ A stage4 7 9 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 11 then 0 else
      c.u*116880497462914519+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 116880497462914519 133367358910513352379 3701756409344116469)) ≤ 3506414923887435570
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z208

section z209
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX188 : rawA stage3 recipe3 8 8 ≤ A stage4 8 8 := by
  change maximum ((cases 2 7).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 12 then 0 else
      c.u*1626712276215111111+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 116880497462914519 133367358910513352379 3701756409344116469)) ≤ 825687345848106419620
  rw [cases_2_1_eq]
  decide +kernel
theorem zX189 : rawA stage3 recipe3 8 9 ≤ A stage4 8 9 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 12 then 0 else
      c.u*1626712276215111111+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 116880497462914519 133367358910513352379 3701756409344116469)) ≤ 7568388270292367270
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z209

section z210
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX190 : rawA stage3 recipe3 9 9 ≤ A stage4 9 9 := by
  change maximum ((cases 1 5).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 12 then 0 else
      c.u*1626712276215111111+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 116880497462914519 133367358910513352379 3701756409344116469)) ≤ 413895597401219440481
  rw [cases_1_1_eq]
  decide +kernel
end ZP
end z210

section z231
namespace ZP
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
theorem zY445 (j : Nat) (hij : 0 ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 0 j ≤ A stage4 0 j := by
  interval_cases j
  · exact zX136
  · exact zX137
  · exact zX138
  · exact zX139
  · exact zX140
  · exact zX141
  · exact zX142
  · exact zX143
  · exact zX144
  · exact zX145
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
theorem zY446 (j : Nat) (hij : 1 ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 1 j ≤ A stage4 1 j := by
  interval_cases j
  · exact zX146
  · exact zX147
  · exact zX148
  · exact zX149
  · exact zX150
  · exact zX151
  · exact zX152
  · exact zX153
  · exact zX154
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
theorem zY447 (j : Nat) (hij : 2 ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 2 j ≤ A stage4 2 j := by
  interval_cases j
  · exact zX155
  · exact zX156
  · exact zX157
  · exact zX158
  · exact zX159
  · exact zX160
  · exact zX161
  · exact zX162
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
theorem zY448 (j : Nat) (hij : 3 ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 3 j ≤ A stage4 3 j := by
  interval_cases j
  · exact zX163
  · exact zX164
  · exact zX165
  · exact zX166
  · exact zX167
  · exact zX168
  · exact zX169
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
theorem zY449 (j : Nat) (hij : 4 ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 4 j ≤ A stage4 4 j := by
  interval_cases j
  · exact zX170
  · exact zX171
  · exact zX172
  · exact zX173
  · exact zX174
  · exact zX175
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
theorem zY450 (j : Nat) (hij : 5 ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 5 j ≤ A stage4 5 j := by
  interval_cases j
  · exact zX176
  · exact zX177
  · exact zX178
  · exact zX179
  · exact zX180
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
theorem zY451 (j : Nat) (hij : 6 ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 6 j ≤ A stage4 6 j := by
  interval_cases j
  · exact zX181
  · exact zX182
  · exact zX183
  · exact zX184
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
theorem zY452 (j : Nat) (hij : 7 ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 7 j ≤ A stage4 7 j := by
  interval_cases j
  · exact zX185
  · exact zX186
  · exact zX187
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
theorem zY453 (j : Nat) (hij : 8 ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 8 j ≤ A stage4 8 j := by
  interval_cases j
  · exact zX188
  · exact zX189
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
theorem zY454 (j : Nat) (hij : 9 ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 9 j ≤ A stage4 9 j := by
  interval_cases j
  · exact zX190
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
theorem zY455 (j : Nat) (hij : 10 ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 10 j ≤ A stage4 10 j := by
  interval_cases j <;> decide +kernel
theorem zY456 (j : Nat) (hij : 11 ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 11 j ≤ A stage4 11 j := by
  interval_cases j <;> decide +kernel
theorem zY457 (j : Nat) (hij : 12 ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 12 j ≤ A stage4 12 j := by
  interval_cases j <;> decide +kernel
theorem zY458 (j : Nat) (hij : 13 ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 13 j ≤ A stage4 13 j := by
  interval_cases j <;> decide +kernel
theorem zY459 (j : Nat) (hij : 14 ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 14 j ≤ A stage4 14 j := by
  interval_cases j <;> decide +kernel
theorem zY460 (j : Nat) (hij : 15 ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 15 j ≤ A stage4 15 j := by
  interval_cases j <;> decide +kernel
theorem zY461 (j : Nat) (hij : 16 ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 16 j ≤ A stage4 16 j := by
  interval_cases j <;> decide +kernel
theorem zY462 (j : Nat) (hij : 17 ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 17 j ≤ A stage4 17 j := by
  interval_cases j <;> decide +kernel
theorem zY463 (j : Nat) (hij : 18 ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 18 j ≤ A stage4 18 j := by
  interval_cases j <;> decide +kernel
theorem zY464 (j : Nat) (hij : 19 ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 19 j ≤ A stage4 19 j := by
  interval_cases j <;> decide +kernel
theorem zY465 (i j : Nat) (hij : i ≤ j) (hj : j < 20) :
    rawA stage3 recipe3 i j ≤ A stage4 i j := by
  have hi : i < 20 := Nat.lt_of_le_of_lt hij hj
  interval_cases i
  · exact zY445 j hij hj
  · exact zY446 j hij hj
  · exact zY447 j hij hj
  · exact zY448 j hij hj
  · exact zY449 j hij hj
  · exact zY450 j hij hj
  · exact zY451 j hij hj
  · exact zY452 j hij hj
  · exact zY453 j hij hj
  · exact zY454 j hij hj
  · exact zY455 j hij hj
  · exact zY456 j hij hj
  · exact zY457 j hij hj
  · exact zY458 j hij hj
  · exact zY459 j hij hj
  · exact zY460 j hij hj
  · exact zY461 j hij hj
  · exact zY462 j hij hj
  · exact zY463 j hij hj
  · exact zY464 j hij hj
theorem zY466 (j : Nat) (hij : 0 ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 0 j ≤ B stage4 0 j := by
  interval_cases j <;> decide +kernel
theorem zY467 (j : Nat) (hij : 1 ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 1 j ≤ B stage4 1 j := by
  interval_cases j <;> decide +kernel
theorem zY468 (j : Nat) (hij : 2 ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 2 j ≤ B stage4 2 j := by
  interval_cases j <;> decide +kernel
theorem zY469 (j : Nat) (hij : 3 ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 3 j ≤ B stage4 3 j := by
  interval_cases j <;> decide +kernel
theorem zY470 (j : Nat) (hij : 4 ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 4 j ≤ B stage4 4 j := by
  interval_cases j <;> decide +kernel
theorem zY471 (j : Nat) (hij : 5 ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 5 j ≤ B stage4 5 j := by
  interval_cases j <;> decide +kernel
theorem zY472 (j : Nat) (hij : 6 ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 6 j ≤ B stage4 6 j := by
  interval_cases j <;> decide +kernel
theorem zY473 (j : Nat) (hij : 7 ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 7 j ≤ B stage4 7 j := by
  interval_cases j <;> decide +kernel
theorem zY474 (j : Nat) (hij : 8 ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 8 j ≤ B stage4 8 j := by
  interval_cases j <;> decide +kernel
theorem zY475 (j : Nat) (hij : 9 ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 9 j ≤ B stage4 9 j := by
  interval_cases j <;> decide +kernel
theorem zY476 (j : Nat) (hij : 10 ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 10 j ≤ B stage4 10 j := by
  interval_cases j <;> decide +kernel
theorem zY477 (j : Nat) (hij : 11 ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 11 j ≤ B stage4 11 j := by
  interval_cases j <;> decide +kernel
theorem zY478 (j : Nat) (hij : 12 ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 12 j ≤ B stage4 12 j := by
  interval_cases j <;> decide +kernel
theorem zY479 (j : Nat) (hij : 13 ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 13 j ≤ B stage4 13 j := by
  interval_cases j <;> decide +kernel
theorem zY480 (j : Nat) (hij : 14 ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 14 j ≤ B stage4 14 j := by
  interval_cases j <;> decide +kernel
theorem zY481 (j : Nat) (hij : 15 ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 15 j ≤ B stage4 15 j := by
  interval_cases j <;> decide +kernel
theorem zY482 (j : Nat) (hij : 16 ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 16 j ≤ B stage4 16 j := by
  interval_cases j <;> decide +kernel
theorem zY483 (j : Nat) (hij : 17 ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 17 j ≤ B stage4 17 j := by
  interval_cases j <;> decide +kernel
theorem zY484 (j : Nat) (hij : 18 ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 18 j ≤ B stage4 18 j := by
  interval_cases j <;> decide +kernel
theorem zY485 (j : Nat) (hij : 19 ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 19 j ≤ B stage4 19 j := by
  interval_cases j <;> decide +kernel
theorem zY486 (i j : Nat) (hij : i ≤ j) (hj : j < 20) :
    rawB stage3 recipe3 i j ≤ B stage4 i j := by
  have hi : i < 20 := Nat.lt_of_le_of_lt hij hj
  interval_cases i
  · exact zY466 j hij hj
  · exact zY467 j hij hj
  · exact zY468 j hij hj
  · exact zY469 j hij hj
  · exact zY470 j hij hj
  · exact zY471 j hij hj
  · exact zY472 j hij hj
  · exact zY473 j hij hj
  · exact zY474 j hij hj
  · exact zY475 j hij hj
  · exact zY476 j hij hj
  · exact zY477 j hij hj
  · exact zY478 j hij hj
  · exact zY479 j hij hj
  · exact zY480 j hij hj
  · exact zY481 j hij hj
  · exact zY482 j hij hj
  · exact zY483 j hij hj
  · exact zY484 j hij hj
  · exact zY485 j hij hj
theorem zY487 (j : Nat) (hij : 0 ≤ j) (hj : j < 19) :
    rawM stage3 recipe3 0 j ≤ M stage4 0 j := by
  interval_cases j <;> decide +kernel
theorem zY488 (j : Nat) (hij : 1 ≤ j) (hj : j < 19) :
    rawM stage3 recipe3 1 j ≤ M stage4 1 j := by
  interval_cases j <;> decide +kernel
theorem zY489 (j : Nat) (hij : 2 ≤ j) (hj : j < 19) :
    rawM stage3 recipe3 2 j ≤ M stage4 2 j := by
  interval_cases j <;> decide +kernel
theorem zY490 (j : Nat) (hij : 3 ≤ j) (hj : j < 19) :
    rawM stage3 recipe3 3 j ≤ M stage4 3 j := by
  interval_cases j <;> decide +kernel
theorem zY491 (j : Nat) (hij : 4 ≤ j) (hj : j < 19) :
    rawM stage3 recipe3 4 j ≤ M stage4 4 j := by
  interval_cases j <;> decide +kernel
theorem zY492 (j : Nat) (hij : 5 ≤ j) (hj : j < 19) :
    rawM stage3 recipe3 5 j ≤ M stage4 5 j := by
  interval_cases j <;> decide +kernel
theorem zY493 (j : Nat) (hij : 6 ≤ j) (hj : j < 19) :
    rawM stage3 recipe3 6 j ≤ M stage4 6 j := by
  interval_cases j <;> decide +kernel
theorem zY494 (j : Nat) (hij : 7 ≤ j) (hj : j < 19) :
    rawM stage3 recipe3 7 j ≤ M stage4 7 j := by
  interval_cases j <;> decide +kernel
theorem zY495 (j : Nat) (hij : 8 ≤ j) (hj : j < 19) :
    rawM stage3 recipe3 8 j ≤ M stage4 8 j := by
  interval_cases j <;> decide +kernel
theorem zY496 (j : Nat) (hij : 9 ≤ j) (hj : j < 19) :
    rawM stage3 recipe3 9 j ≤ M stage4 9 j := by
  interval_cases j <;> decide +kernel
theorem zY497 (j : Nat) (hij : 10 ≤ j) (hj : j < 19) :
    rawM stage3 recipe3 10 j ≤ M stage4 10 j := by
  interval_cases j <;> decide +kernel
theorem zY498 (j : Nat) (hij : 11 ≤ j) (hj : j < 19) :
    rawM stage3 recipe3 11 j ≤ M stage4 11 j := by
  interval_cases j <;> decide +kernel
theorem zY499 (j : Nat) (hij : 12 ≤ j) (hj : j < 19) :
    rawM stage3 recipe3 12 j ≤ M stage4 12 j := by
  interval_cases j <;> decide +kernel
theorem zY500 (j : Nat) (hij : 13 ≤ j) (hj : j < 19) :
    rawM stage3 recipe3 13 j ≤ M stage4 13 j := by
  interval_cases j <;> decide +kernel
theorem zY501 (j : Nat) (hij : 14 ≤ j) (hj : j < 19) :
    rawM stage3 recipe3 14 j ≤ M stage4 14 j := by
  interval_cases j <;> decide +kernel
theorem zY502 (j : Nat) (hij : 15 ≤ j) (hj : j < 19) :
    rawM stage3 recipe3 15 j ≤ M stage4 15 j := by
  interval_cases j <;> decide +kernel
theorem zY503 (j : Nat) (hij : 16 ≤ j) (hj : j < 19) :
    rawM stage3 recipe3 16 j ≤ M stage4 16 j := by
  interval_cases j <;> decide +kernel
theorem zY504 (j : Nat) (hij : 17 ≤ j) (hj : j < 19) :
    rawM stage3 recipe3 17 j ≤ M stage4 17 j := by
  interval_cases j <;> decide +kernel
theorem zY505 (j : Nat) (hij : 18 ≤ j) (hj : j < 19) :
    rawM stage3 recipe3 18 j ≤ M stage4 18 j := by
  interval_cases j <;> decide +kernel
theorem zY506 (i j : Nat) (hij : i ≤ j) (hj : j < 19) :
    rawM stage3 recipe3 i j ≤ M stage4 i j := by
  have hi : i < 19 := Nat.lt_of_le_of_lt hij hj
  interval_cases i
  · exact zY487 j hij hj
  · exact zY488 j hij hj
  · exact zY489 j hij hj
  · exact zY490 j hij hj
  · exact zY491 j hij hj
  · exact zY492 j hij hj
  · exact zY493 j hij hj
  · exact zY494 j hij hj
  · exact zY495 j hij hj
  · exact zY496 j hij hj
  · exact zY497 j hij hj
  · exact zY498 j hij hj
  · exact zY499 j hij hj
  · exact zY500 j hij hj
  · exact zY501 j hij hj
  · exact zY502 j hij hj
  · exact zY503 j hij hj
  · exact zY504 j hij hj
  · exact zY505 j hij hj
theorem zY507 (l : Nat) (hjl : 0 < l) (hl : l < 20) :
    rawP stage3 recipe3 0 l ≤ P stage4 0 l := by
  interval_cases l
  · change rawA stage3 recipe3 1 1 ≤ A stage4 1 1
    exact zX146
  · change rawA stage3 recipe3 1 2 ≤ A stage4 1 2
    exact zX147
  · change rawA stage3 recipe3 1 3 ≤ A stage4 1 3
    exact zX148
  · change rawA stage3 recipe3 1 4 ≤ A stage4 1 4
    exact zX149
  · change rawA stage3 recipe3 1 5 ≤ A stage4 1 5
    exact zX150
  · change rawA stage3 recipe3 1 6 ≤ A stage4 1 6
    exact zX151
  · change rawA stage3 recipe3 1 7 ≤ A stage4 1 7
    exact zX152
  · change rawA stage3 recipe3 1 8 ≤ A stage4 1 8
    exact zX153
  · change rawA stage3 recipe3 1 9 ≤ A stage4 1 9
    exact zX154
  · change rawA stage3 recipe3 1 10 ≤ A stage4 1 10
    decide +kernel
  · change rawA stage3 recipe3 1 11 ≤ A stage4 1 11
    decide +kernel
  · change rawA stage3 recipe3 1 12 ≤ A stage4 1 12
    decide +kernel
  · change rawA stage3 recipe3 1 13 ≤ A stage4 1 13
    decide +kernel
  · change rawA stage3 recipe3 1 14 ≤ A stage4 1 14
    decide +kernel
  · change rawA stage3 recipe3 1 15 ≤ A stage4 1 15
    decide +kernel
  · change rawA stage3 recipe3 1 16 ≤ A stage4 1 16
    decide +kernel
  · change rawA stage3 recipe3 1 17 ≤ A stage4 1 17
    decide +kernel
  · change rawA stage3 recipe3 1 18 ≤ A stage4 1 18
    decide +kernel
  · change rawA stage3 recipe3 1 19 ≤ A stage4 1 19
    decide +kernel
theorem zY508 (l : Nat) (hjl : 1 < l) (hl : l < 20) :
    rawP stage3 recipe3 1 l ≤ P stage4 1 l := by
  interval_cases l
  · change rawA stage3 recipe3 2 2 ≤ A stage4 2 2
    exact zX155
  · change rawA stage3 recipe3 2 3 ≤ A stage4 2 3
    exact zX156
  · change rawA stage3 recipe3 2 4 ≤ A stage4 2 4
    exact zX157
  · change rawA stage3 recipe3 2 5 ≤ A stage4 2 5
    exact zX158
  · change rawA stage3 recipe3 2 6 ≤ A stage4 2 6
    exact zX159
  · change rawA stage3 recipe3 2 7 ≤ A stage4 2 7
    exact zX160
  · change rawA stage3 recipe3 2 8 ≤ A stage4 2 8
    exact zX161
  · change rawA stage3 recipe3 2 9 ≤ A stage4 2 9
    exact zX162
  · change rawA stage3 recipe3 2 10 ≤ A stage4 2 10
    decide +kernel
  · change rawA stage3 recipe3 2 11 ≤ A stage4 2 11
    decide +kernel
  · change rawA stage3 recipe3 2 12 ≤ A stage4 2 12
    decide +kernel
  · change rawA stage3 recipe3 2 13 ≤ A stage4 2 13
    decide +kernel
  · change rawA stage3 recipe3 2 14 ≤ A stage4 2 14
    decide +kernel
  · change rawA stage3 recipe3 2 15 ≤ A stage4 2 15
    decide +kernel
  · change rawA stage3 recipe3 2 16 ≤ A stage4 2 16
    decide +kernel
  · change rawA stage3 recipe3 2 17 ≤ A stage4 2 17
    decide +kernel
  · change rawA stage3 recipe3 2 18 ≤ A stage4 2 18
    decide +kernel
  · change rawA stage3 recipe3 2 19 ≤ A stage4 2 19
    decide +kernel
theorem zY509 (l : Nat) (hjl : 2 < l) (hl : l < 20) :
    rawP stage3 recipe3 2 l ≤ P stage4 2 l := by
  interval_cases l
  · change rawA stage3 recipe3 3 3 ≤ A stage4 3 3
    exact zX163
  · change rawA stage3 recipe3 3 4 ≤ A stage4 3 4
    exact zX164
  · change rawA stage3 recipe3 3 5 ≤ A stage4 3 5
    exact zX165
  · change rawA stage3 recipe3 3 6 ≤ A stage4 3 6
    exact zX166
  · change rawA stage3 recipe3 3 7 ≤ A stage4 3 7
    exact zX167
  · change rawA stage3 recipe3 3 8 ≤ A stage4 3 8
    exact zX168
  · change rawA stage3 recipe3 3 9 ≤ A stage4 3 9
    exact zX169
  · change rawA stage3 recipe3 3 10 ≤ A stage4 3 10
    decide +kernel
  · change rawA stage3 recipe3 3 11 ≤ A stage4 3 11
    decide +kernel
  · change rawA stage3 recipe3 3 12 ≤ A stage4 3 12
    decide +kernel
  · change rawA stage3 recipe3 3 13 ≤ A stage4 3 13
    decide +kernel
  · change rawA stage3 recipe3 3 14 ≤ A stage4 3 14
    decide +kernel
  · change rawA stage3 recipe3 3 15 ≤ A stage4 3 15
    decide +kernel
  · change rawA stage3 recipe3 3 16 ≤ A stage4 3 16
    decide +kernel
  · change rawA stage3 recipe3 3 17 ≤ A stage4 3 17
    decide +kernel
  · change rawA stage3 recipe3 3 18 ≤ A stage4 3 18
    decide +kernel
  · change rawA stage3 recipe3 3 19 ≤ A stage4 3 19
    decide +kernel
theorem zY510 (l : Nat) (hjl : 3 < l) (hl : l < 20) :
    rawP stage3 recipe3 3 l ≤ P stage4 3 l := by
  interval_cases l
  · change rawA stage3 recipe3 4 4 ≤ A stage4 4 4
    exact zX170
  · change rawA stage3 recipe3 4 5 ≤ A stage4 4 5
    exact zX171
  · change rawA stage3 recipe3 4 6 ≤ A stage4 4 6
    exact zX172
  · change rawA stage3 recipe3 4 7 ≤ A stage4 4 7
    exact zX173
  · change rawA stage3 recipe3 4 8 ≤ A stage4 4 8
    exact zX174
  · change rawA stage3 recipe3 4 9 ≤ A stage4 4 9
    exact zX175
  · change rawA stage3 recipe3 4 10 ≤ A stage4 4 10
    decide +kernel
  · change rawA stage3 recipe3 4 11 ≤ A stage4 4 11
    decide +kernel
  · change rawA stage3 recipe3 4 12 ≤ A stage4 4 12
    decide +kernel
  · change rawA stage3 recipe3 4 13 ≤ A stage4 4 13
    decide +kernel
  · change rawA stage3 recipe3 4 14 ≤ A stage4 4 14
    decide +kernel
  · change rawA stage3 recipe3 4 15 ≤ A stage4 4 15
    decide +kernel
  · change rawA stage3 recipe3 4 16 ≤ A stage4 4 16
    decide +kernel
  · change rawA stage3 recipe3 4 17 ≤ A stage4 4 17
    decide +kernel
  · change rawA stage3 recipe3 4 18 ≤ A stage4 4 18
    decide +kernel
  · change rawA stage3 recipe3 4 19 ≤ A stage4 4 19
    decide +kernel
theorem zY511 (l : Nat) (hjl : 4 < l) (hl : l < 20) :
    rawP stage3 recipe3 4 l ≤ P stage4 4 l := by
  interval_cases l
  · change rawA stage3 recipe3 5 5 ≤ A stage4 5 5
    exact zX176
  · change rawA stage3 recipe3 5 6 ≤ A stage4 5 6
    exact zX177
  · change rawA stage3 recipe3 5 7 ≤ A stage4 5 7
    exact zX178
  · change rawA stage3 recipe3 5 8 ≤ A stage4 5 8
    exact zX179
  · change rawA stage3 recipe3 5 9 ≤ A stage4 5 9
    exact zX180
  · change rawA stage3 recipe3 5 10 ≤ A stage4 5 10
    decide +kernel
  · change rawA stage3 recipe3 5 11 ≤ A stage4 5 11
    decide +kernel
  · change rawA stage3 recipe3 5 12 ≤ A stage4 5 12
    decide +kernel
  · change rawA stage3 recipe3 5 13 ≤ A stage4 5 13
    decide +kernel
  · change rawA stage3 recipe3 5 14 ≤ A stage4 5 14
    decide +kernel
  · change rawA stage3 recipe3 5 15 ≤ A stage4 5 15
    decide +kernel
  · change rawA stage3 recipe3 5 16 ≤ A stage4 5 16
    decide +kernel
  · change rawA stage3 recipe3 5 17 ≤ A stage4 5 17
    decide +kernel
  · change rawA stage3 recipe3 5 18 ≤ A stage4 5 18
    decide +kernel
  · change rawA stage3 recipe3 5 19 ≤ A stage4 5 19
    decide +kernel
theorem zY512 (l : Nat) (hjl : 5 < l) (hl : l < 20) :
    rawP stage3 recipe3 5 l ≤ P stage4 5 l := by
  interval_cases l
  · change rawA stage3 recipe3 6 6 ≤ A stage4 6 6
    exact zX181
  · change rawA stage3 recipe3 6 7 ≤ A stage4 6 7
    exact zX182
  · change rawA stage3 recipe3 6 8 ≤ A stage4 6 8
    exact zX183
  · change rawA stage3 recipe3 6 9 ≤ A stage4 6 9
    exact zX184
  · change rawA stage3 recipe3 6 10 ≤ A stage4 6 10
    decide +kernel
  · change rawA stage3 recipe3 6 11 ≤ A stage4 6 11
    decide +kernel
  · change rawA stage3 recipe3 6 12 ≤ A stage4 6 12
    decide +kernel
  · change rawA stage3 recipe3 6 13 ≤ A stage4 6 13
    decide +kernel
  · change rawA stage3 recipe3 6 14 ≤ A stage4 6 14
    decide +kernel
  · change rawA stage3 recipe3 6 15 ≤ A stage4 6 15
    decide +kernel
  · change rawA stage3 recipe3 6 16 ≤ A stage4 6 16
    decide +kernel
  · change rawA stage3 recipe3 6 17 ≤ A stage4 6 17
    decide +kernel
  · change rawA stage3 recipe3 6 18 ≤ A stage4 6 18
    decide +kernel
  · change rawA stage3 recipe3 6 19 ≤ A stage4 6 19
    decide +kernel
theorem zY513 (l : Nat) (hjl : 6 < l) (hl : l < 20) :
    rawP stage3 recipe3 6 l ≤ P stage4 6 l := by
  interval_cases l
  · change rawA stage3 recipe3 7 7 ≤ A stage4 7 7
    exact zX185
  · change rawA stage3 recipe3 7 8 ≤ A stage4 7 8
    exact zX186
  · change rawA stage3 recipe3 7 9 ≤ A stage4 7 9
    exact zX187
  · change rawA stage3 recipe3 7 10 ≤ A stage4 7 10
    decide +kernel
  · change rawA stage3 recipe3 7 11 ≤ A stage4 7 11
    decide +kernel
  · change rawA stage3 recipe3 7 12 ≤ A stage4 7 12
    decide +kernel
  · change rawA stage3 recipe3 7 13 ≤ A stage4 7 13
    decide +kernel
  · change rawA stage3 recipe3 7 14 ≤ A stage4 7 14
    decide +kernel
  · change rawA stage3 recipe3 7 15 ≤ A stage4 7 15
    decide +kernel
  · change rawA stage3 recipe3 7 16 ≤ A stage4 7 16
    decide +kernel
  · change rawA stage3 recipe3 7 17 ≤ A stage4 7 17
    decide +kernel
  · change rawA stage3 recipe3 7 18 ≤ A stage4 7 18
    decide +kernel
  · change rawA stage3 recipe3 7 19 ≤ A stage4 7 19
    decide +kernel
theorem zY514 (l : Nat) (hjl : 7 < l) (hl : l < 20) :
    rawP stage3 recipe3 7 l ≤ P stage4 7 l := by
  interval_cases l
  · change rawA stage3 recipe3 8 8 ≤ A stage4 8 8
    exact zX188
  · change rawA stage3 recipe3 8 9 ≤ A stage4 8 9
    exact zX189
  · change rawA stage3 recipe3 8 10 ≤ A stage4 8 10
    decide +kernel
  · change rawA stage3 recipe3 8 11 ≤ A stage4 8 11
    decide +kernel
  · change rawA stage3 recipe3 8 12 ≤ A stage4 8 12
    decide +kernel
  · change rawA stage3 recipe3 8 13 ≤ A stage4 8 13
    decide +kernel
  · change rawA stage3 recipe3 8 14 ≤ A stage4 8 14
    decide +kernel
  · change rawA stage3 recipe3 8 15 ≤ A stage4 8 15
    decide +kernel
  · change rawA stage3 recipe3 8 16 ≤ A stage4 8 16
    decide +kernel
  · change rawA stage3 recipe3 8 17 ≤ A stage4 8 17
    decide +kernel
  · change rawA stage3 recipe3 8 18 ≤ A stage4 8 18
    decide +kernel
  · change rawA stage3 recipe3 8 19 ≤ A stage4 8 19
    decide +kernel
theorem zY515 (l : Nat) (hjl : 8 < l) (hl : l < 20) :
    rawP stage3 recipe3 8 l ≤ P stage4 8 l := by
  interval_cases l
  · change rawA stage3 recipe3 9 9 ≤ A stage4 9 9
    exact zX190
  · change rawA stage3 recipe3 9 10 ≤ A stage4 9 10
    decide +kernel
  · change rawA stage3 recipe3 9 11 ≤ A stage4 9 11
    decide +kernel
  · change rawA stage3 recipe3 9 12 ≤ A stage4 9 12
    decide +kernel
  · change rawA stage3 recipe3 9 13 ≤ A stage4 9 13
    decide +kernel
  · change rawA stage3 recipe3 9 14 ≤ A stage4 9 14
    decide +kernel
  · change rawA stage3 recipe3 9 15 ≤ A stage4 9 15
    decide +kernel
  · change rawA stage3 recipe3 9 16 ≤ A stage4 9 16
    decide +kernel
  · change rawA stage3 recipe3 9 17 ≤ A stage4 9 17
    decide +kernel
  · change rawA stage3 recipe3 9 18 ≤ A stage4 9 18
    decide +kernel
  · change rawA stage3 recipe3 9 19 ≤ A stage4 9 19
    decide +kernel
theorem zY516 (l : Nat) (hjl : 9 < l) (hl : l < 20) :
    rawP stage3 recipe3 9 l ≤ P stage4 9 l := by
  interval_cases l
  · change rawA stage3 recipe3 10 10 ≤ A stage4 10 10
    decide +kernel
  · change rawA stage3 recipe3 10 11 ≤ A stage4 10 11
    decide +kernel
  · change rawA stage3 recipe3 10 12 ≤ A stage4 10 12
    decide +kernel
  · change rawA stage3 recipe3 10 13 ≤ A stage4 10 13
    decide +kernel
  · change rawA stage3 recipe3 10 14 ≤ A stage4 10 14
    decide +kernel
  · change rawA stage3 recipe3 10 15 ≤ A stage4 10 15
    decide +kernel
  · change rawA stage3 recipe3 10 16 ≤ A stage4 10 16
    decide +kernel
  · change rawA stage3 recipe3 10 17 ≤ A stage4 10 17
    decide +kernel
  · change rawA stage3 recipe3 10 18 ≤ A stage4 10 18
    decide +kernel
  · change rawA stage3 recipe3 10 19 ≤ A stage4 10 19
    decide +kernel
theorem zY517 (l : Nat) (hjl : 10 < l) (hl : l < 20) :
    rawP stage3 recipe3 10 l ≤ P stage4 10 l := by
  interval_cases l
  · change rawA stage3 recipe3 11 11 ≤ A stage4 11 11
    decide +kernel
  · change rawA stage3 recipe3 11 12 ≤ A stage4 11 12
    decide +kernel
  · change rawA stage3 recipe3 11 13 ≤ A stage4 11 13
    decide +kernel
  · change rawA stage3 recipe3 11 14 ≤ A stage4 11 14
    decide +kernel
  · change rawA stage3 recipe3 11 15 ≤ A stage4 11 15
    decide +kernel
  · change rawA stage3 recipe3 11 16 ≤ A stage4 11 16
    decide +kernel
  · change rawA stage3 recipe3 11 17 ≤ A stage4 11 17
    decide +kernel
  · change rawA stage3 recipe3 11 18 ≤ A stage4 11 18
    decide +kernel
  · change rawA stage3 recipe3 11 19 ≤ A stage4 11 19
    decide +kernel
theorem zY518 (l : Nat) (hjl : 11 < l) (hl : l < 20) :
    rawP stage3 recipe3 11 l ≤ P stage4 11 l := by
  interval_cases l
  · change rawA stage3 recipe3 12 12 ≤ A stage4 12 12
    decide +kernel
  · change rawA stage3 recipe3 12 13 ≤ A stage4 12 13
    decide +kernel
  · change rawA stage3 recipe3 12 14 ≤ A stage4 12 14
    decide +kernel
  · change rawA stage3 recipe3 12 15 ≤ A stage4 12 15
    decide +kernel
  · change rawA stage3 recipe3 12 16 ≤ A stage4 12 16
    decide +kernel
  · change rawA stage3 recipe3 12 17 ≤ A stage4 12 17
    decide +kernel
  · change rawA stage3 recipe3 12 18 ≤ A stage4 12 18
    decide +kernel
  · change rawA stage3 recipe3 12 19 ≤ A stage4 12 19
    decide +kernel
theorem zY519 (l : Nat) (hjl : 12 < l) (hl : l < 20) :
    rawP stage3 recipe3 12 l ≤ P stage4 12 l := by
  interval_cases l
  · change rawA stage3 recipe3 13 13 ≤ A stage4 13 13
    decide +kernel
  · change rawA stage3 recipe3 13 14 ≤ A stage4 13 14
    decide +kernel
  · change rawA stage3 recipe3 13 15 ≤ A stage4 13 15
    decide +kernel
  · change rawA stage3 recipe3 13 16 ≤ A stage4 13 16
    decide +kernel
  · change rawA stage3 recipe3 13 17 ≤ A stage4 13 17
    decide +kernel
  · change rawA stage3 recipe3 13 18 ≤ A stage4 13 18
    decide +kernel
  · change rawA stage3 recipe3 13 19 ≤ A stage4 13 19
    decide +kernel
theorem zY520 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawP stage3 recipe3 13 l ≤ P stage4 13 l := by
  interval_cases l
  · change rawA stage3 recipe3 14 14 ≤ A stage4 14 14
    decide +kernel
  · change rawA stage3 recipe3 14 15 ≤ A stage4 14 15
    decide +kernel
  · change rawA stage3 recipe3 14 16 ≤ A stage4 14 16
    decide +kernel
  · change rawA stage3 recipe3 14 17 ≤ A stage4 14 17
    decide +kernel
  · change rawA stage3 recipe3 14 18 ≤ A stage4 14 18
    decide +kernel
  · change rawA stage3 recipe3 14 19 ≤ A stage4 14 19
    decide +kernel
theorem zY521 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawP stage3 recipe3 14 l ≤ P stage4 14 l := by
  interval_cases l
  · change rawA stage3 recipe3 15 15 ≤ A stage4 15 15
    decide +kernel
  · change rawA stage3 recipe3 15 16 ≤ A stage4 15 16
    decide +kernel
  · change rawA stage3 recipe3 15 17 ≤ A stage4 15 17
    decide +kernel
  · change rawA stage3 recipe3 15 18 ≤ A stage4 15 18
    decide +kernel
  · change rawA stage3 recipe3 15 19 ≤ A stage4 15 19
    decide +kernel
theorem zY522 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawP stage3 recipe3 15 l ≤ P stage4 15 l := by
  interval_cases l
  · change rawA stage3 recipe3 16 16 ≤ A stage4 16 16
    decide +kernel
  · change rawA stage3 recipe3 16 17 ≤ A stage4 16 17
    decide +kernel
  · change rawA stage3 recipe3 16 18 ≤ A stage4 16 18
    decide +kernel
  · change rawA stage3 recipe3 16 19 ≤ A stage4 16 19
    decide +kernel
theorem zY523 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawP stage3 recipe3 16 l ≤ P stage4 16 l := by
  interval_cases l
  · change rawA stage3 recipe3 17 17 ≤ A stage4 17 17
    decide +kernel
  · change rawA stage3 recipe3 17 18 ≤ A stage4 17 18
    decide +kernel
  · change rawA stage3 recipe3 17 19 ≤ A stage4 17 19
    decide +kernel
theorem zY524 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawP stage3 recipe3 17 l ≤ P stage4 17 l := by
  interval_cases l
  · change rawA stage3 recipe3 18 18 ≤ A stage4 18 18
    decide +kernel
  · change rawA stage3 recipe3 18 19 ≤ A stage4 18 19
    decide +kernel
theorem zY525 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawP stage3 recipe3 18 l ≤ P stage4 18 l := by
  interval_cases l
  · change rawA stage3 recipe3 19 19 ≤ A stage4 19 19
    decide +kernel
theorem zY526 (j l : Nat) (hjl : j < l) (hl : l < 20) :
    rawP stage3 recipe3 j l ≤ P stage4 j l := by
  have hj : j < 19 := by omega
  interval_cases j
  · exact zY507 l hjl hl
  · exact zY508 l hjl hl
  · exact zY509 l hjl hl
  · exact zY510 l hjl hl
  · exact zY511 l hjl hl
  · exact zY512 l hjl hl
  · exact zY513 l hjl hl
  · exact zY514 l hjl hl
  · exact zY515 l hjl hl
  · exact zY516 l hjl hl
  · exact zY517 l hjl hl
  · exact zY518 l hjl hl
  · exact zY519 l hjl hl
  · exact zY520 l hjl hl
  · exact zY521 l hjl hl
  · exact zY522 l hjl hl
  · exact zY523 l hjl hl
  · exact zY524 l hjl hl
  · exact zY525 l hjl hl

theorem nonzero_tolerance_3 : ∀ i : Fin 10,
    (recipe3[i.val]?.getD default).tol ≠ 0 := by decide +kernel

theorem nonzero_d_sum_3 : ∀ (i : Fin 10) (j l : Fin 20),
    i.val ≤ j.val → j.val < l.val →
    D stage4 i.val j.val l.val = M stage4 i.val j.val + P stage4 j.val l.val := by
  decide +kernel

theorem zY527 (l : Nat) (hjl : 10 < l) (hl : l < 20) :
    rawD stage3 recipe3 10 10 l ≤ D stage4 10 10 l := by
  interval_cases l <;> decide +kernel
theorem zY528 (i l : Nat)
    (hi : 10 ≤ i) (hij : i ≤ 10) (hjl : 10 < l) (hl : l < 20) :
    rawD stage3 recipe3 i 10 l ≤ D stage4 i 10 l := by
  interval_cases i
  · exact zY527 l hjl hl
theorem zY529 (l : Nat) (hjl : 11 < l) (hl : l < 20) :
    rawD stage3 recipe3 10 11 l ≤ D stage4 10 11 l := by
  interval_cases l <;> decide +kernel
theorem zY530 (l : Nat) (hjl : 11 < l) (hl : l < 20) :
    rawD stage3 recipe3 11 11 l ≤ D stage4 11 11 l := by
  interval_cases l <;> decide +kernel
theorem zY531 (i l : Nat)
    (hi : 10 ≤ i) (hij : i ≤ 11) (hjl : 11 < l) (hl : l < 20) :
    rawD stage3 recipe3 i 11 l ≤ D stage4 i 11 l := by
  interval_cases i
  · exact zY529 l hjl hl
  · exact zY530 l hjl hl
theorem zY532 (l : Nat) (hjl : 12 < l) (hl : l < 20) :
    rawD stage3 recipe3 10 12 l ≤ D stage4 10 12 l := by
  interval_cases l <;> decide +kernel
theorem zY533 (l : Nat) (hjl : 12 < l) (hl : l < 20) :
    rawD stage3 recipe3 11 12 l ≤ D stage4 11 12 l := by
  interval_cases l <;> decide +kernel
theorem zY534 (l : Nat) (hjl : 12 < l) (hl : l < 20) :
    rawD stage3 recipe3 12 12 l ≤ D stage4 12 12 l := by
  interval_cases l <;> decide +kernel
theorem zY535 (i l : Nat)
    (hi : 10 ≤ i) (hij : i ≤ 12) (hjl : 12 < l) (hl : l < 20) :
    rawD stage3 recipe3 i 12 l ≤ D stage4 i 12 l := by
  interval_cases i
  · exact zY532 l hjl hl
  · exact zY533 l hjl hl
  · exact zY534 l hjl hl
theorem zY536 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawD stage3 recipe3 10 13 l ≤ D stage4 10 13 l := by
  interval_cases l <;> decide +kernel
theorem zY537 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawD stage3 recipe3 11 13 l ≤ D stage4 11 13 l := by
  interval_cases l <;> decide +kernel
theorem zY538 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawD stage3 recipe3 12 13 l ≤ D stage4 12 13 l := by
  interval_cases l <;> decide +kernel
theorem zY539 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawD stage3 recipe3 13 13 l ≤ D stage4 13 13 l := by
  interval_cases l <;> decide +kernel
theorem zY540 (i l : Nat)
    (hi : 10 ≤ i) (hij : i ≤ 13) (hjl : 13 < l) (hl : l < 20) :
    rawD stage3 recipe3 i 13 l ≤ D stage4 i 13 l := by
  interval_cases i
  · exact zY536 l hjl hl
  · exact zY537 l hjl hl
  · exact zY538 l hjl hl
  · exact zY539 l hjl hl
theorem zY541 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD stage3 recipe3 10 14 l ≤ D stage4 10 14 l := by
  interval_cases l <;> decide +kernel
theorem zY542 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD stage3 recipe3 11 14 l ≤ D stage4 11 14 l := by
  interval_cases l <;> decide +kernel
theorem zY543 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD stage3 recipe3 12 14 l ≤ D stage4 12 14 l := by
  interval_cases l <;> decide +kernel
theorem zY544 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD stage3 recipe3 13 14 l ≤ D stage4 13 14 l := by
  interval_cases l <;> decide +kernel
theorem zY545 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD stage3 recipe3 14 14 l ≤ D stage4 14 14 l := by
  interval_cases l <;> decide +kernel
theorem zY546 (i l : Nat)
    (hi : 10 ≤ i) (hij : i ≤ 14) (hjl : 14 < l) (hl : l < 20) :
    rawD stage3 recipe3 i 14 l ≤ D stage4 i 14 l := by
  interval_cases i
  · exact zY541 l hjl hl
  · exact zY542 l hjl hl
  · exact zY543 l hjl hl
  · exact zY544 l hjl hl
  · exact zY545 l hjl hl
theorem zY547 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD stage3 recipe3 10 15 l ≤ D stage4 10 15 l := by
  interval_cases l <;> decide +kernel
theorem zY548 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD stage3 recipe3 11 15 l ≤ D stage4 11 15 l := by
  interval_cases l <;> decide +kernel
theorem zY549 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD stage3 recipe3 12 15 l ≤ D stage4 12 15 l := by
  interval_cases l <;> decide +kernel
theorem zY550 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD stage3 recipe3 13 15 l ≤ D stage4 13 15 l := by
  interval_cases l <;> decide +kernel
theorem zY551 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD stage3 recipe3 14 15 l ≤ D stage4 14 15 l := by
  interval_cases l <;> decide +kernel
theorem zY552 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD stage3 recipe3 15 15 l ≤ D stage4 15 15 l := by
  interval_cases l <;> decide +kernel
theorem zY553 (i l : Nat)
    (hi : 10 ≤ i) (hij : i ≤ 15) (hjl : 15 < l) (hl : l < 20) :
    rawD stage3 recipe3 i 15 l ≤ D stage4 i 15 l := by
  interval_cases i
  · exact zY547 l hjl hl
  · exact zY548 l hjl hl
  · exact zY549 l hjl hl
  · exact zY550 l hjl hl
  · exact zY551 l hjl hl
  · exact zY552 l hjl hl
theorem zY554 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage3 recipe3 10 16 l ≤ D stage4 10 16 l := by
  interval_cases l <;> decide +kernel
theorem zY555 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage3 recipe3 11 16 l ≤ D stage4 11 16 l := by
  interval_cases l <;> decide +kernel
theorem zY556 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage3 recipe3 12 16 l ≤ D stage4 12 16 l := by
  interval_cases l <;> decide +kernel
theorem zY557 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage3 recipe3 13 16 l ≤ D stage4 13 16 l := by
  interval_cases l <;> decide +kernel
theorem zY558 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage3 recipe3 14 16 l ≤ D stage4 14 16 l := by
  interval_cases l <;> decide +kernel
theorem zY559 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage3 recipe3 15 16 l ≤ D stage4 15 16 l := by
  interval_cases l <;> decide +kernel
theorem zY560 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage3 recipe3 16 16 l ≤ D stage4 16 16 l := by
  interval_cases l <;> decide +kernel
theorem zY561 (i l : Nat)
    (hi : 10 ≤ i) (hij : i ≤ 16) (hjl : 16 < l) (hl : l < 20) :
    rawD stage3 recipe3 i 16 l ≤ D stage4 i 16 l := by
  interval_cases i
  · exact zY554 l hjl hl
  · exact zY555 l hjl hl
  · exact zY556 l hjl hl
  · exact zY557 l hjl hl
  · exact zY558 l hjl hl
  · exact zY559 l hjl hl
  · exact zY560 l hjl hl
theorem zY562 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage3 recipe3 10 17 l ≤ D stage4 10 17 l := by
  interval_cases l <;> decide +kernel
theorem zY563 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage3 recipe3 11 17 l ≤ D stage4 11 17 l := by
  interval_cases l <;> decide +kernel
theorem zY564 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage3 recipe3 12 17 l ≤ D stage4 12 17 l := by
  interval_cases l <;> decide +kernel
theorem zY565 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage3 recipe3 13 17 l ≤ D stage4 13 17 l := by
  interval_cases l <;> decide +kernel
theorem zY566 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage3 recipe3 14 17 l ≤ D stage4 14 17 l := by
  interval_cases l <;> decide +kernel
theorem zY567 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage3 recipe3 15 17 l ≤ D stage4 15 17 l := by
  interval_cases l <;> decide +kernel
theorem zY568 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage3 recipe3 16 17 l ≤ D stage4 16 17 l := by
  interval_cases l <;> decide +kernel
theorem zY569 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage3 recipe3 17 17 l ≤ D stage4 17 17 l := by
  interval_cases l <;> decide +kernel
theorem zY570 (i l : Nat)
    (hi : 10 ≤ i) (hij : i ≤ 17) (hjl : 17 < l) (hl : l < 20) :
    rawD stage3 recipe3 i 17 l ≤ D stage4 i 17 l := by
  interval_cases i
  · exact zY562 l hjl hl
  · exact zY563 l hjl hl
  · exact zY564 l hjl hl
  · exact zY565 l hjl hl
  · exact zY566 l hjl hl
  · exact zY567 l hjl hl
  · exact zY568 l hjl hl
  · exact zY569 l hjl hl
theorem zY571 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage3 recipe3 10 18 l ≤ D stage4 10 18 l := by
  interval_cases l <;> decide +kernel
theorem zY572 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage3 recipe3 11 18 l ≤ D stage4 11 18 l := by
  interval_cases l <;> decide +kernel
theorem zY573 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage3 recipe3 12 18 l ≤ D stage4 12 18 l := by
  interval_cases l <;> decide +kernel
theorem zY574 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage3 recipe3 13 18 l ≤ D stage4 13 18 l := by
  interval_cases l <;> decide +kernel
theorem zY575 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage3 recipe3 14 18 l ≤ D stage4 14 18 l := by
  interval_cases l <;> decide +kernel
theorem zY576 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage3 recipe3 15 18 l ≤ D stage4 15 18 l := by
  interval_cases l <;> decide +kernel
theorem zY577 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage3 recipe3 16 18 l ≤ D stage4 16 18 l := by
  interval_cases l <;> decide +kernel
theorem zY578 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage3 recipe3 17 18 l ≤ D stage4 17 18 l := by
  interval_cases l <;> decide +kernel
theorem zY579 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage3 recipe3 18 18 l ≤ D stage4 18 18 l := by
  interval_cases l <;> decide +kernel
theorem zY580 (i l : Nat)
    (hi : 10 ≤ i) (hij : i ≤ 18) (hjl : 18 < l) (hl : l < 20) :
    rawD stage3 recipe3 i 18 l ≤ D stage4 i 18 l := by
  interval_cases i
  · exact zY571 l hjl hl
  · exact zY572 l hjl hl
  · exact zY573 l hjl hl
  · exact zY574 l hjl hl
  · exact zY575 l hjl hl
  · exact zY576 l hjl hl
  · exact zY577 l hjl hl
  · exact zY578 l hjl hl
  · exact zY579 l hjl hl

end ZP
end z231

section z232
namespace ZP
set_option maxHeartbeats 3000000

theorem zY581 (i j l : Nat) (hij : i ≤ j) (hjl : j < l) (hl : l < 20) :
    rawD stage3 recipe3 i j l ≤ D stage4 i j l := by
  by_cases hi : i < 10
  · have hqi := nonzero_tolerance_3 ⟨i,hi⟩
    rw [rawD_eq_sum_of_nonzero hqi]
    rw [nonzero_d_sum_3 ⟨i,hi⟩ ⟨j,by omega⟩ ⟨l,hl⟩ hij hjl]
    exact Nat.add_le_add (zY506 i j hij (by omega))
      (zY526 j l hjl hl)
  · have hi' : 10 ≤ i := by omega
    have hj : 10 ≤ j := by omega
    have hj' : j < 19 := by omega
    interval_cases j
    · exact zY528 i l hi' hij hjl hl
    · exact zY531 i l hi' hij hjl hl
    · exact zY535 i l hi' hij hjl hl
    · exact zY540 i l hi' hij hjl hl
    · exact zY546 i l hi' hij hjl hl
    · exact zY553 i l hi' hij hjl hl
    · exact zY561 i l hi' hij hjl hl
    · exact zY570 i l hi' hij hjl hl
    · exact zY580 i l hi' hij hjl hl

theorem _root_.solution : TransitionCertificate stage3 recipe3 stage4 where
  a i j hij := zY465 i.val j.val hij j.isLt
  b i j hij := zY486 i.val j.val hij j.isLt
  m i j hij hn := zY506 i.val j.val hij (by omega)
  p j l hjl := zY526 j.val l.val hjl l.isLt
  d i j l hij hjl := zY581 i.val j.val l.val hij hjl l.isLt
end ZP
end z232
