-- Prove2me | solution 1 for Paley11987Verified.CompactFiniteProfile11987.transition1
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-23T05:25:00.593391+00:00
-- url     : https://prove2.me/submissions/4162db5c-9b62-4c97-8050-2640c3bbe764

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

section z128
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX36 : rawA stage1 recipe1 0 0 ≤ A stage2 0 0 := by
  change maximum ((cases 8 19).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 9 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251974595919926 21158633452378305 21158633452378305)) ≤ 1412344207399923468
  rw [cases_8_1_eq]
  decide +kernel
theorem zX37 : rawA stage1 recipe1 0 1 ≤ A stage2 0 1 := by
  change maximum ((cases 7 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 9 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251974595919926 21158633452378305 21158633452378305)) ≤ 17134272522554968
  rw [cases_7_0_eq]
  decide +kernel
theorem zX38 : rawA stage1 recipe1 0 2 ≤ A stage2 0 2 := by
  change maximum ((cases 6 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 9 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 21158633452378305 21088803175974973)) ≤ 15359819334081394
  rw [cases_6_0_eq]
  decide +kernel
theorem zX39 : rawA stage1 recipe1 0 3 ≤ A stage2 0 3 := by
  change maximum ((cases 5 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 9 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 21158633452378305 21088803175974973)) ≤ 14100817749320624
  rw [cases_5_0_eq]
  decide +kernel
theorem zX40 : rawA stage1 recipe1 0 4 ≤ A stage2 0 4 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 9 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 21158633452378305 21088803175974973)) ≤ 12338215530655546
  rw [cases_4_0_eq]
  decide +kernel
theorem zX41 : rawA stage1 recipe1 0 5 ≤ A stage2 0 5 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 9 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 18516669605698843 18446839329295511)) ≤ 12338215530655546
  rw [cases_4_0_eq]
  decide +kernel
theorem zX42 : rawA stage1 recipe1 0 6 ≤ A stage2 0 6 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 9 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 18516669605698843 18446839329295511)) ≤ 10827413628942622
  rw [cases_3_0_eq]
  decide +kernel
theorem zX43 : rawA stage1 recipe1 0 7 ≤ A stage2 0 7 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 9 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 18516669605698843 18446839329295511)) ≤ 9316611727229698
  rw [cases_2_0_eq]
  decide +kernel
theorem zX44 : rawA stage1 recipe1 0 8 ≤ A stage2 0 8 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 9 then 0 else
      c.u*17377574121934+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 17377574121934 18516669605698843 550371609386590)) ≤ 642970242511558
  rw [cases_2_0_eq]
  decide +kernel
theorem zX45 : rawA stage1 recipe1 0 9 ≤ A stage2 0 9 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 9 then 0 else
      c.u*17377574121934+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 17377574121934 18516669605698843 550371609386590)) ≤ 521327223658020
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z128

section z129
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX46 : rawA stage1 recipe1 1 1 ≤ A stage2 1 1 := by
  change maximum ((cases 7 17).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 9 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251974595919926 21158633452378305 21158633452378305)) ≤ 1178591341040082409
  rw [cases_7_1_eq]
  decide +kernel
theorem zX47 : rawA stage1 recipe1 1 2 ≤ A stage2 1 2 := by
  change maximum ((cases 6 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 9 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 21158633452378305 21088803175974973)) ≤ 15359819334081394
  rw [cases_6_0_eq]
  decide +kernel
theorem zX48 : rawA stage1 recipe1 1 3 ≤ A stage2 1 3 := by
  change maximum ((cases 5 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 9 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 21158633452378305 21088803175974973)) ≤ 14100817749320624
  rw [cases_5_0_eq]
  decide +kernel
theorem zX49 : rawA stage1 recipe1 1 4 ≤ A stage2 1 4 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 9 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 21158633452378305 21088803175974973)) ≤ 12338215530655546
  rw [cases_4_0_eq]
  decide +kernel
theorem zX50 : rawA stage1 recipe1 1 5 ≤ A stage2 1 5 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 9 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 18516669605698843 18446839329295511)) ≤ 12338215530655546
  rw [cases_4_0_eq]
  decide +kernel
end ZP
end z129

section z130
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX51 : rawA stage1 recipe1 1 6 ≤ A stage2 1 6 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 9 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 18516669605698843 18446839329295511)) ≤ 10827413628942622
  rw [cases_3_0_eq]
  decide +kernel
theorem zX52 : rawA stage1 recipe1 1 7 ≤ A stage2 1 7 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 9 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 18516669605698843 18446839329295511)) ≤ 9316611727229698
  rw [cases_2_0_eq]
  decide +kernel
theorem zX53 : rawA stage1 recipe1 1 8 ≤ A stage2 1 8 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 9 then 0 else
      c.u*17377574121934+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 17377574121934 18516669605698843 550371609386590)) ≤ 642970242511558
  rw [cases_2_0_eq]
  decide +kernel
theorem zX54 : rawA stage1 recipe1 1 9 ≤ A stage2 1 9 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 9 then 0 else
      c.u*17377574121934+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 17377574121934 18516669605698843 550371609386590)) ≤ 521327223658020
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z130

section z131
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX55 : rawA stage1 recipe1 2 2 ≤ A stage2 2 2 := by
  change maximum ((cases 6 15).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 21158633452378305 21088803175974973)) ≤ 964226977180227911
  rw [cases_6_1_eq]
  decide +kernel
theorem zX56 : rawA stage1 recipe1 2 3 ≤ A stage2 2 3 := by
  change maximum ((cases 5 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 21158633452378305 21088803175974973)) ≤ 14100817749320624
  rw [cases_5_0_eq]
  decide +kernel
theorem zX57 : rawA stage1 recipe1 2 4 ≤ A stage2 2 4 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 21158633452378305 21088803175974973)) ≤ 12338215530655546
  rw [cases_4_0_eq]
  decide +kernel
theorem zX58 : rawA stage1 recipe1 2 5 ≤ A stage2 2 5 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 18516669605698843 18446839329295511)) ≤ 12338215530655546
  rw [cases_4_0_eq]
  decide +kernel
theorem zX59 : rawA stage1 recipe1 2 6 ≤ A stage2 2 6 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 18516669605698843 18446839329295511)) ≤ 10827413628942622
  rw [cases_3_0_eq]
  decide +kernel
theorem zX60 : rawA stage1 recipe1 2 7 ≤ A stage2 2 7 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 18516669605698843 18446839329295511)) ≤ 9316611727229698
  rw [cases_2_0_eq]
  decide +kernel
theorem zX61 : rawA stage1 recipe1 2 8 ≤ A stage2 2 8 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*17377574121934+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 17377574121934 18516669605698843 550371609386590)) ≤ 642970242511558
  rw [cases_2_0_eq]
  decide +kernel
theorem zX62 : rawA stage1 recipe1 2 9 ≤ A stage2 2 9 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*17377574121934+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 17377574121934 18516669605698843 550371609386590)) ≤ 521327223658020
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z131

section z132
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX63 : rawA stage1 recipe1 3 3 ≤ A stage2 3 3 := by
  change maximum ((cases 5 13).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 21158633452378305 21088803175974973)) ≤ 772931735393821214
  rw [cases_5_1_eq]
  decide +kernel
theorem zX64 : rawA stage1 recipe1 3 4 ≤ A stage2 3 4 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 21158633452378305 21088803175974973)) ≤ 12338215530655546
  rw [cases_4_0_eq]
  decide +kernel
theorem zX65 : rawA stage1 recipe1 3 5 ≤ A stage2 3 5 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 18516669605698843 18446839329295511)) ≤ 12338215530655546
  rw [cases_4_0_eq]
  decide +kernel
theorem zX66 : rawA stage1 recipe1 3 6 ≤ A stage2 3 6 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 18516669605698843 18446839329295511)) ≤ 10827413628942622
  rw [cases_3_0_eq]
  decide +kernel
theorem zX67 : rawA stage1 recipe1 3 7 ≤ A stage2 3 7 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 18516669605698843 18446839329295511)) ≤ 9316611727229698
  rw [cases_2_0_eq]
  decide +kernel
theorem zX68 : rawA stage1 recipe1 3 8 ≤ A stage2 3 8 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*17377574121934+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 17377574121934 18516669605698843 550371609386590)) ≤ 642970242511558
  rw [cases_2_0_eq]
  decide +kernel
end ZP
end z132

section z133
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX69 : rawA stage1 recipe1 3 9 ≤ A stage2 3 9 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*17377574121934+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 17377574121934 18516669605698843 550371609386590)) ≤ 521327223658020
  rw [cases_1_0_eq]
  decide +kernel
theorem zX70 : rawA stage1 recipe1 4 4 ≤ A stage2 4 4 := by
  change maximum ((cases 4 11).map (fun c : Case =>
    if c.u > 0 ∧ (9 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 21158633452378305 21088803175974973)) ≤ 602291526425888514
  rw [cases_4_1_eq]
  decide +kernel
end ZP
end z133

section z134
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX71 : rawA stage1 recipe1 4 5 ≤ A stage2 4 5 := by
  change maximum ((cases 4 11).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 18516669605698843 18446839329295511)) ≤ 528316538718863578
  rw [cases_4_1_eq]
  decide +kernel
theorem zX72 : rawA stage1 recipe1 4 6 ≤ A stage2 4 6 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 18516669605698843 18446839329295511)) ≤ 10827413628942622
  rw [cases_3_0_eq]
  decide +kernel
theorem zX73 : rawA stage1 recipe1 4 7 ≤ A stage2 4 7 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 18516669605698843 18446839329295511)) ≤ 9316611727229698
  rw [cases_2_0_eq]
  decide +kernel
theorem zX74 : rawA stage1 recipe1 4 8 ≤ A stage2 4 8 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*17377574121934+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 17377574121934 18516669605698843 550371609386590)) ≤ 642970242511558
  rw [cases_2_0_eq]
  decide +kernel
theorem zX75 : rawA stage1 recipe1 4 9 ≤ A stage2 4 9 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*17377574121934+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 17377574121934 18516669605698843 550371609386590)) ≤ 521327223658020
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z134

section z135
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX76 : rawA stage1 recipe1 5 5 ≤ A stage2 5 5 := by
  change maximum ((cases 4 11).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 19828809568467281 18446839329295511)) ≤ 546686498197621710
  rw [cases_4_1_eq]
  decide +kernel
theorem zX77 : rawA stage1 recipe1 5 6 ≤ A stage2 5 6 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 19828809568467281 18446839329295511)) ≤ 10827413628942622
  rw [cases_3_0_eq]
  decide +kernel
theorem zX78 : rawA stage1 recipe1 5 7 ≤ A stage2 5 7 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 19828809568467281 18446839329295511)) ≤ 9316611727229698
  rw [cases_2_0_eq]
  decide +kernel
theorem zX79 : rawA stage1 recipe1 5 8 ≤ A stage2 5 8 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*17377574121934+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 17377574121934 19828809568467281 550371609386590)) ≤ 642970242511558
  rw [cases_2_0_eq]
  decide +kernel
theorem zX80 : rawA stage1 recipe1 5 9 ≤ A stage2 5 9 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*17377574121934+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 17377574121934 19828809568467281 550371609386590)) ≤ 521327223658020
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z135

section z136
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX81 : rawA stage1 recipe1 6 6 ≤ A stage2 6 6 := by
  change maximum ((cases 3 9).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 19828809568467281 18446839329295511)) ≤ 407123567259364127
  rw [cases_3_1_eq]
  decide +kernel
theorem zX82 : rawA stage1 recipe1 6 7 ≤ A stage2 6 7 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 19828809568467281 18446839329295511)) ≤ 9316611727229698
  rw [cases_2_0_eq]
  decide +kernel
theorem zX83 : rawA stage1 recipe1 6 8 ≤ A stage2 6 8 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*17377574121934+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 17377574121934 19828809568467281 550371609386590)) ≤ 642970242511558
  rw [cases_2_0_eq]
  decide +kernel
theorem zX84 : rawA stage1 recipe1 6 9 ≤ A stage2 6 9 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*17377574121934+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 17377574121934 19828809568467281 550371609386590)) ≤ 521327223658020
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z136

section z137
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX85 : rawA stage1 recipe1 7 7 ≤ A stage2 7 7 := by
  change maximum ((cases 2 7).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*251800316952154+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 251800316952154 19828809568467281 18446839329295511)) ≤ 291921851594712597
  rw [cases_2_1_eq]
  decide +kernel
theorem zX86 : rawA stage1 recipe1 7 8 ≤ A stage2 7 8 := by
  change maximum ((cases 2 7).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*17377574121934+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 17377574121934 19828809568467281 550371609386590)) ≤ 122761659142537378
  rw [cases_2_1_eq]
  decide +kernel
theorem zX87 : rawA stage1 recipe1 7 9 ≤ A stage2 7 9 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 10 then 0 else
      c.u*17377574121934+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 17377574121934 19828809568467281 550371609386590)) ≤ 521327223658020
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z137

section z138
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX88 : rawA stage1 recipe1 8 8 ≤ A stage2 8 8 := by
  change maximum ((cases 2 7).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 11 then 0 else
      c.u*241856539025375+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 17377574121934 19828809568467281 550371609386590)) ≤ 122761659142537378
  rw [cases_2_1_eq]
  decide +kernel
theorem zX89 : rawA stage1 recipe1 8 9 ≤ A stage2 8 9 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 11 then 0 else
      c.u*241856539025375+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 17377574121934 19828809568467281 550371609386590)) ≤ 1125253821880607
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z138

section z139
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX90 : rawA stage1 recipe1 9 9 ≤ A stage2 9 9 := by
  change maximum ((cases 1 5).map (fun c : Case =>
    if c.u > 0 ∧ (8 : Nat) = 11 then 0 else
      c.u*241856539025375+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 17377574121934 19828809568467281 550371609386590)) ≤ 61537227738366095
  rw [cases_1_1_eq]
  decide +kernel
end ZP
end z139

section z160
namespace ZP
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
theorem zY160 (j : Nat) (hij : 0 ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 0 j ≤ A stage2 0 j := by
  interval_cases j
  · exact zX36
  · exact zX37
  · exact zX38
  · exact zX39
  · exact zX40
  · exact zX41
  · exact zX42
  · exact zX43
  · exact zX44
  · exact zX45
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
theorem zY161 (j : Nat) (hij : 1 ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 1 j ≤ A stage2 1 j := by
  interval_cases j
  · exact zX46
  · exact zX47
  · exact zX48
  · exact zX49
  · exact zX50
  · exact zX51
  · exact zX52
  · exact zX53
  · exact zX54
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
theorem zY162 (j : Nat) (hij : 2 ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 2 j ≤ A stage2 2 j := by
  interval_cases j
  · exact zX55
  · exact zX56
  · exact zX57
  · exact zX58
  · exact zX59
  · exact zX60
  · exact zX61
  · exact zX62
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
theorem zY163 (j : Nat) (hij : 3 ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 3 j ≤ A stage2 3 j := by
  interval_cases j
  · exact zX63
  · exact zX64
  · exact zX65
  · exact zX66
  · exact zX67
  · exact zX68
  · exact zX69
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
theorem zY164 (j : Nat) (hij : 4 ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 4 j ≤ A stage2 4 j := by
  interval_cases j
  · exact zX70
  · exact zX71
  · exact zX72
  · exact zX73
  · exact zX74
  · exact zX75
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
theorem zY165 (j : Nat) (hij : 5 ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 5 j ≤ A stage2 5 j := by
  interval_cases j
  · exact zX76
  · exact zX77
  · exact zX78
  · exact zX79
  · exact zX80
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
theorem zY166 (j : Nat) (hij : 6 ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 6 j ≤ A stage2 6 j := by
  interval_cases j
  · exact zX81
  · exact zX82
  · exact zX83
  · exact zX84
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
theorem zY167 (j : Nat) (hij : 7 ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 7 j ≤ A stage2 7 j := by
  interval_cases j
  · exact zX85
  · exact zX86
  · exact zX87
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
theorem zY168 (j : Nat) (hij : 8 ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 8 j ≤ A stage2 8 j := by
  interval_cases j
  · exact zX88
  · exact zX89
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
theorem zY169 (j : Nat) (hij : 9 ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 9 j ≤ A stage2 9 j := by
  interval_cases j
  · exact zX90
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
theorem zY170 (j : Nat) (hij : 10 ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 10 j ≤ A stage2 10 j := by
  interval_cases j <;> decide +kernel
theorem zY171 (j : Nat) (hij : 11 ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 11 j ≤ A stage2 11 j := by
  interval_cases j <;> decide +kernel
theorem zY172 (j : Nat) (hij : 12 ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 12 j ≤ A stage2 12 j := by
  interval_cases j <;> decide +kernel
theorem zY173 (j : Nat) (hij : 13 ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 13 j ≤ A stage2 13 j := by
  interval_cases j <;> decide +kernel
theorem zY174 (j : Nat) (hij : 14 ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 14 j ≤ A stage2 14 j := by
  interval_cases j <;> decide +kernel
theorem zY175 (j : Nat) (hij : 15 ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 15 j ≤ A stage2 15 j := by
  interval_cases j <;> decide +kernel
theorem zY176 (j : Nat) (hij : 16 ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 16 j ≤ A stage2 16 j := by
  interval_cases j <;> decide +kernel
theorem zY177 (j : Nat) (hij : 17 ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 17 j ≤ A stage2 17 j := by
  interval_cases j <;> decide +kernel
theorem zY178 (j : Nat) (hij : 18 ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 18 j ≤ A stage2 18 j := by
  interval_cases j <;> decide +kernel
theorem zY179 (j : Nat) (hij : 19 ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 19 j ≤ A stage2 19 j := by
  interval_cases j <;> decide +kernel
theorem zY180 (i j : Nat) (hij : i ≤ j) (hj : j < 20) :
    rawA stage1 recipe1 i j ≤ A stage2 i j := by
  have hi : i < 20 := Nat.lt_of_le_of_lt hij hj
  interval_cases i
  · exact zY160 j hij hj
  · exact zY161 j hij hj
  · exact zY162 j hij hj
  · exact zY163 j hij hj
  · exact zY164 j hij hj
  · exact zY165 j hij hj
  · exact zY166 j hij hj
  · exact zY167 j hij hj
  · exact zY168 j hij hj
  · exact zY169 j hij hj
  · exact zY170 j hij hj
  · exact zY171 j hij hj
  · exact zY172 j hij hj
  · exact zY173 j hij hj
  · exact zY174 j hij hj
  · exact zY175 j hij hj
  · exact zY176 j hij hj
  · exact zY177 j hij hj
  · exact zY178 j hij hj
  · exact zY179 j hij hj
theorem zY181 (j : Nat) (hij : 0 ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 0 j ≤ B stage2 0 j := by
  interval_cases j <;> decide +kernel
theorem zY182 (j : Nat) (hij : 1 ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 1 j ≤ B stage2 1 j := by
  interval_cases j <;> decide +kernel
theorem zY183 (j : Nat) (hij : 2 ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 2 j ≤ B stage2 2 j := by
  interval_cases j <;> decide +kernel
theorem zY184 (j : Nat) (hij : 3 ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 3 j ≤ B stage2 3 j := by
  interval_cases j <;> decide +kernel
theorem zY185 (j : Nat) (hij : 4 ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 4 j ≤ B stage2 4 j := by
  interval_cases j <;> decide +kernel
theorem zY186 (j : Nat) (hij : 5 ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 5 j ≤ B stage2 5 j := by
  interval_cases j <;> decide +kernel
theorem zY187 (j : Nat) (hij : 6 ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 6 j ≤ B stage2 6 j := by
  interval_cases j <;> decide +kernel
theorem zY188 (j : Nat) (hij : 7 ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 7 j ≤ B stage2 7 j := by
  interval_cases j <;> decide +kernel
theorem zY189 (j : Nat) (hij : 8 ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 8 j ≤ B stage2 8 j := by
  interval_cases j <;> decide +kernel
theorem zY190 (j : Nat) (hij : 9 ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 9 j ≤ B stage2 9 j := by
  interval_cases j <;> decide +kernel
theorem zY191 (j : Nat) (hij : 10 ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 10 j ≤ B stage2 10 j := by
  interval_cases j <;> decide +kernel
theorem zY192 (j : Nat) (hij : 11 ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 11 j ≤ B stage2 11 j := by
  interval_cases j <;> decide +kernel
theorem zY193 (j : Nat) (hij : 12 ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 12 j ≤ B stage2 12 j := by
  interval_cases j <;> decide +kernel
theorem zY194 (j : Nat) (hij : 13 ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 13 j ≤ B stage2 13 j := by
  interval_cases j <;> decide +kernel
theorem zY195 (j : Nat) (hij : 14 ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 14 j ≤ B stage2 14 j := by
  interval_cases j <;> decide +kernel
theorem zY196 (j : Nat) (hij : 15 ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 15 j ≤ B stage2 15 j := by
  interval_cases j <;> decide +kernel
theorem zY197 (j : Nat) (hij : 16 ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 16 j ≤ B stage2 16 j := by
  interval_cases j <;> decide +kernel
theorem zY198 (j : Nat) (hij : 17 ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 17 j ≤ B stage2 17 j := by
  interval_cases j <;> decide +kernel
theorem zY199 (j : Nat) (hij : 18 ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 18 j ≤ B stage2 18 j := by
  interval_cases j <;> decide +kernel
theorem zY200 (j : Nat) (hij : 19 ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 19 j ≤ B stage2 19 j := by
  interval_cases j <;> decide +kernel
theorem zY201 (i j : Nat) (hij : i ≤ j) (hj : j < 20) :
    rawB stage1 recipe1 i j ≤ B stage2 i j := by
  have hi : i < 20 := Nat.lt_of_le_of_lt hij hj
  interval_cases i
  · exact zY181 j hij hj
  · exact zY182 j hij hj
  · exact zY183 j hij hj
  · exact zY184 j hij hj
  · exact zY185 j hij hj
  · exact zY186 j hij hj
  · exact zY187 j hij hj
  · exact zY188 j hij hj
  · exact zY189 j hij hj
  · exact zY190 j hij hj
  · exact zY191 j hij hj
  · exact zY192 j hij hj
  · exact zY193 j hij hj
  · exact zY194 j hij hj
  · exact zY195 j hij hj
  · exact zY196 j hij hj
  · exact zY197 j hij hj
  · exact zY198 j hij hj
  · exact zY199 j hij hj
  · exact zY200 j hij hj
theorem zY202 (j : Nat) (hij : 0 ≤ j) (hj : j < 19) :
    rawM stage1 recipe1 0 j ≤ M stage2 0 j := by
  interval_cases j <;> decide +kernel
theorem zY203 (j : Nat) (hij : 1 ≤ j) (hj : j < 19) :
    rawM stage1 recipe1 1 j ≤ M stage2 1 j := by
  interval_cases j <;> decide +kernel
theorem zY204 (j : Nat) (hij : 2 ≤ j) (hj : j < 19) :
    rawM stage1 recipe1 2 j ≤ M stage2 2 j := by
  interval_cases j <;> decide +kernel
theorem zY205 (j : Nat) (hij : 3 ≤ j) (hj : j < 19) :
    rawM stage1 recipe1 3 j ≤ M stage2 3 j := by
  interval_cases j <;> decide +kernel
theorem zY206 (j : Nat) (hij : 4 ≤ j) (hj : j < 19) :
    rawM stage1 recipe1 4 j ≤ M stage2 4 j := by
  interval_cases j <;> decide +kernel
theorem zY207 (j : Nat) (hij : 5 ≤ j) (hj : j < 19) :
    rawM stage1 recipe1 5 j ≤ M stage2 5 j := by
  interval_cases j <;> decide +kernel
theorem zY208 (j : Nat) (hij : 6 ≤ j) (hj : j < 19) :
    rawM stage1 recipe1 6 j ≤ M stage2 6 j := by
  interval_cases j <;> decide +kernel
theorem zY209 (j : Nat) (hij : 7 ≤ j) (hj : j < 19) :
    rawM stage1 recipe1 7 j ≤ M stage2 7 j := by
  interval_cases j <;> decide +kernel
theorem zY210 (j : Nat) (hij : 8 ≤ j) (hj : j < 19) :
    rawM stage1 recipe1 8 j ≤ M stage2 8 j := by
  interval_cases j <;> decide +kernel
theorem zY211 (j : Nat) (hij : 9 ≤ j) (hj : j < 19) :
    rawM stage1 recipe1 9 j ≤ M stage2 9 j := by
  interval_cases j <;> decide +kernel
theorem zY212 (j : Nat) (hij : 10 ≤ j) (hj : j < 19) :
    rawM stage1 recipe1 10 j ≤ M stage2 10 j := by
  interval_cases j <;> decide +kernel
theorem zY213 (j : Nat) (hij : 11 ≤ j) (hj : j < 19) :
    rawM stage1 recipe1 11 j ≤ M stage2 11 j := by
  interval_cases j <;> decide +kernel
theorem zY214 (j : Nat) (hij : 12 ≤ j) (hj : j < 19) :
    rawM stage1 recipe1 12 j ≤ M stage2 12 j := by
  interval_cases j <;> decide +kernel
theorem zY215 (j : Nat) (hij : 13 ≤ j) (hj : j < 19) :
    rawM stage1 recipe1 13 j ≤ M stage2 13 j := by
  interval_cases j <;> decide +kernel
theorem zY216 (j : Nat) (hij : 14 ≤ j) (hj : j < 19) :
    rawM stage1 recipe1 14 j ≤ M stage2 14 j := by
  interval_cases j <;> decide +kernel
theorem zY217 (j : Nat) (hij : 15 ≤ j) (hj : j < 19) :
    rawM stage1 recipe1 15 j ≤ M stage2 15 j := by
  interval_cases j <;> decide +kernel
theorem zY218 (j : Nat) (hij : 16 ≤ j) (hj : j < 19) :
    rawM stage1 recipe1 16 j ≤ M stage2 16 j := by
  interval_cases j <;> decide +kernel
theorem zY219 (j : Nat) (hij : 17 ≤ j) (hj : j < 19) :
    rawM stage1 recipe1 17 j ≤ M stage2 17 j := by
  interval_cases j <;> decide +kernel
theorem zY220 (j : Nat) (hij : 18 ≤ j) (hj : j < 19) :
    rawM stage1 recipe1 18 j ≤ M stage2 18 j := by
  interval_cases j <;> decide +kernel
theorem zY221 (i j : Nat) (hij : i ≤ j) (hj : j < 19) :
    rawM stage1 recipe1 i j ≤ M stage2 i j := by
  have hi : i < 19 := Nat.lt_of_le_of_lt hij hj
  interval_cases i
  · exact zY202 j hij hj
  · exact zY203 j hij hj
  · exact zY204 j hij hj
  · exact zY205 j hij hj
  · exact zY206 j hij hj
  · exact zY207 j hij hj
  · exact zY208 j hij hj
  · exact zY209 j hij hj
  · exact zY210 j hij hj
  · exact zY211 j hij hj
  · exact zY212 j hij hj
  · exact zY213 j hij hj
  · exact zY214 j hij hj
  · exact zY215 j hij hj
  · exact zY216 j hij hj
  · exact zY217 j hij hj
  · exact zY218 j hij hj
  · exact zY219 j hij hj
  · exact zY220 j hij hj
theorem zY222 (l : Nat) (hjl : 0 < l) (hl : l < 20) :
    rawP stage1 recipe1 0 l ≤ P stage2 0 l := by
  interval_cases l
  · change rawA stage1 recipe1 1 1 ≤ A stage2 1 1
    exact zX46
  · change rawA stage1 recipe1 1 2 ≤ A stage2 1 2
    exact zX47
  · change rawA stage1 recipe1 1 3 ≤ A stage2 1 3
    exact zX48
  · change rawA stage1 recipe1 1 4 ≤ A stage2 1 4
    exact zX49
  · change rawA stage1 recipe1 1 5 ≤ A stage2 1 5
    exact zX50
  · change rawA stage1 recipe1 1 6 ≤ A stage2 1 6
    exact zX51
  · change rawA stage1 recipe1 1 7 ≤ A stage2 1 7
    exact zX52
  · change rawA stage1 recipe1 1 8 ≤ A stage2 1 8
    exact zX53
  · change rawA stage1 recipe1 1 9 ≤ A stage2 1 9
    exact zX54
  · change rawA stage1 recipe1 1 10 ≤ A stage2 1 10
    decide +kernel
  · change rawA stage1 recipe1 1 11 ≤ A stage2 1 11
    decide +kernel
  · change rawA stage1 recipe1 1 12 ≤ A stage2 1 12
    decide +kernel
  · change rawA stage1 recipe1 1 13 ≤ A stage2 1 13
    decide +kernel
  · change rawA stage1 recipe1 1 14 ≤ A stage2 1 14
    decide +kernel
  · change rawA stage1 recipe1 1 15 ≤ A stage2 1 15
    decide +kernel
  · change rawA stage1 recipe1 1 16 ≤ A stage2 1 16
    decide +kernel
  · change rawA stage1 recipe1 1 17 ≤ A stage2 1 17
    decide +kernel
  · change rawA stage1 recipe1 1 18 ≤ A stage2 1 18
    decide +kernel
  · change rawA stage1 recipe1 1 19 ≤ A stage2 1 19
    decide +kernel
theorem zY223 (l : Nat) (hjl : 1 < l) (hl : l < 20) :
    rawP stage1 recipe1 1 l ≤ P stage2 1 l := by
  interval_cases l
  · change rawA stage1 recipe1 2 2 ≤ A stage2 2 2
    exact zX55
  · change rawA stage1 recipe1 2 3 ≤ A stage2 2 3
    exact zX56
  · change rawA stage1 recipe1 2 4 ≤ A stage2 2 4
    exact zX57
  · change rawA stage1 recipe1 2 5 ≤ A stage2 2 5
    exact zX58
  · change rawA stage1 recipe1 2 6 ≤ A stage2 2 6
    exact zX59
  · change rawA stage1 recipe1 2 7 ≤ A stage2 2 7
    exact zX60
  · change rawA stage1 recipe1 2 8 ≤ A stage2 2 8
    exact zX61
  · change rawA stage1 recipe1 2 9 ≤ A stage2 2 9
    exact zX62
  · change rawA stage1 recipe1 2 10 ≤ A stage2 2 10
    decide +kernel
  · change rawA stage1 recipe1 2 11 ≤ A stage2 2 11
    decide +kernel
  · change rawA stage1 recipe1 2 12 ≤ A stage2 2 12
    decide +kernel
  · change rawA stage1 recipe1 2 13 ≤ A stage2 2 13
    decide +kernel
  · change rawA stage1 recipe1 2 14 ≤ A stage2 2 14
    decide +kernel
  · change rawA stage1 recipe1 2 15 ≤ A stage2 2 15
    decide +kernel
  · change rawA stage1 recipe1 2 16 ≤ A stage2 2 16
    decide +kernel
  · change rawA stage1 recipe1 2 17 ≤ A stage2 2 17
    decide +kernel
  · change rawA stage1 recipe1 2 18 ≤ A stage2 2 18
    decide +kernel
  · change rawA stage1 recipe1 2 19 ≤ A stage2 2 19
    decide +kernel
theorem zY224 (l : Nat) (hjl : 2 < l) (hl : l < 20) :
    rawP stage1 recipe1 2 l ≤ P stage2 2 l := by
  interval_cases l
  · change rawA stage1 recipe1 3 3 ≤ A stage2 3 3
    exact zX63
  · change rawA stage1 recipe1 3 4 ≤ A stage2 3 4
    exact zX64
  · change rawA stage1 recipe1 3 5 ≤ A stage2 3 5
    exact zX65
  · change rawA stage1 recipe1 3 6 ≤ A stage2 3 6
    exact zX66
  · change rawA stage1 recipe1 3 7 ≤ A stage2 3 7
    exact zX67
  · change rawA stage1 recipe1 3 8 ≤ A stage2 3 8
    exact zX68
  · change rawA stage1 recipe1 3 9 ≤ A stage2 3 9
    exact zX69
  · change rawA stage1 recipe1 3 10 ≤ A stage2 3 10
    decide +kernel
  · change rawA stage1 recipe1 3 11 ≤ A stage2 3 11
    decide +kernel
  · change rawA stage1 recipe1 3 12 ≤ A stage2 3 12
    decide +kernel
  · change rawA stage1 recipe1 3 13 ≤ A stage2 3 13
    decide +kernel
  · change rawA stage1 recipe1 3 14 ≤ A stage2 3 14
    decide +kernel
  · change rawA stage1 recipe1 3 15 ≤ A stage2 3 15
    decide +kernel
  · change rawA stage1 recipe1 3 16 ≤ A stage2 3 16
    decide +kernel
  · change rawA stage1 recipe1 3 17 ≤ A stage2 3 17
    decide +kernel
  · change rawA stage1 recipe1 3 18 ≤ A stage2 3 18
    decide +kernel
  · change rawA stage1 recipe1 3 19 ≤ A stage2 3 19
    decide +kernel
theorem zY225 (l : Nat) (hjl : 3 < l) (hl : l < 20) :
    rawP stage1 recipe1 3 l ≤ P stage2 3 l := by
  interval_cases l
  · change rawA stage1 recipe1 4 4 ≤ A stage2 4 4
    exact zX70
  · change rawA stage1 recipe1 4 5 ≤ A stage2 4 5
    exact zX71
  · change rawA stage1 recipe1 4 6 ≤ A stage2 4 6
    exact zX72
  · change rawA stage1 recipe1 4 7 ≤ A stage2 4 7
    exact zX73
  · change rawA stage1 recipe1 4 8 ≤ A stage2 4 8
    exact zX74
  · change rawA stage1 recipe1 4 9 ≤ A stage2 4 9
    exact zX75
  · change rawA stage1 recipe1 4 10 ≤ A stage2 4 10
    decide +kernel
  · change rawA stage1 recipe1 4 11 ≤ A stage2 4 11
    decide +kernel
  · change rawA stage1 recipe1 4 12 ≤ A stage2 4 12
    decide +kernel
  · change rawA stage1 recipe1 4 13 ≤ A stage2 4 13
    decide +kernel
  · change rawA stage1 recipe1 4 14 ≤ A stage2 4 14
    decide +kernel
  · change rawA stage1 recipe1 4 15 ≤ A stage2 4 15
    decide +kernel
  · change rawA stage1 recipe1 4 16 ≤ A stage2 4 16
    decide +kernel
  · change rawA stage1 recipe1 4 17 ≤ A stage2 4 17
    decide +kernel
  · change rawA stage1 recipe1 4 18 ≤ A stage2 4 18
    decide +kernel
  · change rawA stage1 recipe1 4 19 ≤ A stage2 4 19
    decide +kernel
theorem zY226 (l : Nat) (hjl : 4 < l) (hl : l < 20) :
    rawP stage1 recipe1 4 l ≤ P stage2 4 l := by
  interval_cases l
  · change rawA stage1 recipe1 5 5 ≤ A stage2 5 5
    exact zX76
  · change rawA stage1 recipe1 5 6 ≤ A stage2 5 6
    exact zX77
  · change rawA stage1 recipe1 5 7 ≤ A stage2 5 7
    exact zX78
  · change rawA stage1 recipe1 5 8 ≤ A stage2 5 8
    exact zX79
  · change rawA stage1 recipe1 5 9 ≤ A stage2 5 9
    exact zX80
  · change rawA stage1 recipe1 5 10 ≤ A stage2 5 10
    decide +kernel
  · change rawA stage1 recipe1 5 11 ≤ A stage2 5 11
    decide +kernel
  · change rawA stage1 recipe1 5 12 ≤ A stage2 5 12
    decide +kernel
  · change rawA stage1 recipe1 5 13 ≤ A stage2 5 13
    decide +kernel
  · change rawA stage1 recipe1 5 14 ≤ A stage2 5 14
    decide +kernel
  · change rawA stage1 recipe1 5 15 ≤ A stage2 5 15
    decide +kernel
  · change rawA stage1 recipe1 5 16 ≤ A stage2 5 16
    decide +kernel
  · change rawA stage1 recipe1 5 17 ≤ A stage2 5 17
    decide +kernel
  · change rawA stage1 recipe1 5 18 ≤ A stage2 5 18
    decide +kernel
  · change rawA stage1 recipe1 5 19 ≤ A stage2 5 19
    decide +kernel
theorem zY227 (l : Nat) (hjl : 5 < l) (hl : l < 20) :
    rawP stage1 recipe1 5 l ≤ P stage2 5 l := by
  interval_cases l
  · change rawA stage1 recipe1 6 6 ≤ A stage2 6 6
    exact zX81
  · change rawA stage1 recipe1 6 7 ≤ A stage2 6 7
    exact zX82
  · change rawA stage1 recipe1 6 8 ≤ A stage2 6 8
    exact zX83
  · change rawA stage1 recipe1 6 9 ≤ A stage2 6 9
    exact zX84
  · change rawA stage1 recipe1 6 10 ≤ A stage2 6 10
    decide +kernel
  · change rawA stage1 recipe1 6 11 ≤ A stage2 6 11
    decide +kernel
  · change rawA stage1 recipe1 6 12 ≤ A stage2 6 12
    decide +kernel
  · change rawA stage1 recipe1 6 13 ≤ A stage2 6 13
    decide +kernel
  · change rawA stage1 recipe1 6 14 ≤ A stage2 6 14
    decide +kernel
  · change rawA stage1 recipe1 6 15 ≤ A stage2 6 15
    decide +kernel
  · change rawA stage1 recipe1 6 16 ≤ A stage2 6 16
    decide +kernel
  · change rawA stage1 recipe1 6 17 ≤ A stage2 6 17
    decide +kernel
  · change rawA stage1 recipe1 6 18 ≤ A stage2 6 18
    decide +kernel
  · change rawA stage1 recipe1 6 19 ≤ A stage2 6 19
    decide +kernel
theorem zY228 (l : Nat) (hjl : 6 < l) (hl : l < 20) :
    rawP stage1 recipe1 6 l ≤ P stage2 6 l := by
  interval_cases l
  · change rawA stage1 recipe1 7 7 ≤ A stage2 7 7
    exact zX85
  · change rawA stage1 recipe1 7 8 ≤ A stage2 7 8
    exact zX86
  · change rawA stage1 recipe1 7 9 ≤ A stage2 7 9
    exact zX87
  · change rawA stage1 recipe1 7 10 ≤ A stage2 7 10
    decide +kernel
  · change rawA stage1 recipe1 7 11 ≤ A stage2 7 11
    decide +kernel
  · change rawA stage1 recipe1 7 12 ≤ A stage2 7 12
    decide +kernel
  · change rawA stage1 recipe1 7 13 ≤ A stage2 7 13
    decide +kernel
  · change rawA stage1 recipe1 7 14 ≤ A stage2 7 14
    decide +kernel
  · change rawA stage1 recipe1 7 15 ≤ A stage2 7 15
    decide +kernel
  · change rawA stage1 recipe1 7 16 ≤ A stage2 7 16
    decide +kernel
  · change rawA stage1 recipe1 7 17 ≤ A stage2 7 17
    decide +kernel
  · change rawA stage1 recipe1 7 18 ≤ A stage2 7 18
    decide +kernel
  · change rawA stage1 recipe1 7 19 ≤ A stage2 7 19
    decide +kernel
theorem zY229 (l : Nat) (hjl : 7 < l) (hl : l < 20) :
    rawP stage1 recipe1 7 l ≤ P stage2 7 l := by
  interval_cases l
  · change rawA stage1 recipe1 8 8 ≤ A stage2 8 8
    exact zX88
  · change rawA stage1 recipe1 8 9 ≤ A stage2 8 9
    exact zX89
  · change rawA stage1 recipe1 8 10 ≤ A stage2 8 10
    decide +kernel
  · change rawA stage1 recipe1 8 11 ≤ A stage2 8 11
    decide +kernel
  · change rawA stage1 recipe1 8 12 ≤ A stage2 8 12
    decide +kernel
  · change rawA stage1 recipe1 8 13 ≤ A stage2 8 13
    decide +kernel
  · change rawA stage1 recipe1 8 14 ≤ A stage2 8 14
    decide +kernel
  · change rawA stage1 recipe1 8 15 ≤ A stage2 8 15
    decide +kernel
  · change rawA stage1 recipe1 8 16 ≤ A stage2 8 16
    decide +kernel
  · change rawA stage1 recipe1 8 17 ≤ A stage2 8 17
    decide +kernel
  · change rawA stage1 recipe1 8 18 ≤ A stage2 8 18
    decide +kernel
  · change rawA stage1 recipe1 8 19 ≤ A stage2 8 19
    decide +kernel
theorem zY230 (l : Nat) (hjl : 8 < l) (hl : l < 20) :
    rawP stage1 recipe1 8 l ≤ P stage2 8 l := by
  interval_cases l
  · change rawA stage1 recipe1 9 9 ≤ A stage2 9 9
    exact zX90
  · change rawA stage1 recipe1 9 10 ≤ A stage2 9 10
    decide +kernel
  · change rawA stage1 recipe1 9 11 ≤ A stage2 9 11
    decide +kernel
  · change rawA stage1 recipe1 9 12 ≤ A stage2 9 12
    decide +kernel
  · change rawA stage1 recipe1 9 13 ≤ A stage2 9 13
    decide +kernel
  · change rawA stage1 recipe1 9 14 ≤ A stage2 9 14
    decide +kernel
  · change rawA stage1 recipe1 9 15 ≤ A stage2 9 15
    decide +kernel
  · change rawA stage1 recipe1 9 16 ≤ A stage2 9 16
    decide +kernel
  · change rawA stage1 recipe1 9 17 ≤ A stage2 9 17
    decide +kernel
  · change rawA stage1 recipe1 9 18 ≤ A stage2 9 18
    decide +kernel
  · change rawA stage1 recipe1 9 19 ≤ A stage2 9 19
    decide +kernel
theorem zY231 (l : Nat) (hjl : 9 < l) (hl : l < 20) :
    rawP stage1 recipe1 9 l ≤ P stage2 9 l := by
  interval_cases l
  · change rawA stage1 recipe1 10 10 ≤ A stage2 10 10
    decide +kernel
  · change rawA stage1 recipe1 10 11 ≤ A stage2 10 11
    decide +kernel
  · change rawA stage1 recipe1 10 12 ≤ A stage2 10 12
    decide +kernel
  · change rawA stage1 recipe1 10 13 ≤ A stage2 10 13
    decide +kernel
  · change rawA stage1 recipe1 10 14 ≤ A stage2 10 14
    decide +kernel
  · change rawA stage1 recipe1 10 15 ≤ A stage2 10 15
    decide +kernel
  · change rawA stage1 recipe1 10 16 ≤ A stage2 10 16
    decide +kernel
  · change rawA stage1 recipe1 10 17 ≤ A stage2 10 17
    decide +kernel
  · change rawA stage1 recipe1 10 18 ≤ A stage2 10 18
    decide +kernel
  · change rawA stage1 recipe1 10 19 ≤ A stage2 10 19
    decide +kernel
theorem zY232 (l : Nat) (hjl : 10 < l) (hl : l < 20) :
    rawP stage1 recipe1 10 l ≤ P stage2 10 l := by
  interval_cases l
  · change rawA stage1 recipe1 11 11 ≤ A stage2 11 11
    decide +kernel
  · change rawA stage1 recipe1 11 12 ≤ A stage2 11 12
    decide +kernel
  · change rawA stage1 recipe1 11 13 ≤ A stage2 11 13
    decide +kernel
  · change rawA stage1 recipe1 11 14 ≤ A stage2 11 14
    decide +kernel
  · change rawA stage1 recipe1 11 15 ≤ A stage2 11 15
    decide +kernel
  · change rawA stage1 recipe1 11 16 ≤ A stage2 11 16
    decide +kernel
  · change rawA stage1 recipe1 11 17 ≤ A stage2 11 17
    decide +kernel
  · change rawA stage1 recipe1 11 18 ≤ A stage2 11 18
    decide +kernel
  · change rawA stage1 recipe1 11 19 ≤ A stage2 11 19
    decide +kernel
theorem zY233 (l : Nat) (hjl : 11 < l) (hl : l < 20) :
    rawP stage1 recipe1 11 l ≤ P stage2 11 l := by
  interval_cases l
  · change rawA stage1 recipe1 12 12 ≤ A stage2 12 12
    decide +kernel
  · change rawA stage1 recipe1 12 13 ≤ A stage2 12 13
    decide +kernel
  · change rawA stage1 recipe1 12 14 ≤ A stage2 12 14
    decide +kernel
  · change rawA stage1 recipe1 12 15 ≤ A stage2 12 15
    decide +kernel
  · change rawA stage1 recipe1 12 16 ≤ A stage2 12 16
    decide +kernel
  · change rawA stage1 recipe1 12 17 ≤ A stage2 12 17
    decide +kernel
  · change rawA stage1 recipe1 12 18 ≤ A stage2 12 18
    decide +kernel
  · change rawA stage1 recipe1 12 19 ≤ A stage2 12 19
    decide +kernel
theorem zY234 (l : Nat) (hjl : 12 < l) (hl : l < 20) :
    rawP stage1 recipe1 12 l ≤ P stage2 12 l := by
  interval_cases l
  · change rawA stage1 recipe1 13 13 ≤ A stage2 13 13
    decide +kernel
  · change rawA stage1 recipe1 13 14 ≤ A stage2 13 14
    decide +kernel
  · change rawA stage1 recipe1 13 15 ≤ A stage2 13 15
    decide +kernel
  · change rawA stage1 recipe1 13 16 ≤ A stage2 13 16
    decide +kernel
  · change rawA stage1 recipe1 13 17 ≤ A stage2 13 17
    decide +kernel
  · change rawA stage1 recipe1 13 18 ≤ A stage2 13 18
    decide +kernel
  · change rawA stage1 recipe1 13 19 ≤ A stage2 13 19
    decide +kernel
theorem zY235 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawP stage1 recipe1 13 l ≤ P stage2 13 l := by
  interval_cases l
  · change rawA stage1 recipe1 14 14 ≤ A stage2 14 14
    decide +kernel
  · change rawA stage1 recipe1 14 15 ≤ A stage2 14 15
    decide +kernel
  · change rawA stage1 recipe1 14 16 ≤ A stage2 14 16
    decide +kernel
  · change rawA stage1 recipe1 14 17 ≤ A stage2 14 17
    decide +kernel
  · change rawA stage1 recipe1 14 18 ≤ A stage2 14 18
    decide +kernel
  · change rawA stage1 recipe1 14 19 ≤ A stage2 14 19
    decide +kernel
theorem zY236 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawP stage1 recipe1 14 l ≤ P stage2 14 l := by
  interval_cases l
  · change rawA stage1 recipe1 15 15 ≤ A stage2 15 15
    decide +kernel
  · change rawA stage1 recipe1 15 16 ≤ A stage2 15 16
    decide +kernel
  · change rawA stage1 recipe1 15 17 ≤ A stage2 15 17
    decide +kernel
  · change rawA stage1 recipe1 15 18 ≤ A stage2 15 18
    decide +kernel
  · change rawA stage1 recipe1 15 19 ≤ A stage2 15 19
    decide +kernel
theorem zY237 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawP stage1 recipe1 15 l ≤ P stage2 15 l := by
  interval_cases l
  · change rawA stage1 recipe1 16 16 ≤ A stage2 16 16
    decide +kernel
  · change rawA stage1 recipe1 16 17 ≤ A stage2 16 17
    decide +kernel
  · change rawA stage1 recipe1 16 18 ≤ A stage2 16 18
    decide +kernel
  · change rawA stage1 recipe1 16 19 ≤ A stage2 16 19
    decide +kernel
theorem zY238 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawP stage1 recipe1 16 l ≤ P stage2 16 l := by
  interval_cases l
  · change rawA stage1 recipe1 17 17 ≤ A stage2 17 17
    decide +kernel
  · change rawA stage1 recipe1 17 18 ≤ A stage2 17 18
    decide +kernel
  · change rawA stage1 recipe1 17 19 ≤ A stage2 17 19
    decide +kernel
theorem zY239 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawP stage1 recipe1 17 l ≤ P stage2 17 l := by
  interval_cases l
  · change rawA stage1 recipe1 18 18 ≤ A stage2 18 18
    decide +kernel
  · change rawA stage1 recipe1 18 19 ≤ A stage2 18 19
    decide +kernel
theorem zY240 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawP stage1 recipe1 18 l ≤ P stage2 18 l := by
  interval_cases l
  · change rawA stage1 recipe1 19 19 ≤ A stage2 19 19
    decide +kernel
theorem zY241 (j l : Nat) (hjl : j < l) (hl : l < 20) :
    rawP stage1 recipe1 j l ≤ P stage2 j l := by
  have hj : j < 19 := by omega
  interval_cases j
  · exact zY222 l hjl hl
  · exact zY223 l hjl hl
  · exact zY224 l hjl hl
  · exact zY225 l hjl hl
  · exact zY226 l hjl hl
  · exact zY227 l hjl hl
  · exact zY228 l hjl hl
  · exact zY229 l hjl hl
  · exact zY230 l hjl hl
  · exact zY231 l hjl hl
  · exact zY232 l hjl hl
  · exact zY233 l hjl hl
  · exact zY234 l hjl hl
  · exact zY235 l hjl hl
  · exact zY236 l hjl hl
  · exact zY237 l hjl hl
  · exact zY238 l hjl hl
  · exact zY239 l hjl hl
  · exact zY240 l hjl hl

theorem nonzero_tolerance_1 : ∀ i : Fin 10,
    (recipe1[i.val]?.getD default).tol ≠ 0 := by decide +kernel

theorem nonzero_d_sum_1 : ∀ (i : Fin 10) (j l : Fin 20),
    i.val ≤ j.val → j.val < l.val →
    D stage2 i.val j.val l.val = M stage2 i.val j.val + P stage2 j.val l.val := by
  decide +kernel

theorem zY242 (l : Nat) (hjl : 10 < l) (hl : l < 20) :
    rawD stage1 recipe1 10 10 l ≤ D stage2 10 10 l := by
  interval_cases l <;> decide +kernel
theorem zY243 (i l : Nat)
    (hi : 10 ≤ i) (hij : i ≤ 10) (hjl : 10 < l) (hl : l < 20) :
    rawD stage1 recipe1 i 10 l ≤ D stage2 i 10 l := by
  interval_cases i
  · exact zY242 l hjl hl
theorem zY244 (l : Nat) (hjl : 11 < l) (hl : l < 20) :
    rawD stage1 recipe1 10 11 l ≤ D stage2 10 11 l := by
  interval_cases l <;> decide +kernel
theorem zY245 (l : Nat) (hjl : 11 < l) (hl : l < 20) :
    rawD stage1 recipe1 11 11 l ≤ D stage2 11 11 l := by
  interval_cases l <;> decide +kernel
theorem zY246 (i l : Nat)
    (hi : 10 ≤ i) (hij : i ≤ 11) (hjl : 11 < l) (hl : l < 20) :
    rawD stage1 recipe1 i 11 l ≤ D stage2 i 11 l := by
  interval_cases i
  · exact zY244 l hjl hl
  · exact zY245 l hjl hl
theorem zY247 (l : Nat) (hjl : 12 < l) (hl : l < 20) :
    rawD stage1 recipe1 10 12 l ≤ D stage2 10 12 l := by
  interval_cases l <;> decide +kernel
theorem zY248 (l : Nat) (hjl : 12 < l) (hl : l < 20) :
    rawD stage1 recipe1 11 12 l ≤ D stage2 11 12 l := by
  interval_cases l <;> decide +kernel
theorem zY249 (l : Nat) (hjl : 12 < l) (hl : l < 20) :
    rawD stage1 recipe1 12 12 l ≤ D stage2 12 12 l := by
  interval_cases l <;> decide +kernel
theorem zY250 (i l : Nat)
    (hi : 10 ≤ i) (hij : i ≤ 12) (hjl : 12 < l) (hl : l < 20) :
    rawD stage1 recipe1 i 12 l ≤ D stage2 i 12 l := by
  interval_cases i
  · exact zY247 l hjl hl
  · exact zY248 l hjl hl
  · exact zY249 l hjl hl
theorem zY251 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawD stage1 recipe1 10 13 l ≤ D stage2 10 13 l := by
  interval_cases l <;> decide +kernel
theorem zY252 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawD stage1 recipe1 11 13 l ≤ D stage2 11 13 l := by
  interval_cases l <;> decide +kernel
theorem zY253 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawD stage1 recipe1 12 13 l ≤ D stage2 12 13 l := by
  interval_cases l <;> decide +kernel
theorem zY254 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawD stage1 recipe1 13 13 l ≤ D stage2 13 13 l := by
  interval_cases l <;> decide +kernel
theorem zY255 (i l : Nat)
    (hi : 10 ≤ i) (hij : i ≤ 13) (hjl : 13 < l) (hl : l < 20) :
    rawD stage1 recipe1 i 13 l ≤ D stage2 i 13 l := by
  interval_cases i
  · exact zY251 l hjl hl
  · exact zY252 l hjl hl
  · exact zY253 l hjl hl
  · exact zY254 l hjl hl
theorem zY256 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD stage1 recipe1 10 14 l ≤ D stage2 10 14 l := by
  interval_cases l <;> decide +kernel
theorem zY257 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD stage1 recipe1 11 14 l ≤ D stage2 11 14 l := by
  interval_cases l <;> decide +kernel
theorem zY258 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD stage1 recipe1 12 14 l ≤ D stage2 12 14 l := by
  interval_cases l <;> decide +kernel
theorem zY259 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD stage1 recipe1 13 14 l ≤ D stage2 13 14 l := by
  interval_cases l <;> decide +kernel
theorem zY260 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD stage1 recipe1 14 14 l ≤ D stage2 14 14 l := by
  interval_cases l <;> decide +kernel
theorem zY261 (i l : Nat)
    (hi : 10 ≤ i) (hij : i ≤ 14) (hjl : 14 < l) (hl : l < 20) :
    rawD stage1 recipe1 i 14 l ≤ D stage2 i 14 l := by
  interval_cases i
  · exact zY256 l hjl hl
  · exact zY257 l hjl hl
  · exact zY258 l hjl hl
  · exact zY259 l hjl hl
  · exact zY260 l hjl hl
theorem zY262 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD stage1 recipe1 10 15 l ≤ D stage2 10 15 l := by
  interval_cases l <;> decide +kernel
theorem zY263 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD stage1 recipe1 11 15 l ≤ D stage2 11 15 l := by
  interval_cases l <;> decide +kernel
theorem zY264 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD stage1 recipe1 12 15 l ≤ D stage2 12 15 l := by
  interval_cases l <;> decide +kernel
theorem zY265 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD stage1 recipe1 13 15 l ≤ D stage2 13 15 l := by
  interval_cases l <;> decide +kernel
theorem zY266 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD stage1 recipe1 14 15 l ≤ D stage2 14 15 l := by
  interval_cases l <;> decide +kernel
theorem zY267 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD stage1 recipe1 15 15 l ≤ D stage2 15 15 l := by
  interval_cases l <;> decide +kernel
theorem zY268 (i l : Nat)
    (hi : 10 ≤ i) (hij : i ≤ 15) (hjl : 15 < l) (hl : l < 20) :
    rawD stage1 recipe1 i 15 l ≤ D stage2 i 15 l := by
  interval_cases i
  · exact zY262 l hjl hl
  · exact zY263 l hjl hl
  · exact zY264 l hjl hl
  · exact zY265 l hjl hl
  · exact zY266 l hjl hl
  · exact zY267 l hjl hl
theorem zY269 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage1 recipe1 10 16 l ≤ D stage2 10 16 l := by
  interval_cases l <;> decide +kernel
theorem zY270 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage1 recipe1 11 16 l ≤ D stage2 11 16 l := by
  interval_cases l <;> decide +kernel
theorem zY271 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage1 recipe1 12 16 l ≤ D stage2 12 16 l := by
  interval_cases l <;> decide +kernel
theorem zY272 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage1 recipe1 13 16 l ≤ D stage2 13 16 l := by
  interval_cases l <;> decide +kernel
theorem zY273 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage1 recipe1 14 16 l ≤ D stage2 14 16 l := by
  interval_cases l <;> decide +kernel
theorem zY274 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage1 recipe1 15 16 l ≤ D stage2 15 16 l := by
  interval_cases l <;> decide +kernel
theorem zY275 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage1 recipe1 16 16 l ≤ D stage2 16 16 l := by
  interval_cases l <;> decide +kernel
theorem zY276 (i l : Nat)
    (hi : 10 ≤ i) (hij : i ≤ 16) (hjl : 16 < l) (hl : l < 20) :
    rawD stage1 recipe1 i 16 l ≤ D stage2 i 16 l := by
  interval_cases i
  · exact zY269 l hjl hl
  · exact zY270 l hjl hl
  · exact zY271 l hjl hl
  · exact zY272 l hjl hl
  · exact zY273 l hjl hl
  · exact zY274 l hjl hl
  · exact zY275 l hjl hl
theorem zY277 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage1 recipe1 10 17 l ≤ D stage2 10 17 l := by
  interval_cases l <;> decide +kernel
theorem zY278 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage1 recipe1 11 17 l ≤ D stage2 11 17 l := by
  interval_cases l <;> decide +kernel
theorem zY279 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage1 recipe1 12 17 l ≤ D stage2 12 17 l := by
  interval_cases l <;> decide +kernel
theorem zY280 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage1 recipe1 13 17 l ≤ D stage2 13 17 l := by
  interval_cases l <;> decide +kernel
theorem zY281 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage1 recipe1 14 17 l ≤ D stage2 14 17 l := by
  interval_cases l <;> decide +kernel
theorem zY282 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage1 recipe1 15 17 l ≤ D stage2 15 17 l := by
  interval_cases l <;> decide +kernel
theorem zY283 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage1 recipe1 16 17 l ≤ D stage2 16 17 l := by
  interval_cases l <;> decide +kernel
theorem zY284 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage1 recipe1 17 17 l ≤ D stage2 17 17 l := by
  interval_cases l <;> decide +kernel
theorem zY285 (i l : Nat)
    (hi : 10 ≤ i) (hij : i ≤ 17) (hjl : 17 < l) (hl : l < 20) :
    rawD stage1 recipe1 i 17 l ≤ D stage2 i 17 l := by
  interval_cases i
  · exact zY277 l hjl hl
  · exact zY278 l hjl hl
  · exact zY279 l hjl hl
  · exact zY280 l hjl hl
  · exact zY281 l hjl hl
  · exact zY282 l hjl hl
  · exact zY283 l hjl hl
  · exact zY284 l hjl hl
theorem zY286 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage1 recipe1 10 18 l ≤ D stage2 10 18 l := by
  interval_cases l <;> decide +kernel
theorem zY287 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage1 recipe1 11 18 l ≤ D stage2 11 18 l := by
  interval_cases l <;> decide +kernel
theorem zY288 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage1 recipe1 12 18 l ≤ D stage2 12 18 l := by
  interval_cases l <;> decide +kernel
theorem zY289 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage1 recipe1 13 18 l ≤ D stage2 13 18 l := by
  interval_cases l <;> decide +kernel
theorem zY290 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage1 recipe1 14 18 l ≤ D stage2 14 18 l := by
  interval_cases l <;> decide +kernel
theorem zY291 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage1 recipe1 15 18 l ≤ D stage2 15 18 l := by
  interval_cases l <;> decide +kernel
theorem zY292 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage1 recipe1 16 18 l ≤ D stage2 16 18 l := by
  interval_cases l <;> decide +kernel
theorem zY293 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage1 recipe1 17 18 l ≤ D stage2 17 18 l := by
  interval_cases l <;> decide +kernel
theorem zY294 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage1 recipe1 18 18 l ≤ D stage2 18 18 l := by
  interval_cases l <;> decide +kernel
theorem zY295 (i l : Nat)
    (hi : 10 ≤ i) (hij : i ≤ 18) (hjl : 18 < l) (hl : l < 20) :
    rawD stage1 recipe1 i 18 l ≤ D stage2 i 18 l := by
  interval_cases i
  · exact zY286 l hjl hl
  · exact zY287 l hjl hl
  · exact zY288 l hjl hl
  · exact zY289 l hjl hl
  · exact zY290 l hjl hl
  · exact zY291 l hjl hl
  · exact zY292 l hjl hl
  · exact zY293 l hjl hl
  · exact zY294 l hjl hl

end ZP
end z160

section z161
namespace ZP
set_option maxHeartbeats 3000000

theorem zY296 (i j l : Nat) (hij : i ≤ j) (hjl : j < l) (hl : l < 20) :
    rawD stage1 recipe1 i j l ≤ D stage2 i j l := by
  by_cases hi : i < 10
  · have hqi := nonzero_tolerance_1 ⟨i,hi⟩
    rw [rawD_eq_sum_of_nonzero hqi]
    rw [nonzero_d_sum_1 ⟨i,hi⟩ ⟨j,by omega⟩ ⟨l,hl⟩ hij hjl]
    exact Nat.add_le_add (zY221 i j hij (by omega))
      (zY241 j l hjl hl)
  · have hi' : 10 ≤ i := by omega
    have hj : 10 ≤ j := by omega
    have hj' : j < 19 := by omega
    interval_cases j
    · exact zY243 i l hi' hij hjl hl
    · exact zY246 i l hi' hij hjl hl
    · exact zY250 i l hi' hij hjl hl
    · exact zY255 i l hi' hij hjl hl
    · exact zY261 i l hi' hij hjl hl
    · exact zY268 i l hi' hij hjl hl
    · exact zY276 i l hi' hij hjl hl
    · exact zY285 i l hi' hij hjl hl
    · exact zY295 i l hi' hij hjl hl

theorem _root_.solution : TransitionCertificate stage1 recipe1 stage2 where
  a i j hij := zY180 i.val j.val hij j.isLt
  b i j hij := zY201 i.val j.val hij j.isLt
  m i j hij hn := zY221 i.val j.val hij (by omega)
  p j l hjl := zY241 j.val l.val hjl l.isLt
  d i j l hij hjl := zY296 i.val j.val l.val hij hjl l.isLt
end ZP
end z161
