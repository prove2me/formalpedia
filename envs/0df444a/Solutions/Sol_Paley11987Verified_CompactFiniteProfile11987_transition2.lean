-- Prove2me | solution 1 for Paley11987Verified.CompactFiniteProfile11987.transition2
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-23T05:41:06.553894+00:00
-- url     : https://prove2.me/submissions/b1773f87-3cd3-402c-9758-69062f48b414

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

section z162
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX91 : rawA stage2 recipe2 0 0 ≤ A stage3 0 0 := by
  change maximum ((cases 8 19).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 20674599937926749 1625525984337541404 1625525984337541404)) ≤ 108587214762367117851
  rw [cases_8_1_eq]
  decide +kernel
theorem zX92 : rawA stage2 recipe2 0 1 ≤ A stage3 0 1 := by
  change maximum ((cases 6 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 20674599937926749 1625525984337541404 1625525984337541404)) ≤ 1261150596213531689
  rw [cases_6_0_eq]
  decide +kernel
theorem zX93 : rawA stage2 recipe2 0 2 ≤ A stage3 0 2 := by
  change maximum ((cases 5 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 20674599937926749 1625525984337541404 1625525984337541404)) ≤ 1157777596523897944
  rw [cases_5_0_eq]
  decide +kernel
theorem zX94 : rawA stage2 recipe2 0 3 ≤ A stage3 0 3 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 20674599937926749 1625525984337541404 1625525984337541404)) ≤ 1013055396958410701
  rw [cases_4_0_eq]
  decide +kernel
theorem zX95 : rawA stage2 recipe2 0 4 ≤ A stage3 0 4 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 20674594148790991 1625525984337541404 1512177354544003822)) ≤ 889007548398012613
  rw [cases_3_0_eq]
  decide +kernel
theorem zX96 : rawA stage2 recipe2 0 5 ≤ A stage3 0 5 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 61747765955078292
  rw [cases_3_0_eq]
  decide +kernel
theorem zX97 : rawA stage2 recipe2 0 6 ≤ A stage3 0 6 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 53131798612509228
  rw [cases_2_0_eq]
  decide +kernel
theorem zX98 : rawA stage2 recipe2 0 7 ≤ A stage3 0 7 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 43079836712845320
  rw [cases_1_0_eq]
  decide +kernel
theorem zX99 : rawA stage2 recipe2 0 8 ≤ A stage3 0 8 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1422023548741702 1625525984337541404 45065321753532464)) ≤ 42660706462251060
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z162

section z163
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX100 : rawA stage2 recipe2 1 1 ≤ A stage3 1 1 := by
  change maximum ((cases 6 15).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 20674599937926749 1625525984337541404 1625525984337541404)) ≤ 74244423091899480877
  rw [cases_6_1_eq]
  decide +kernel
theorem zX101 : rawA stage2 recipe2 1 2 ≤ A stage3 1 2 := by
  change maximum ((cases 5 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 20674599937926749 1625525984337541404 1625525984337541404)) ≤ 1157777596523897944
  rw [cases_5_0_eq]
  decide +kernel
theorem zX102 : rawA stage2 recipe2 1 3 ≤ A stage3 1 3 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 20674599937926749 1625525984337541404 1625525984337541404)) ≤ 1013055396958410701
  rw [cases_4_0_eq]
  decide +kernel
theorem zX103 : rawA stage2 recipe2 1 4 ≤ A stage3 1 4 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 20674594148790991 1625525984337541404 1512177354544003822)) ≤ 889007548398012613
  rw [cases_3_0_eq]
  decide +kernel
theorem zX104 : rawA stage2 recipe2 1 5 ≤ A stage3 1 5 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 61747765955078292
  rw [cases_3_0_eq]
  decide +kernel
end ZP
end z163

section z164
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX105 : rawA stage2 recipe2 1 6 ≤ A stage3 1 6 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 53131798612509228
  rw [cases_2_0_eq]
  decide +kernel
theorem zX106 : rawA stage2 recipe2 1 7 ≤ A stage3 1 7 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 43079836712845320
  rw [cases_1_0_eq]
  decide +kernel
theorem zX107 : rawA stage2 recipe2 1 8 ≤ A stage3 1 8 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1422023548741702 1625525984337541404 45065321753532464)) ≤ 42660706462251060
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z164

section z165
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX108 : rawA stage2 recipe2 2 2 ≤ A stage3 2 2 := by
  change maximum ((cases 5 13).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 20674599937926749 1625525984337541404 1625525984337541404)) ≤ 59531990833109901245
  rw [cases_5_1_eq]
  decide +kernel
theorem zX109 : rawA stage2 recipe2 2 3 ≤ A stage3 2 3 := by
  change maximum ((cases 4 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 20674599937926749 1625525984337541404 1625525984337541404)) ≤ 1013055396958410701
  rw [cases_4_0_eq]
  decide +kernel
theorem zX110 : rawA stage2 recipe2 2 4 ≤ A stage3 2 4 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 20674594148790991 1625525984337541404 1512177354544003822)) ≤ 889007548398012613
  rw [cases_3_0_eq]
  decide +kernel
theorem zX111 : rawA stage2 recipe2 2 5 ≤ A stage3 2 5 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 61747765955078292
  rw [cases_3_0_eq]
  decide +kernel
theorem zX112 : rawA stage2 recipe2 2 6 ≤ A stage3 2 6 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 53131798612509228
  rw [cases_2_0_eq]
  decide +kernel
theorem zX113 : rawA stage2 recipe2 2 7 ≤ A stage3 2 7 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 43079836712845320
  rw [cases_1_0_eq]
  decide +kernel
theorem zX114 : rawA stage2 recipe2 2 8 ≤ A stage3 2 8 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1422023548741702 1625525984337541404 45065321753532464)) ≤ 42660706462251060
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z165

section z166
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX115 : rawA stage2 recipe2 3 3 ≤ A stage3 3 3 := by
  change maximum ((cases 4 11).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 20674599937926749 1625525984337541404 1625525984337541404)) ≤ 46403735358782009519
  rw [cases_4_1_eq]
  decide +kernel
theorem zX116 : rawA stage2 recipe2 3 4 ≤ A stage3 3 4 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 20674594148790991 1625525984337541404 1512177354544003822)) ≤ 889007548398012613
  rw [cases_3_0_eq]
  decide +kernel
theorem zX117 : rawA stage2 recipe2 3 5 ≤ A stage3 3 5 := by
  change maximum ((cases 3 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 61747765955078292
  rw [cases_3_0_eq]
  decide +kernel
theorem zX118 : rawA stage2 recipe2 3 6 ≤ A stage3 3 6 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 53131798612509228
  rw [cases_2_0_eq]
  decide +kernel
theorem zX119 : rawA stage2 recipe2 3 7 ≤ A stage3 3 7 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 43079836712845320
  rw [cases_1_0_eq]
  decide +kernel
theorem zX120 : rawA stage2 recipe2 3 8 ≤ A stage3 3 8 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 10 then 0 else
      c.u*0+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1422023548741702 1625525984337541404 45065321753532464)) ≤ 42660706462251060
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z166

section z167
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX121 : rawA stage2 recipe2 4 4 ≤ A stage3 4 4 := by
  change maximum ((cases 3 9).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 11 then 0 else
      c.u*20674594148790991+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 20674594148790991 1625525984337541404 1512177354544003822)) ≤ 33375425343880857239
  rw [cases_3_1_eq]
  decide +kernel
end ZP
end z167

section z168
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX122 : rawA stage2 recipe2 4 5 ≤ A stage3 4 5 := by
  change maximum ((cases 3 9).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 11 then 0 else
      c.u*1435994557094844+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 16750909287944232964
  rw [cases_3_1_eq]
  decide +kernel
theorem zX123 : rawA stage2 recipe2 4 6 ≤ A stage3 4 6 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 11 then 0 else
      c.u*1435994557094844+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 53131798612509228
  rw [cases_2_0_eq]
  decide +kernel
theorem zX124 : rawA stage2 recipe2 4 7 ≤ A stage3 4 7 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 11 then 0 else
      c.u*1435994557094844+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 43079836712845320
  rw [cases_1_0_eq]
  decide +kernel
theorem zX125 : rawA stage2 recipe2 4 8 ≤ A stage3 4 8 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 11 then 0 else
      c.u*1422023548741702+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1422023548741702 1625525984337541404 45065321753532464)) ≤ 42660706462251060
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z168

section z169
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX126 : rawA stage2 recipe2 5 5 ≤ A stage3 5 5 := by
  change maximum ((cases 3 9).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 12 then 0 else
      c.u*19854567479288484+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 16750909287944232964
  rw [cases_3_1_eq]
  decide +kernel
theorem zX127 : rawA stage2 recipe2 5 6 ≤ A stage3 5 6 := by
  change maximum ((cases 2 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 12 then 0 else
      c.u*19854567479288484+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 143788668666382584
  rw [cases_2_0_eq]
  decide +kernel
theorem zX128 : rawA stage2 recipe2 5 7 ≤ A stage3 5 7 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 12 then 0 else
      c.u*19854567479288484+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 92591577251046864
  rw [cases_1_0_eq]
  decide +kernel
theorem zX129 : rawA stage2 recipe2 5 8 ≤ A stage3 5 8 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 12 then 0 else
      c.u*19840596470935342+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1422023548741702 1625525984337541404 45065321753532464)) ≤ 92228331033865172
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z169

section z170
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX130 : rawA stage2 recipe2 6 6 ≤ A stage3 6 6 := by
  change maximum ((cases 2 7).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 12 then 0 else
      c.u*19854567479288484+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 10064043921603231312
  rw [cases_2_1_eq]
  decide +kernel
theorem zX131 : rawA stage2 recipe2 6 7 ≤ A stage3 6 7 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 12 then 0 else
      c.u*19854567479288484+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 92591577251046864
  rw [cases_1_0_eq]
  decide +kernel
theorem zX132 : rawA stage2 recipe2 6 8 ≤ A stage3 6 8 := by
  change maximum ((cases 1 0).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 12 then 0 else
      c.u*19840596470935342+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1422023548741702 1625525984337541404 45065321753532464)) ≤ 92228331033865172
  rw [cases_1_0_eq]
  decide +kernel
end ZP
end z170

section z171
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX133 : rawA stage2 recipe2 7 7 ≤ A stage3 7 7 := by
  change maximum ((cases 1 5).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 12 then 0 else
      c.u*19854567479288484+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1435994557094844 1625525984337541404 45113361329887876)) ≤ 5044945911815469252
  rw [cases_1_1_eq]
  decide +kernel
theorem zX134 : rawA stage2 recipe2 7 8 ≤ A stage3 7 8 := by
  change maximum ((cases 1 5).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 12 then 0 else
      c.u*19840596470935342+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1422023548741702 1625525984337541404 45065321753532464)) ≤ 5044480459894280750
  rw [cases_1_1_eq]
  decide +kernel
end ZP
end z171

section z172
namespace ZP
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
theorem zX135 : rawA stage2 recipe2 8 8 ≤ A stage3 8 8 := by
  change maximum ((cases 1 5).map (fun c : Case =>
    if c.u > 0 ∧ (10 : Nat) = 13 then 0 else
      c.u*19840596470935342+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
        (c.intr+min c.u c.save) (c.ext-c.low) 1422023548741702 1625525984337541404 45065321753532464)) ≤ 5044480459894280750
  rw [cases_1_1_eq]
  decide +kernel
end ZP
end z172

section z197
namespace ZP
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
theorem zY297 (j : Nat) (hij : 0 ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 0 j ≤ A stage3 0 j := by
  interval_cases j
  · exact zX91
  · exact zX92
  · exact zX93
  · exact zX94
  · exact zX95
  · exact zX96
  · exact zX97
  · exact zX98
  · exact zX99
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
theorem zY298 (j : Nat) (hij : 1 ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 1 j ≤ A stage3 1 j := by
  interval_cases j
  · exact zX100
  · exact zX101
  · exact zX102
  · exact zX103
  · exact zX104
  · exact zX105
  · exact zX106
  · exact zX107
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
theorem zY299 (j : Nat) (hij : 2 ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 2 j ≤ A stage3 2 j := by
  interval_cases j
  · exact zX108
  · exact zX109
  · exact zX110
  · exact zX111
  · exact zX112
  · exact zX113
  · exact zX114
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
theorem zY300 (j : Nat) (hij : 3 ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 3 j ≤ A stage3 3 j := by
  interval_cases j
  · exact zX115
  · exact zX116
  · exact zX117
  · exact zX118
  · exact zX119
  · exact zX120
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
theorem zY301 (j : Nat) (hij : 4 ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 4 j ≤ A stage3 4 j := by
  interval_cases j
  · exact zX121
  · exact zX122
  · exact zX123
  · exact zX124
  · exact zX125
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
theorem zY302 (j : Nat) (hij : 5 ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 5 j ≤ A stage3 5 j := by
  interval_cases j
  · exact zX126
  · exact zX127
  · exact zX128
  · exact zX129
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
theorem zY303 (j : Nat) (hij : 6 ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 6 j ≤ A stage3 6 j := by
  interval_cases j
  · exact zX130
  · exact zX131
  · exact zX132
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
theorem zY304 (j : Nat) (hij : 7 ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 7 j ≤ A stage3 7 j := by
  interval_cases j
  · exact zX133
  · exact zX134
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
theorem zY305 (j : Nat) (hij : 8 ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 8 j ≤ A stage3 8 j := by
  interval_cases j
  · exact zX135
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
theorem zY306 (j : Nat) (hij : 9 ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 9 j ≤ A stage3 9 j := by
  interval_cases j <;> decide +kernel
theorem zY307 (j : Nat) (hij : 10 ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 10 j ≤ A stage3 10 j := by
  interval_cases j <;> decide +kernel
theorem zY308 (j : Nat) (hij : 11 ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 11 j ≤ A stage3 11 j := by
  interval_cases j <;> decide +kernel
theorem zY309 (j : Nat) (hij : 12 ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 12 j ≤ A stage3 12 j := by
  interval_cases j <;> decide +kernel
theorem zY310 (j : Nat) (hij : 13 ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 13 j ≤ A stage3 13 j := by
  interval_cases j <;> decide +kernel
theorem zY311 (j : Nat) (hij : 14 ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 14 j ≤ A stage3 14 j := by
  interval_cases j <;> decide +kernel
theorem zY312 (j : Nat) (hij : 15 ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 15 j ≤ A stage3 15 j := by
  interval_cases j <;> decide +kernel
theorem zY313 (j : Nat) (hij : 16 ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 16 j ≤ A stage3 16 j := by
  interval_cases j <;> decide +kernel
theorem zY314 (j : Nat) (hij : 17 ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 17 j ≤ A stage3 17 j := by
  interval_cases j <;> decide +kernel
theorem zY315 (j : Nat) (hij : 18 ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 18 j ≤ A stage3 18 j := by
  interval_cases j <;> decide +kernel
theorem zY316 (j : Nat) (hij : 19 ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 19 j ≤ A stage3 19 j := by
  interval_cases j <;> decide +kernel
theorem zY317 (i j : Nat) (hij : i ≤ j) (hj : j < 20) :
    rawA stage2 recipe2 i j ≤ A stage3 i j := by
  have hi : i < 20 := Nat.lt_of_le_of_lt hij hj
  interval_cases i
  · exact zY297 j hij hj
  · exact zY298 j hij hj
  · exact zY299 j hij hj
  · exact zY300 j hij hj
  · exact zY301 j hij hj
  · exact zY302 j hij hj
  · exact zY303 j hij hj
  · exact zY304 j hij hj
  · exact zY305 j hij hj
  · exact zY306 j hij hj
  · exact zY307 j hij hj
  · exact zY308 j hij hj
  · exact zY309 j hij hj
  · exact zY310 j hij hj
  · exact zY311 j hij hj
  · exact zY312 j hij hj
  · exact zY313 j hij hj
  · exact zY314 j hij hj
  · exact zY315 j hij hj
  · exact zY316 j hij hj
theorem zY318 (j : Nat) (hij : 0 ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 0 j ≤ B stage3 0 j := by
  interval_cases j <;> decide +kernel
theorem zY319 (j : Nat) (hij : 1 ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 1 j ≤ B stage3 1 j := by
  interval_cases j <;> decide +kernel
theorem zY320 (j : Nat) (hij : 2 ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 2 j ≤ B stage3 2 j := by
  interval_cases j <;> decide +kernel
theorem zY321 (j : Nat) (hij : 3 ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 3 j ≤ B stage3 3 j := by
  interval_cases j <;> decide +kernel
theorem zY322 (j : Nat) (hij : 4 ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 4 j ≤ B stage3 4 j := by
  interval_cases j <;> decide +kernel
theorem zY323 (j : Nat) (hij : 5 ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 5 j ≤ B stage3 5 j := by
  interval_cases j <;> decide +kernel
theorem zY324 (j : Nat) (hij : 6 ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 6 j ≤ B stage3 6 j := by
  interval_cases j <;> decide +kernel
theorem zY325 (j : Nat) (hij : 7 ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 7 j ≤ B stage3 7 j := by
  interval_cases j <;> decide +kernel
theorem zY326 (j : Nat) (hij : 8 ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 8 j ≤ B stage3 8 j := by
  interval_cases j <;> decide +kernel
theorem zY327 (j : Nat) (hij : 9 ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 9 j ≤ B stage3 9 j := by
  interval_cases j <;> decide +kernel
theorem zY328 (j : Nat) (hij : 10 ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 10 j ≤ B stage3 10 j := by
  interval_cases j <;> decide +kernel
theorem zY329 (j : Nat) (hij : 11 ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 11 j ≤ B stage3 11 j := by
  interval_cases j <;> decide +kernel
theorem zY330 (j : Nat) (hij : 12 ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 12 j ≤ B stage3 12 j := by
  interval_cases j <;> decide +kernel
theorem zY331 (j : Nat) (hij : 13 ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 13 j ≤ B stage3 13 j := by
  interval_cases j <;> decide +kernel
theorem zY332 (j : Nat) (hij : 14 ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 14 j ≤ B stage3 14 j := by
  interval_cases j <;> decide +kernel
theorem zY333 (j : Nat) (hij : 15 ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 15 j ≤ B stage3 15 j := by
  interval_cases j <;> decide +kernel
theorem zY334 (j : Nat) (hij : 16 ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 16 j ≤ B stage3 16 j := by
  interval_cases j <;> decide +kernel
theorem zY335 (j : Nat) (hij : 17 ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 17 j ≤ B stage3 17 j := by
  interval_cases j <;> decide +kernel
theorem zY336 (j : Nat) (hij : 18 ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 18 j ≤ B stage3 18 j := by
  interval_cases j <;> decide +kernel
theorem zY337 (j : Nat) (hij : 19 ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 19 j ≤ B stage3 19 j := by
  interval_cases j <;> decide +kernel
theorem zY338 (i j : Nat) (hij : i ≤ j) (hj : j < 20) :
    rawB stage2 recipe2 i j ≤ B stage3 i j := by
  have hi : i < 20 := Nat.lt_of_le_of_lt hij hj
  interval_cases i
  · exact zY318 j hij hj
  · exact zY319 j hij hj
  · exact zY320 j hij hj
  · exact zY321 j hij hj
  · exact zY322 j hij hj
  · exact zY323 j hij hj
  · exact zY324 j hij hj
  · exact zY325 j hij hj
  · exact zY326 j hij hj
  · exact zY327 j hij hj
  · exact zY328 j hij hj
  · exact zY329 j hij hj
  · exact zY330 j hij hj
  · exact zY331 j hij hj
  · exact zY332 j hij hj
  · exact zY333 j hij hj
  · exact zY334 j hij hj
  · exact zY335 j hij hj
  · exact zY336 j hij hj
  · exact zY337 j hij hj
theorem zY339 (j : Nat) (hij : 0 ≤ j) (hj : j < 19) :
    rawM stage2 recipe2 0 j ≤ M stage3 0 j := by
  interval_cases j <;> decide +kernel
theorem zY340 (j : Nat) (hij : 1 ≤ j) (hj : j < 19) :
    rawM stage2 recipe2 1 j ≤ M stage3 1 j := by
  interval_cases j <;> decide +kernel
theorem zY341 (j : Nat) (hij : 2 ≤ j) (hj : j < 19) :
    rawM stage2 recipe2 2 j ≤ M stage3 2 j := by
  interval_cases j <;> decide +kernel
theorem zY342 (j : Nat) (hij : 3 ≤ j) (hj : j < 19) :
    rawM stage2 recipe2 3 j ≤ M stage3 3 j := by
  interval_cases j <;> decide +kernel
theorem zY343 (j : Nat) (hij : 4 ≤ j) (hj : j < 19) :
    rawM stage2 recipe2 4 j ≤ M stage3 4 j := by
  interval_cases j <;> decide +kernel
theorem zY344 (j : Nat) (hij : 5 ≤ j) (hj : j < 19) :
    rawM stage2 recipe2 5 j ≤ M stage3 5 j := by
  interval_cases j <;> decide +kernel
theorem zY345 (j : Nat) (hij : 6 ≤ j) (hj : j < 19) :
    rawM stage2 recipe2 6 j ≤ M stage3 6 j := by
  interval_cases j <;> decide +kernel
theorem zY346 (j : Nat) (hij : 7 ≤ j) (hj : j < 19) :
    rawM stage2 recipe2 7 j ≤ M stage3 7 j := by
  interval_cases j <;> decide +kernel
theorem zY347 (j : Nat) (hij : 8 ≤ j) (hj : j < 19) :
    rawM stage2 recipe2 8 j ≤ M stage3 8 j := by
  interval_cases j <;> decide +kernel
theorem zY348 (j : Nat) (hij : 9 ≤ j) (hj : j < 19) :
    rawM stage2 recipe2 9 j ≤ M stage3 9 j := by
  interval_cases j <;> decide +kernel
theorem zY349 (j : Nat) (hij : 10 ≤ j) (hj : j < 19) :
    rawM stage2 recipe2 10 j ≤ M stage3 10 j := by
  interval_cases j <;> decide +kernel
theorem zY350 (j : Nat) (hij : 11 ≤ j) (hj : j < 19) :
    rawM stage2 recipe2 11 j ≤ M stage3 11 j := by
  interval_cases j <;> decide +kernel
theorem zY351 (j : Nat) (hij : 12 ≤ j) (hj : j < 19) :
    rawM stage2 recipe2 12 j ≤ M stage3 12 j := by
  interval_cases j <;> decide +kernel
theorem zY352 (j : Nat) (hij : 13 ≤ j) (hj : j < 19) :
    rawM stage2 recipe2 13 j ≤ M stage3 13 j := by
  interval_cases j <;> decide +kernel
theorem zY353 (j : Nat) (hij : 14 ≤ j) (hj : j < 19) :
    rawM stage2 recipe2 14 j ≤ M stage3 14 j := by
  interval_cases j <;> decide +kernel
theorem zY354 (j : Nat) (hij : 15 ≤ j) (hj : j < 19) :
    rawM stage2 recipe2 15 j ≤ M stage3 15 j := by
  interval_cases j <;> decide +kernel
theorem zY355 (j : Nat) (hij : 16 ≤ j) (hj : j < 19) :
    rawM stage2 recipe2 16 j ≤ M stage3 16 j := by
  interval_cases j <;> decide +kernel
theorem zY356 (j : Nat) (hij : 17 ≤ j) (hj : j < 19) :
    rawM stage2 recipe2 17 j ≤ M stage3 17 j := by
  interval_cases j <;> decide +kernel
theorem zY357 (j : Nat) (hij : 18 ≤ j) (hj : j < 19) :
    rawM stage2 recipe2 18 j ≤ M stage3 18 j := by
  interval_cases j <;> decide +kernel
theorem zY358 (i j : Nat) (hij : i ≤ j) (hj : j < 19) :
    rawM stage2 recipe2 i j ≤ M stage3 i j := by
  have hi : i < 19 := Nat.lt_of_le_of_lt hij hj
  interval_cases i
  · exact zY339 j hij hj
  · exact zY340 j hij hj
  · exact zY341 j hij hj
  · exact zY342 j hij hj
  · exact zY343 j hij hj
  · exact zY344 j hij hj
  · exact zY345 j hij hj
  · exact zY346 j hij hj
  · exact zY347 j hij hj
  · exact zY348 j hij hj
  · exact zY349 j hij hj
  · exact zY350 j hij hj
  · exact zY351 j hij hj
  · exact zY352 j hij hj
  · exact zY353 j hij hj
  · exact zY354 j hij hj
  · exact zY355 j hij hj
  · exact zY356 j hij hj
  · exact zY357 j hij hj
theorem zY359 (l : Nat) (hjl : 0 < l) (hl : l < 20) :
    rawP stage2 recipe2 0 l ≤ P stage3 0 l := by
  interval_cases l
  · change rawA stage2 recipe2 1 1 ≤ A stage3 1 1
    exact zX100
  · change rawA stage2 recipe2 1 2 ≤ A stage3 1 2
    exact zX101
  · change rawA stage2 recipe2 1 3 ≤ A stage3 1 3
    exact zX102
  · change rawA stage2 recipe2 1 4 ≤ A stage3 1 4
    exact zX103
  · change rawA stage2 recipe2 1 5 ≤ A stage3 1 5
    exact zX104
  · change rawA stage2 recipe2 1 6 ≤ A stage3 1 6
    exact zX105
  · change rawA stage2 recipe2 1 7 ≤ A stage3 1 7
    exact zX106
  · change rawA stage2 recipe2 1 8 ≤ A stage3 1 8
    exact zX107
  · change rawA stage2 recipe2 1 9 ≤ A stage3 1 9
    decide +kernel
  · change rawA stage2 recipe2 1 10 ≤ A stage3 1 10
    decide +kernel
  · change rawA stage2 recipe2 1 11 ≤ A stage3 1 11
    decide +kernel
  · change rawA stage2 recipe2 1 12 ≤ A stage3 1 12
    decide +kernel
  · change rawA stage2 recipe2 1 13 ≤ A stage3 1 13
    decide +kernel
  · change rawA stage2 recipe2 1 14 ≤ A stage3 1 14
    decide +kernel
  · change rawA stage2 recipe2 1 15 ≤ A stage3 1 15
    decide +kernel
  · change rawA stage2 recipe2 1 16 ≤ A stage3 1 16
    decide +kernel
  · change rawA stage2 recipe2 1 17 ≤ A stage3 1 17
    decide +kernel
  · change rawA stage2 recipe2 1 18 ≤ A stage3 1 18
    decide +kernel
  · change rawA stage2 recipe2 1 19 ≤ A stage3 1 19
    decide +kernel
theorem zY360 (l : Nat) (hjl : 1 < l) (hl : l < 20) :
    rawP stage2 recipe2 1 l ≤ P stage3 1 l := by
  interval_cases l
  · change rawA stage2 recipe2 2 2 ≤ A stage3 2 2
    exact zX108
  · change rawA stage2 recipe2 2 3 ≤ A stage3 2 3
    exact zX109
  · change rawA stage2 recipe2 2 4 ≤ A stage3 2 4
    exact zX110
  · change rawA stage2 recipe2 2 5 ≤ A stage3 2 5
    exact zX111
  · change rawA stage2 recipe2 2 6 ≤ A stage3 2 6
    exact zX112
  · change rawA stage2 recipe2 2 7 ≤ A stage3 2 7
    exact zX113
  · change rawA stage2 recipe2 2 8 ≤ A stage3 2 8
    exact zX114
  · change rawA stage2 recipe2 2 9 ≤ A stage3 2 9
    decide +kernel
  · change rawA stage2 recipe2 2 10 ≤ A stage3 2 10
    decide +kernel
  · change rawA stage2 recipe2 2 11 ≤ A stage3 2 11
    decide +kernel
  · change rawA stage2 recipe2 2 12 ≤ A stage3 2 12
    decide +kernel
  · change rawA stage2 recipe2 2 13 ≤ A stage3 2 13
    decide +kernel
  · change rawA stage2 recipe2 2 14 ≤ A stage3 2 14
    decide +kernel
  · change rawA stage2 recipe2 2 15 ≤ A stage3 2 15
    decide +kernel
  · change rawA stage2 recipe2 2 16 ≤ A stage3 2 16
    decide +kernel
  · change rawA stage2 recipe2 2 17 ≤ A stage3 2 17
    decide +kernel
  · change rawA stage2 recipe2 2 18 ≤ A stage3 2 18
    decide +kernel
  · change rawA stage2 recipe2 2 19 ≤ A stage3 2 19
    decide +kernel
theorem zY361 (l : Nat) (hjl : 2 < l) (hl : l < 20) :
    rawP stage2 recipe2 2 l ≤ P stage3 2 l := by
  interval_cases l
  · change rawA stage2 recipe2 3 3 ≤ A stage3 3 3
    exact zX115
  · change rawA stage2 recipe2 3 4 ≤ A stage3 3 4
    exact zX116
  · change rawA stage2 recipe2 3 5 ≤ A stage3 3 5
    exact zX117
  · change rawA stage2 recipe2 3 6 ≤ A stage3 3 6
    exact zX118
  · change rawA stage2 recipe2 3 7 ≤ A stage3 3 7
    exact zX119
  · change rawA stage2 recipe2 3 8 ≤ A stage3 3 8
    exact zX120
  · change rawA stage2 recipe2 3 9 ≤ A stage3 3 9
    decide +kernel
  · change rawA stage2 recipe2 3 10 ≤ A stage3 3 10
    decide +kernel
  · change rawA stage2 recipe2 3 11 ≤ A stage3 3 11
    decide +kernel
  · change rawA stage2 recipe2 3 12 ≤ A stage3 3 12
    decide +kernel
  · change rawA stage2 recipe2 3 13 ≤ A stage3 3 13
    decide +kernel
  · change rawA stage2 recipe2 3 14 ≤ A stage3 3 14
    decide +kernel
  · change rawA stage2 recipe2 3 15 ≤ A stage3 3 15
    decide +kernel
  · change rawA stage2 recipe2 3 16 ≤ A stage3 3 16
    decide +kernel
  · change rawA stage2 recipe2 3 17 ≤ A stage3 3 17
    decide +kernel
  · change rawA stage2 recipe2 3 18 ≤ A stage3 3 18
    decide +kernel
  · change rawA stage2 recipe2 3 19 ≤ A stage3 3 19
    decide +kernel
theorem zY362 (l : Nat) (hjl : 3 < l) (hl : l < 20) :
    rawP stage2 recipe2 3 l ≤ P stage3 3 l := by
  interval_cases l
  · change rawA stage2 recipe2 4 4 ≤ A stage3 4 4
    exact zX121
  · change rawA stage2 recipe2 4 5 ≤ A stage3 4 5
    exact zX122
  · change rawA stage2 recipe2 4 6 ≤ A stage3 4 6
    exact zX123
  · change rawA stage2 recipe2 4 7 ≤ A stage3 4 7
    exact zX124
  · change rawA stage2 recipe2 4 8 ≤ A stage3 4 8
    exact zX125
  · change rawA stage2 recipe2 4 9 ≤ A stage3 4 9
    decide +kernel
  · change rawA stage2 recipe2 4 10 ≤ A stage3 4 10
    decide +kernel
  · change rawA stage2 recipe2 4 11 ≤ A stage3 4 11
    decide +kernel
  · change rawA stage2 recipe2 4 12 ≤ A stage3 4 12
    decide +kernel
  · change rawA stage2 recipe2 4 13 ≤ A stage3 4 13
    decide +kernel
  · change rawA stage2 recipe2 4 14 ≤ A stage3 4 14
    decide +kernel
  · change rawA stage2 recipe2 4 15 ≤ A stage3 4 15
    decide +kernel
  · change rawA stage2 recipe2 4 16 ≤ A stage3 4 16
    decide +kernel
  · change rawA stage2 recipe2 4 17 ≤ A stage3 4 17
    decide +kernel
  · change rawA stage2 recipe2 4 18 ≤ A stage3 4 18
    decide +kernel
  · change rawA stage2 recipe2 4 19 ≤ A stage3 4 19
    decide +kernel
theorem zY363 (l : Nat) (hjl : 4 < l) (hl : l < 20) :
    rawP stage2 recipe2 4 l ≤ P stage3 4 l := by
  interval_cases l
  · change rawA stage2 recipe2 5 5 ≤ A stage3 5 5
    exact zX126
  · change rawA stage2 recipe2 5 6 ≤ A stage3 5 6
    exact zX127
  · change rawA stage2 recipe2 5 7 ≤ A stage3 5 7
    exact zX128
  · change rawA stage2 recipe2 5 8 ≤ A stage3 5 8
    exact zX129
  · change rawA stage2 recipe2 5 9 ≤ A stage3 5 9
    decide +kernel
  · change rawA stage2 recipe2 5 10 ≤ A stage3 5 10
    decide +kernel
  · change rawA stage2 recipe2 5 11 ≤ A stage3 5 11
    decide +kernel
  · change rawA stage2 recipe2 5 12 ≤ A stage3 5 12
    decide +kernel
  · change rawA stage2 recipe2 5 13 ≤ A stage3 5 13
    decide +kernel
  · change rawA stage2 recipe2 5 14 ≤ A stage3 5 14
    decide +kernel
  · change rawA stage2 recipe2 5 15 ≤ A stage3 5 15
    decide +kernel
  · change rawA stage2 recipe2 5 16 ≤ A stage3 5 16
    decide +kernel
  · change rawA stage2 recipe2 5 17 ≤ A stage3 5 17
    decide +kernel
  · change rawA stage2 recipe2 5 18 ≤ A stage3 5 18
    decide +kernel
  · change rawA stage2 recipe2 5 19 ≤ A stage3 5 19
    decide +kernel
theorem zY364 (l : Nat) (hjl : 5 < l) (hl : l < 20) :
    rawP stage2 recipe2 5 l ≤ P stage3 5 l := by
  interval_cases l
  · change rawA stage2 recipe2 6 6 ≤ A stage3 6 6
    exact zX130
  · change rawA stage2 recipe2 6 7 ≤ A stage3 6 7
    exact zX131
  · change rawA stage2 recipe2 6 8 ≤ A stage3 6 8
    exact zX132
  · change rawA stage2 recipe2 6 9 ≤ A stage3 6 9
    decide +kernel
  · change rawA stage2 recipe2 6 10 ≤ A stage3 6 10
    decide +kernel
  · change rawA stage2 recipe2 6 11 ≤ A stage3 6 11
    decide +kernel
  · change rawA stage2 recipe2 6 12 ≤ A stage3 6 12
    decide +kernel
  · change rawA stage2 recipe2 6 13 ≤ A stage3 6 13
    decide +kernel
  · change rawA stage2 recipe2 6 14 ≤ A stage3 6 14
    decide +kernel
  · change rawA stage2 recipe2 6 15 ≤ A stage3 6 15
    decide +kernel
  · change rawA stage2 recipe2 6 16 ≤ A stage3 6 16
    decide +kernel
  · change rawA stage2 recipe2 6 17 ≤ A stage3 6 17
    decide +kernel
  · change rawA stage2 recipe2 6 18 ≤ A stage3 6 18
    decide +kernel
  · change rawA stage2 recipe2 6 19 ≤ A stage3 6 19
    decide +kernel
theorem zY365 (l : Nat) (hjl : 6 < l) (hl : l < 20) :
    rawP stage2 recipe2 6 l ≤ P stage3 6 l := by
  interval_cases l
  · change rawA stage2 recipe2 7 7 ≤ A stage3 7 7
    exact zX133
  · change rawA stage2 recipe2 7 8 ≤ A stage3 7 8
    exact zX134
  · change rawA stage2 recipe2 7 9 ≤ A stage3 7 9
    decide +kernel
  · change rawA stage2 recipe2 7 10 ≤ A stage3 7 10
    decide +kernel
  · change rawA stage2 recipe2 7 11 ≤ A stage3 7 11
    decide +kernel
  · change rawA stage2 recipe2 7 12 ≤ A stage3 7 12
    decide +kernel
  · change rawA stage2 recipe2 7 13 ≤ A stage3 7 13
    decide +kernel
  · change rawA stage2 recipe2 7 14 ≤ A stage3 7 14
    decide +kernel
  · change rawA stage2 recipe2 7 15 ≤ A stage3 7 15
    decide +kernel
  · change rawA stage2 recipe2 7 16 ≤ A stage3 7 16
    decide +kernel
  · change rawA stage2 recipe2 7 17 ≤ A stage3 7 17
    decide +kernel
  · change rawA stage2 recipe2 7 18 ≤ A stage3 7 18
    decide +kernel
  · change rawA stage2 recipe2 7 19 ≤ A stage3 7 19
    decide +kernel
theorem zY366 (l : Nat) (hjl : 7 < l) (hl : l < 20) :
    rawP stage2 recipe2 7 l ≤ P stage3 7 l := by
  interval_cases l
  · change rawA stage2 recipe2 8 8 ≤ A stage3 8 8
    exact zX135
  · change rawA stage2 recipe2 8 9 ≤ A stage3 8 9
    decide +kernel
  · change rawA stage2 recipe2 8 10 ≤ A stage3 8 10
    decide +kernel
  · change rawA stage2 recipe2 8 11 ≤ A stage3 8 11
    decide +kernel
  · change rawA stage2 recipe2 8 12 ≤ A stage3 8 12
    decide +kernel
  · change rawA stage2 recipe2 8 13 ≤ A stage3 8 13
    decide +kernel
  · change rawA stage2 recipe2 8 14 ≤ A stage3 8 14
    decide +kernel
  · change rawA stage2 recipe2 8 15 ≤ A stage3 8 15
    decide +kernel
  · change rawA stage2 recipe2 8 16 ≤ A stage3 8 16
    decide +kernel
  · change rawA stage2 recipe2 8 17 ≤ A stage3 8 17
    decide +kernel
  · change rawA stage2 recipe2 8 18 ≤ A stage3 8 18
    decide +kernel
  · change rawA stage2 recipe2 8 19 ≤ A stage3 8 19
    decide +kernel
theorem zY367 (l : Nat) (hjl : 8 < l) (hl : l < 20) :
    rawP stage2 recipe2 8 l ≤ P stage3 8 l := by
  interval_cases l
  · change rawA stage2 recipe2 9 9 ≤ A stage3 9 9
    decide +kernel
  · change rawA stage2 recipe2 9 10 ≤ A stage3 9 10
    decide +kernel
  · change rawA stage2 recipe2 9 11 ≤ A stage3 9 11
    decide +kernel
  · change rawA stage2 recipe2 9 12 ≤ A stage3 9 12
    decide +kernel
  · change rawA stage2 recipe2 9 13 ≤ A stage3 9 13
    decide +kernel
  · change rawA stage2 recipe2 9 14 ≤ A stage3 9 14
    decide +kernel
  · change rawA stage2 recipe2 9 15 ≤ A stage3 9 15
    decide +kernel
  · change rawA stage2 recipe2 9 16 ≤ A stage3 9 16
    decide +kernel
  · change rawA stage2 recipe2 9 17 ≤ A stage3 9 17
    decide +kernel
  · change rawA stage2 recipe2 9 18 ≤ A stage3 9 18
    decide +kernel
  · change rawA stage2 recipe2 9 19 ≤ A stage3 9 19
    decide +kernel
theorem zY368 (l : Nat) (hjl : 9 < l) (hl : l < 20) :
    rawP stage2 recipe2 9 l ≤ P stage3 9 l := by
  interval_cases l
  · change rawA stage2 recipe2 10 10 ≤ A stage3 10 10
    decide +kernel
  · change rawA stage2 recipe2 10 11 ≤ A stage3 10 11
    decide +kernel
  · change rawA stage2 recipe2 10 12 ≤ A stage3 10 12
    decide +kernel
  · change rawA stage2 recipe2 10 13 ≤ A stage3 10 13
    decide +kernel
  · change rawA stage2 recipe2 10 14 ≤ A stage3 10 14
    decide +kernel
  · change rawA stage2 recipe2 10 15 ≤ A stage3 10 15
    decide +kernel
  · change rawA stage2 recipe2 10 16 ≤ A stage3 10 16
    decide +kernel
  · change rawA stage2 recipe2 10 17 ≤ A stage3 10 17
    decide +kernel
  · change rawA stage2 recipe2 10 18 ≤ A stage3 10 18
    decide +kernel
  · change rawA stage2 recipe2 10 19 ≤ A stage3 10 19
    decide +kernel
theorem zY369 (l : Nat) (hjl : 10 < l) (hl : l < 20) :
    rawP stage2 recipe2 10 l ≤ P stage3 10 l := by
  interval_cases l
  · change rawA stage2 recipe2 11 11 ≤ A stage3 11 11
    decide +kernel
  · change rawA stage2 recipe2 11 12 ≤ A stage3 11 12
    decide +kernel
  · change rawA stage2 recipe2 11 13 ≤ A stage3 11 13
    decide +kernel
  · change rawA stage2 recipe2 11 14 ≤ A stage3 11 14
    decide +kernel
  · change rawA stage2 recipe2 11 15 ≤ A stage3 11 15
    decide +kernel
  · change rawA stage2 recipe2 11 16 ≤ A stage3 11 16
    decide +kernel
  · change rawA stage2 recipe2 11 17 ≤ A stage3 11 17
    decide +kernel
  · change rawA stage2 recipe2 11 18 ≤ A stage3 11 18
    decide +kernel
  · change rawA stage2 recipe2 11 19 ≤ A stage3 11 19
    decide +kernel
theorem zY370 (l : Nat) (hjl : 11 < l) (hl : l < 20) :
    rawP stage2 recipe2 11 l ≤ P stage3 11 l := by
  interval_cases l
  · change rawA stage2 recipe2 12 12 ≤ A stage3 12 12
    decide +kernel
  · change rawA stage2 recipe2 12 13 ≤ A stage3 12 13
    decide +kernel
  · change rawA stage2 recipe2 12 14 ≤ A stage3 12 14
    decide +kernel
  · change rawA stage2 recipe2 12 15 ≤ A stage3 12 15
    decide +kernel
  · change rawA stage2 recipe2 12 16 ≤ A stage3 12 16
    decide +kernel
  · change rawA stage2 recipe2 12 17 ≤ A stage3 12 17
    decide +kernel
  · change rawA stage2 recipe2 12 18 ≤ A stage3 12 18
    decide +kernel
  · change rawA stage2 recipe2 12 19 ≤ A stage3 12 19
    decide +kernel
theorem zY371 (l : Nat) (hjl : 12 < l) (hl : l < 20) :
    rawP stage2 recipe2 12 l ≤ P stage3 12 l := by
  interval_cases l
  · change rawA stage2 recipe2 13 13 ≤ A stage3 13 13
    decide +kernel
  · change rawA stage2 recipe2 13 14 ≤ A stage3 13 14
    decide +kernel
  · change rawA stage2 recipe2 13 15 ≤ A stage3 13 15
    decide +kernel
  · change rawA stage2 recipe2 13 16 ≤ A stage3 13 16
    decide +kernel
  · change rawA stage2 recipe2 13 17 ≤ A stage3 13 17
    decide +kernel
  · change rawA stage2 recipe2 13 18 ≤ A stage3 13 18
    decide +kernel
  · change rawA stage2 recipe2 13 19 ≤ A stage3 13 19
    decide +kernel
theorem zY372 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawP stage2 recipe2 13 l ≤ P stage3 13 l := by
  interval_cases l
  · change rawA stage2 recipe2 14 14 ≤ A stage3 14 14
    decide +kernel
  · change rawA stage2 recipe2 14 15 ≤ A stage3 14 15
    decide +kernel
  · change rawA stage2 recipe2 14 16 ≤ A stage3 14 16
    decide +kernel
  · change rawA stage2 recipe2 14 17 ≤ A stage3 14 17
    decide +kernel
  · change rawA stage2 recipe2 14 18 ≤ A stage3 14 18
    decide +kernel
  · change rawA stage2 recipe2 14 19 ≤ A stage3 14 19
    decide +kernel
theorem zY373 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawP stage2 recipe2 14 l ≤ P stage3 14 l := by
  interval_cases l
  · change rawA stage2 recipe2 15 15 ≤ A stage3 15 15
    decide +kernel
  · change rawA stage2 recipe2 15 16 ≤ A stage3 15 16
    decide +kernel
  · change rawA stage2 recipe2 15 17 ≤ A stage3 15 17
    decide +kernel
  · change rawA stage2 recipe2 15 18 ≤ A stage3 15 18
    decide +kernel
  · change rawA stage2 recipe2 15 19 ≤ A stage3 15 19
    decide +kernel
theorem zY374 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawP stage2 recipe2 15 l ≤ P stage3 15 l := by
  interval_cases l
  · change rawA stage2 recipe2 16 16 ≤ A stage3 16 16
    decide +kernel
  · change rawA stage2 recipe2 16 17 ≤ A stage3 16 17
    decide +kernel
  · change rawA stage2 recipe2 16 18 ≤ A stage3 16 18
    decide +kernel
  · change rawA stage2 recipe2 16 19 ≤ A stage3 16 19
    decide +kernel
theorem zY375 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawP stage2 recipe2 16 l ≤ P stage3 16 l := by
  interval_cases l
  · change rawA stage2 recipe2 17 17 ≤ A stage3 17 17
    decide +kernel
  · change rawA stage2 recipe2 17 18 ≤ A stage3 17 18
    decide +kernel
  · change rawA stage2 recipe2 17 19 ≤ A stage3 17 19
    decide +kernel
theorem zY376 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawP stage2 recipe2 17 l ≤ P stage3 17 l := by
  interval_cases l
  · change rawA stage2 recipe2 18 18 ≤ A stage3 18 18
    decide +kernel
  · change rawA stage2 recipe2 18 19 ≤ A stage3 18 19
    decide +kernel
theorem zY377 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawP stage2 recipe2 18 l ≤ P stage3 18 l := by
  interval_cases l
  · change rawA stage2 recipe2 19 19 ≤ A stage3 19 19
    decide +kernel
theorem zY378 (j l : Nat) (hjl : j < l) (hl : l < 20) :
    rawP stage2 recipe2 j l ≤ P stage3 j l := by
  have hj : j < 19 := by omega
  interval_cases j
  · exact zY359 l hjl hl
  · exact zY360 l hjl hl
  · exact zY361 l hjl hl
  · exact zY362 l hjl hl
  · exact zY363 l hjl hl
  · exact zY364 l hjl hl
  · exact zY365 l hjl hl
  · exact zY366 l hjl hl
  · exact zY367 l hjl hl
  · exact zY368 l hjl hl
  · exact zY369 l hjl hl
  · exact zY370 l hjl hl
  · exact zY371 l hjl hl
  · exact zY372 l hjl hl
  · exact zY373 l hjl hl
  · exact zY374 l hjl hl
  · exact zY375 l hjl hl
  · exact zY376 l hjl hl
  · exact zY377 l hjl hl

theorem nonzero_tolerance_2 : ∀ i : Fin 9,
    (recipe2[i.val]?.getD default).tol ≠ 0 := by decide +kernel

theorem nonzero_d_sum_2 : ∀ (i : Fin 9) (j l : Fin 20),
    i.val ≤ j.val → j.val < l.val →
    D stage3 i.val j.val l.val = M stage3 i.val j.val + P stage3 j.val l.val := by
  decide +kernel

theorem zY379 (l : Nat) (hjl : 9 < l) (hl : l < 20) :
    rawD stage2 recipe2 9 9 l ≤ D stage3 9 9 l := by
  interval_cases l <;> decide +kernel
theorem zY380 (i l : Nat)
    (hi : 9 ≤ i) (hij : i ≤ 9) (hjl : 9 < l) (hl : l < 20) :
    rawD stage2 recipe2 i 9 l ≤ D stage3 i 9 l := by
  interval_cases i
  · exact zY379 l hjl hl
theorem zY381 (l : Nat) (hjl : 10 < l) (hl : l < 20) :
    rawD stage2 recipe2 9 10 l ≤ D stage3 9 10 l := by
  interval_cases l <;> decide +kernel
theorem zY382 (l : Nat) (hjl : 10 < l) (hl : l < 20) :
    rawD stage2 recipe2 10 10 l ≤ D stage3 10 10 l := by
  interval_cases l <;> decide +kernel
theorem zY383 (i l : Nat)
    (hi : 9 ≤ i) (hij : i ≤ 10) (hjl : 10 < l) (hl : l < 20) :
    rawD stage2 recipe2 i 10 l ≤ D stage3 i 10 l := by
  interval_cases i
  · exact zY381 l hjl hl
  · exact zY382 l hjl hl
theorem zY384 (l : Nat) (hjl : 11 < l) (hl : l < 20) :
    rawD stage2 recipe2 9 11 l ≤ D stage3 9 11 l := by
  interval_cases l <;> decide +kernel
theorem zY385 (l : Nat) (hjl : 11 < l) (hl : l < 20) :
    rawD stage2 recipe2 10 11 l ≤ D stage3 10 11 l := by
  interval_cases l <;> decide +kernel
theorem zY386 (l : Nat) (hjl : 11 < l) (hl : l < 20) :
    rawD stage2 recipe2 11 11 l ≤ D stage3 11 11 l := by
  interval_cases l <;> decide +kernel
theorem zY387 (i l : Nat)
    (hi : 9 ≤ i) (hij : i ≤ 11) (hjl : 11 < l) (hl : l < 20) :
    rawD stage2 recipe2 i 11 l ≤ D stage3 i 11 l := by
  interval_cases i
  · exact zY384 l hjl hl
  · exact zY385 l hjl hl
  · exact zY386 l hjl hl
theorem zY388 (l : Nat) (hjl : 12 < l) (hl : l < 20) :
    rawD stage2 recipe2 9 12 l ≤ D stage3 9 12 l := by
  interval_cases l <;> decide +kernel
theorem zY389 (l : Nat) (hjl : 12 < l) (hl : l < 20) :
    rawD stage2 recipe2 10 12 l ≤ D stage3 10 12 l := by
  interval_cases l <;> decide +kernel
theorem zY390 (l : Nat) (hjl : 12 < l) (hl : l < 20) :
    rawD stage2 recipe2 11 12 l ≤ D stage3 11 12 l := by
  interval_cases l <;> decide +kernel
theorem zY391 (l : Nat) (hjl : 12 < l) (hl : l < 20) :
    rawD stage2 recipe2 12 12 l ≤ D stage3 12 12 l := by
  interval_cases l <;> decide +kernel
theorem zY392 (i l : Nat)
    (hi : 9 ≤ i) (hij : i ≤ 12) (hjl : 12 < l) (hl : l < 20) :
    rawD stage2 recipe2 i 12 l ≤ D stage3 i 12 l := by
  interval_cases i
  · exact zY388 l hjl hl
  · exact zY389 l hjl hl
  · exact zY390 l hjl hl
  · exact zY391 l hjl hl
theorem zY393 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawD stage2 recipe2 9 13 l ≤ D stage3 9 13 l := by
  interval_cases l <;> decide +kernel
theorem zY394 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawD stage2 recipe2 10 13 l ≤ D stage3 10 13 l := by
  interval_cases l <;> decide +kernel
theorem zY395 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawD stage2 recipe2 11 13 l ≤ D stage3 11 13 l := by
  interval_cases l <;> decide +kernel
theorem zY396 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawD stage2 recipe2 12 13 l ≤ D stage3 12 13 l := by
  interval_cases l <;> decide +kernel
theorem zY397 (l : Nat) (hjl : 13 < l) (hl : l < 20) :
    rawD stage2 recipe2 13 13 l ≤ D stage3 13 13 l := by
  interval_cases l <;> decide +kernel
theorem zY398 (i l : Nat)
    (hi : 9 ≤ i) (hij : i ≤ 13) (hjl : 13 < l) (hl : l < 20) :
    rawD stage2 recipe2 i 13 l ≤ D stage3 i 13 l := by
  interval_cases i
  · exact zY393 l hjl hl
  · exact zY394 l hjl hl
  · exact zY395 l hjl hl
  · exact zY396 l hjl hl
  · exact zY397 l hjl hl
theorem zY399 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD stage2 recipe2 9 14 l ≤ D stage3 9 14 l := by
  interval_cases l <;> decide +kernel
theorem zY400 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD stage2 recipe2 10 14 l ≤ D stage3 10 14 l := by
  interval_cases l <;> decide +kernel
theorem zY401 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD stage2 recipe2 11 14 l ≤ D stage3 11 14 l := by
  interval_cases l <;> decide +kernel
theorem zY402 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD stage2 recipe2 12 14 l ≤ D stage3 12 14 l := by
  interval_cases l <;> decide +kernel
theorem zY403 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD stage2 recipe2 13 14 l ≤ D stage3 13 14 l := by
  interval_cases l <;> decide +kernel
theorem zY404 (l : Nat) (hjl : 14 < l) (hl : l < 20) :
    rawD stage2 recipe2 14 14 l ≤ D stage3 14 14 l := by
  interval_cases l <;> decide +kernel
theorem zY405 (i l : Nat)
    (hi : 9 ≤ i) (hij : i ≤ 14) (hjl : 14 < l) (hl : l < 20) :
    rawD stage2 recipe2 i 14 l ≤ D stage3 i 14 l := by
  interval_cases i
  · exact zY399 l hjl hl
  · exact zY400 l hjl hl
  · exact zY401 l hjl hl
  · exact zY402 l hjl hl
  · exact zY403 l hjl hl
  · exact zY404 l hjl hl
theorem zY406 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD stage2 recipe2 9 15 l ≤ D stage3 9 15 l := by
  interval_cases l <;> decide +kernel
theorem zY407 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD stage2 recipe2 10 15 l ≤ D stage3 10 15 l := by
  interval_cases l <;> decide +kernel
theorem zY408 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD stage2 recipe2 11 15 l ≤ D stage3 11 15 l := by
  interval_cases l <;> decide +kernel
theorem zY409 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD stage2 recipe2 12 15 l ≤ D stage3 12 15 l := by
  interval_cases l <;> decide +kernel
theorem zY410 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD stage2 recipe2 13 15 l ≤ D stage3 13 15 l := by
  interval_cases l <;> decide +kernel
theorem zY411 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD stage2 recipe2 14 15 l ≤ D stage3 14 15 l := by
  interval_cases l <;> decide +kernel
theorem zY412 (l : Nat) (hjl : 15 < l) (hl : l < 20) :
    rawD stage2 recipe2 15 15 l ≤ D stage3 15 15 l := by
  interval_cases l <;> decide +kernel
theorem zY413 (i l : Nat)
    (hi : 9 ≤ i) (hij : i ≤ 15) (hjl : 15 < l) (hl : l < 20) :
    rawD stage2 recipe2 i 15 l ≤ D stage3 i 15 l := by
  interval_cases i
  · exact zY406 l hjl hl
  · exact zY407 l hjl hl
  · exact zY408 l hjl hl
  · exact zY409 l hjl hl
  · exact zY410 l hjl hl
  · exact zY411 l hjl hl
  · exact zY412 l hjl hl
theorem zY414 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage2 recipe2 9 16 l ≤ D stage3 9 16 l := by
  interval_cases l <;> decide +kernel
theorem zY415 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage2 recipe2 10 16 l ≤ D stage3 10 16 l := by
  interval_cases l <;> decide +kernel
theorem zY416 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage2 recipe2 11 16 l ≤ D stage3 11 16 l := by
  interval_cases l <;> decide +kernel
theorem zY417 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage2 recipe2 12 16 l ≤ D stage3 12 16 l := by
  interval_cases l <;> decide +kernel
theorem zY418 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage2 recipe2 13 16 l ≤ D stage3 13 16 l := by
  interval_cases l <;> decide +kernel
theorem zY419 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage2 recipe2 14 16 l ≤ D stage3 14 16 l := by
  interval_cases l <;> decide +kernel
theorem zY420 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage2 recipe2 15 16 l ≤ D stage3 15 16 l := by
  interval_cases l <;> decide +kernel
theorem zY421 (l : Nat) (hjl : 16 < l) (hl : l < 20) :
    rawD stage2 recipe2 16 16 l ≤ D stage3 16 16 l := by
  interval_cases l <;> decide +kernel
theorem zY422 (i l : Nat)
    (hi : 9 ≤ i) (hij : i ≤ 16) (hjl : 16 < l) (hl : l < 20) :
    rawD stage2 recipe2 i 16 l ≤ D stage3 i 16 l := by
  interval_cases i
  · exact zY414 l hjl hl
  · exact zY415 l hjl hl
  · exact zY416 l hjl hl
  · exact zY417 l hjl hl
  · exact zY418 l hjl hl
  · exact zY419 l hjl hl
  · exact zY420 l hjl hl
  · exact zY421 l hjl hl
theorem zY423 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage2 recipe2 9 17 l ≤ D stage3 9 17 l := by
  interval_cases l <;> decide +kernel
theorem zY424 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage2 recipe2 10 17 l ≤ D stage3 10 17 l := by
  interval_cases l <;> decide +kernel
theorem zY425 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage2 recipe2 11 17 l ≤ D stage3 11 17 l := by
  interval_cases l <;> decide +kernel
theorem zY426 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage2 recipe2 12 17 l ≤ D stage3 12 17 l := by
  interval_cases l <;> decide +kernel
theorem zY427 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage2 recipe2 13 17 l ≤ D stage3 13 17 l := by
  interval_cases l <;> decide +kernel
theorem zY428 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage2 recipe2 14 17 l ≤ D stage3 14 17 l := by
  interval_cases l <;> decide +kernel
theorem zY429 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage2 recipe2 15 17 l ≤ D stage3 15 17 l := by
  interval_cases l <;> decide +kernel
theorem zY430 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage2 recipe2 16 17 l ≤ D stage3 16 17 l := by
  interval_cases l <;> decide +kernel
theorem zY431 (l : Nat) (hjl : 17 < l) (hl : l < 20) :
    rawD stage2 recipe2 17 17 l ≤ D stage3 17 17 l := by
  interval_cases l <;> decide +kernel
theorem zY432 (i l : Nat)
    (hi : 9 ≤ i) (hij : i ≤ 17) (hjl : 17 < l) (hl : l < 20) :
    rawD stage2 recipe2 i 17 l ≤ D stage3 i 17 l := by
  interval_cases i
  · exact zY423 l hjl hl
  · exact zY424 l hjl hl
  · exact zY425 l hjl hl
  · exact zY426 l hjl hl
  · exact zY427 l hjl hl
  · exact zY428 l hjl hl
  · exact zY429 l hjl hl
  · exact zY430 l hjl hl
  · exact zY431 l hjl hl
theorem zY433 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage2 recipe2 9 18 l ≤ D stage3 9 18 l := by
  interval_cases l <;> decide +kernel
theorem zY434 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage2 recipe2 10 18 l ≤ D stage3 10 18 l := by
  interval_cases l <;> decide +kernel
theorem zY435 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage2 recipe2 11 18 l ≤ D stage3 11 18 l := by
  interval_cases l <;> decide +kernel
theorem zY436 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage2 recipe2 12 18 l ≤ D stage3 12 18 l := by
  interval_cases l <;> decide +kernel
theorem zY437 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage2 recipe2 13 18 l ≤ D stage3 13 18 l := by
  interval_cases l <;> decide +kernel
theorem zY438 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage2 recipe2 14 18 l ≤ D stage3 14 18 l := by
  interval_cases l <;> decide +kernel
theorem zY439 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage2 recipe2 15 18 l ≤ D stage3 15 18 l := by
  interval_cases l <;> decide +kernel
theorem zY440 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage2 recipe2 16 18 l ≤ D stage3 16 18 l := by
  interval_cases l <;> decide +kernel
theorem zY441 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage2 recipe2 17 18 l ≤ D stage3 17 18 l := by
  interval_cases l <;> decide +kernel
theorem zY442 (l : Nat) (hjl : 18 < l) (hl : l < 20) :
    rawD stage2 recipe2 18 18 l ≤ D stage3 18 18 l := by
  interval_cases l <;> decide +kernel
theorem zY443 (i l : Nat)
    (hi : 9 ≤ i) (hij : i ≤ 18) (hjl : 18 < l) (hl : l < 20) :
    rawD stage2 recipe2 i 18 l ≤ D stage3 i 18 l := by
  interval_cases i
  · exact zY433 l hjl hl
  · exact zY434 l hjl hl
  · exact zY435 l hjl hl
  · exact zY436 l hjl hl
  · exact zY437 l hjl hl
  · exact zY438 l hjl hl
  · exact zY439 l hjl hl
  · exact zY440 l hjl hl
  · exact zY441 l hjl hl
  · exact zY442 l hjl hl

end ZP
end z197

section z198
namespace ZP
set_option maxHeartbeats 3000000

theorem zY444 (i j l : Nat) (hij : i ≤ j) (hjl : j < l) (hl : l < 20) :
    rawD stage2 recipe2 i j l ≤ D stage3 i j l := by
  by_cases hi : i < 9
  · have hqi := nonzero_tolerance_2 ⟨i,hi⟩
    rw [rawD_eq_sum_of_nonzero hqi]
    rw [nonzero_d_sum_2 ⟨i,hi⟩ ⟨j,by omega⟩ ⟨l,hl⟩ hij hjl]
    exact Nat.add_le_add (zY358 i j hij (by omega))
      (zY378 j l hjl hl)
  · have hi' : 9 ≤ i := by omega
    have hj : 9 ≤ j := by omega
    have hj' : j < 19 := by omega
    interval_cases j
    · exact zY380 i l hi' hij hjl hl
    · exact zY383 i l hi' hij hjl hl
    · exact zY387 i l hi' hij hjl hl
    · exact zY392 i l hi' hij hjl hl
    · exact zY398 i l hi' hij hjl hl
    · exact zY405 i l hi' hij hjl hl
    · exact zY413 i l hi' hij hjl hl
    · exact zY422 i l hi' hij hjl hl
    · exact zY432 i l hi' hij hjl hl
    · exact zY443 i l hi' hij hjl hl

theorem _root_.solution : TransitionCertificate stage2 recipe2 stage3 where
  a i j hij := zY317 i.val j.val hij j.isLt
  b i j hij := zY338 i.val j.val hij j.isLt
  m i j hij hn := zY358 i.val j.val hij (by omega)
  p j l hjl := zY378 j.val l.val hjl l.isLt
  d i j l hij hjl := zY444 i.val j.val l.val hij hjl l.isLt
end ZP
end z198
