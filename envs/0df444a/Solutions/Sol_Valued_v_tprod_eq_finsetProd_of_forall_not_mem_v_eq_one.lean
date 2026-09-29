-- Prove2me | solution 1 for Valued.v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/50a5b8f4-0e8c-5c57-a307-01a74f55af82

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Valued_v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one

set_option autoImplicit false

open scoped Topology
open Filter

theorem solution
    {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {ι : Type*} (f : ι → K) (hf : Multipliable f)
    (S : Finset ι) (hS : ∀ i, i ∉ S → Valued.v (f i) = 1) :
    Valued.v (∏' i, f i) = ∏ i ∈ S, Valued.v (f i) := by
  classical
  have hprod := hf.hasProd

  have hpart : ∀ T : Finset ι, S ⊆ T → Valued.v (∏ i ∈ T, f i) = Valued.v (∏ i ∈ S, f i) := by
    intro T hT
    rw [map_prod, map_prod, ← Finset.prod_sdiff hT, Finset.prod_eq_one (fun i hi => hS i (Finset.mem_sdiff.mp hi).2),
      one_mul]

  have hres : ∀ x y : K, Valued.v x = Valued.v y ↔
      (Valued.v : Valuation K Γ₀).restrict x = (Valued.v : Valuation K Γ₀).restrict y := by
    intro x y
    constructor
    · intro h
      apply le_antisymm
      · rw [← not_lt, Valuation.restrict_lt_iff, not_lt, h]
      · rw [← not_lt, Valuation.restrict_lt_iff, not_lt, h]
    · intro h
      apply le_antisymm
      · rw [← not_lt, ← Valuation.restrict_lt_iff, not_lt, h]
      · rw [← not_lt, ← Valuation.restrict_lt_iff, not_lt, h]

  have hclosed := Valued.isClosed_sphere (R := K) ((Valued.v : Valuation K Γ₀).restrict (∏ i ∈ S, f i))
  have hev : ∀ᶠ T : Finset ι in atTop,
      (∏ i ∈ T, f i) ∈ {x : K | (Valued.v : Valuation K Γ₀).restrict x =
        (Valued.v : Valuation K Γ₀).restrict (∏ i ∈ S, f i)} := by
    filter_upwards [eventually_ge_atTop S] with T hT
    exact (hres _ _).mp (hpart T hT)
  have hmem := hclosed.mem_of_tendsto hprod hev
  rw [Set.mem_setOf_eq] at hmem
  rw [(hres _ _).mpr hmem, map_prod]

end S_Valued_v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one
end P2MW
export P2MW.S_Valued_v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one (solution)
