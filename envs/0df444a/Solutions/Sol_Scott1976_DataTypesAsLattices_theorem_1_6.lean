-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_1_6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:03:27.822937+00:00
-- url     : https://prove2.me/submissions/622cfd1f-c322-479e-90d4-30f22baa705a

import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Basic
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
open TopologicalSpace
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {X : Type*} [TopologicalSpace X] [T0Space X]
    (U : ℕ → Set X) (hbasis : IsTopologicalBasis (Set.range U)) :
    Function.Injective (embed U) ∧ Continuous (embed U) := by
  constructor
  · intro x y hxy
    have hmem : ∀ n, x ∈ U n ↔ y ∈ U n := fun n =>
      show n ∈ embed U x ↔ n ∈ embed U y by rw [hxy]
    refine Inseparable.eq ?_
    refine inseparable_iff_forall_isOpen.mpr ?_
    intro V hV
    constructor
    · intro hx
      obtain ⟨t, ⟨n, rfl⟩, hxt, htV⟩ :=
        hbasis.mem_nhds_iff.mp (hV.mem_nhds hx)
      exact htV ((hmem n).mp hxt)
    · intro hy
      obtain ⟨t, ⟨n, rfl⟩, hyt, htV⟩ :=
        hbasis.mem_nhds_iff.mp (hV.mem_nhds hy)
      exact htV ((hmem n).mpr hyt)
  · refine continuous_generateFrom_iff.2 ?_
    rintro _ ⟨n, rfl⟩
    have : embed U ⁻¹' memOpen n = U n := rfl
    rw [this]
    exact hbasis.isOpen ⟨n, rfl⟩
end Scott1976.DataTypesAsLattices
