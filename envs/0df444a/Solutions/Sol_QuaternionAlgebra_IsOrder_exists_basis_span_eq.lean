-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.exists_basis_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/09e6214c-dc15-5cbf-85b0-0b4a18b80d10

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Theorems.Thm_QuaternionAlgebra_IsOrder_finrank_eq_four
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_exists_basis_span_eq

set_option autoImplicit false

open scoped Quaternion

theorem solution {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) :
    ∃ B : Module.Basis (Fin 4) ℚ ℍ[ℚ, a, b], (∀ i, B i ∈ Λ) ∧ Submodule.span ℤ (Set.range B) = Λ := by
  haveI : Submodule.IsLattice ℚ Λ := ⟨hΛ.fg, hΛ.spanTop⟩
  haveI : Module.Free ℤ Λ := Submodule.IsLattice.free ℚ Λ
  haveI : Module.Finite ℤ Λ := Submodule.IsLattice.finite ℚ Λ
  let Bz : Module.Basis (Fin 4) ℤ Λ := (Module.finBasis ℤ Λ).reindex (finCongr hΛ.finrank_eq_four)
  refine ⟨Bz.extendOfIsLattice ℚ, fun i => ?_, ?_⟩
  · rw [Module.Basis.extendOfIsLattice_apply]; exact (Bz i).2
  · have hrng : Set.range (Bz.extendOfIsLattice ℚ) = Λ.subtype '' Set.range Bz := by
      ext y
      simp only [Set.mem_range, Set.mem_image, Module.Basis.extendOfIsLattice_apply]
      exact ⟨fun ⟨i, hi⟩ => ⟨Bz i, ⟨i, rfl⟩, hi⟩, fun ⟨z, ⟨i, hi⟩, hz⟩ => ⟨i, hi ▸ hz⟩⟩
    rw [hrng, ← Submodule.map_span, Bz.span_eq, Submodule.map_top, Submodule.range_subtype]

end S_QuaternionAlgebra_IsOrder_exists_basis_span_eq
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_exists_basis_span_eq (solution)
