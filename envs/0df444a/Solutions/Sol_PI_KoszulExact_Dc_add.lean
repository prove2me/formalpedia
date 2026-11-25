-- Prove2me | solution 1 for PI.KoszulExact.Dc_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:48:49.475228+00:00
-- url     : https://prove2.me/submissions/8fec19fc-62db-40d7-81c9-f63ec24605fc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ContractPowSuccMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open PI PI.KoszulExact
variable {R : Type u} [CommRing R] {D : ℕ}
namespace PI.KoszulExact
theorem _root_.solution (i : Fin D) (p q : ℕ) (x y : ExteriorAlgebra R (Fin D → R))
    (hx : Dc R i p q x) (hy : Dc R i p q y) : Dc R i p q (x + y) := by
  obtain ⟨a1, ha1, b1, hb1, rfl⟩ := hx
  obtain ⟨a2, ha2, b2, hb2, rfl⟩ := hy
  refine ⟨a1 + a2, Submodule.add_mem _ ha1 ha2, b1 + b2, Submodule.add_mem _ hb1 hb2, ?_⟩
  rw [mul_add]
  abel
end PI.KoszulExact
