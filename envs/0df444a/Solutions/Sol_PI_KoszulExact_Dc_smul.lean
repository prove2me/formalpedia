-- Prove2me | solution 1 for PI.KoszulExact.Dc_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:48:55.140167+00:00
-- url     : https://prove2.me/submissions/d45f3642-1e70-4cef-819c-e9062f102a61

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
theorem _root_.solution (i : Fin D) (p q : ℕ) (r : R) (x : ExteriorAlgebra R (Fin D → R))
    (hx : Dc R i p q x) : Dc R i p q (r • x) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨r • a, Submodule.smul_mem _ _ ha, r • b, Submodule.smul_mem _ _ hb,
    by rw [smul_add, mul_smul_comm]⟩
end PI.KoszulExact
