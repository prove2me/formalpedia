-- Prove2me | solution 1 for PI.KoszulExact.eb_mem_Li
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:49:02.579332+00:00
-- url     : https://prove2.me/submissions/43dbe593-8334-4658-91f9-177996a547c8

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
theorem _root_.solution (k : Fin D) (i : ℕ) (hk : (k : ℕ) < i) : eb R k ∈ Li R D i :=
  Submodule.subset_span ⟨k, hk, rfl⟩
end PI.KoszulExact
