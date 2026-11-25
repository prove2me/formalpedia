-- Prove2me | solution 1 for PI.KoszulExact.one_mem_pow_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:48:42.562344+00:00
-- url     : https://prove2.me/submissions/acda892b-cc0d-4a4a-96fb-ad07b2cc4e46

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
theorem _root_.solution (i : ℕ) : (1 : ExteriorAlgebra R (Fin D → R)) ∈ Li R D i ^ 0 := by
  rw [pow_zero]
  exact Submodule.mem_one.2 ⟨1, map_one _⟩
end PI.KoszulExact
