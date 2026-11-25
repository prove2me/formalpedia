-- Prove2me | solution 1 for PI.KoszulExact.Li_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:48:58.370849+00:00
-- url     : https://prove2.me/submissions/0685e12f-3b37-4c44-b5ac-78eff6708f43

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Ii
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ContractPowSuccMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
open PI PI.KoszulExact
variable {R : Type u} [CommRing R] {D : ℕ}
namespace PI.KoszulExact
theorem _root_.solution (R : Type u) [CommRing R] (D : ℕ) (i : ℕ) :
    Li R D i = (Submodule.span R ((fun k : Fin D => (Pi.single k (1 : R) : Fin D → R)) ''
      {k : Fin D | (k : ℕ) < i})).map (ExteriorAlgebra.ι R) := by
  rw [Submodule.map_span, Set.image_image]
  rfl
end PI.KoszulExact
