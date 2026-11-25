-- Prove2me | solution 1 for PI.MkQ.rho_apply_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:57:28.178799+00:00
-- url     : https://prove2.me/submissions/939c3749-70f4-4965-9b15-14691d2711ff

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MinkowskiQ
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_Minkowski
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiTorsionFree_Lattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.MkQ
open Matrix
variable {N : ℕ} (G : Subgroup (GeneralLinearGroup (Fin N) ℚ))
namespace PI.MkQ
theorem _root_.solution (g : G) (v : lat G) :
    ((rho G g v : lat G) : Fin N → ℚ) =
      ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec v := rfl
end PI.MkQ
