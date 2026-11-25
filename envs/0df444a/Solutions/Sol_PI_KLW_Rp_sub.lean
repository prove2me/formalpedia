-- Prove2me | solution 1 for PI.KLW.Rp_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:54:37.901473+00:00
-- url     : https://prove2.me/submissions/75c9cfd0-0c18-4a2a-b4a6-952a1eddf958

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Theorems.Thm_PI_KLW_Rp_add
import Theorems.Thm_PI_KLW_Rp_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW
variable {K : Type} [Field K] [NumberField K]
namespace PI.KLW
theorem _root_.solution {p : ℕ} {x y : K} (hx : Rp K p x) (hy : Rp K p y) : Rp K p (x - y) := by
  simpa [sub_eq_add_neg] using Rp_add hx (Rp_neg hy)
end PI.KLW
