-- Prove2me | solution 1 for PI.MkQ.minkowskiBoundQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:35:32.572157+00:00
-- url     : https://prove2.me/submissions/f49bb6b6-9de2-4595-ac15-67046c69eda9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MinkowskiQ
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_Minkowski
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiTorsionFree_Lattice
import Theorems.Thm_PI_MkQ_phi_injective
import Theorems.Thm_card_dvd_minkowskiNumber


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
theorem _root_.solution : PI.MinkowskiBoundQ := by
  intro N G hG
  let e := MonoidHom.ofInjective (phi_injective G)
  have : Finite (phi G).range := Finite.of_equiv _ e.toEquiv
  rw [Nat.card_congr e.toEquiv]
  exact card_dvd_minkowskiNumber N _ inferInstance
end PI.MkQ
