-- Prove2me | solution 1 for PI.WAU.B.countable_cls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:23.370825+00:00
-- url     : https://prove2.me/submissions/a2a67b35-cd62-43ce-a7a8-14495e4a695c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal
import Theorems.Thm_PI_WAU_B_countable_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU PI.WAU.B
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]
namespace PI.WAU.B
theorem _root_.solution (M : ℕ) : Countable (Bad F M → F) := by
  haveI : Finite (Bad F M) := (HeightOneSpectrum.Support.finite (𝓞 F) ((M : F)⁻¹)).to_subtype
  haveI : Countable F := countable_field F
  infer_instance
end PI.WAU.B
