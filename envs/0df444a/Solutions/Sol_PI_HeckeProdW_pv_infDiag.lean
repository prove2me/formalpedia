-- Prove2me | solution 1 for PI.HeckeProdW.pv_infDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:13.621858+00:00
-- url     : https://prove2.me/submissions/782d2ab8-8b30-4ab5-b40f-e3e5aa712801

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_Kernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_PvLocalSelf
import Theorems.Thm_PI_HeckeProdW_infDiag_eq
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_infIdele_snd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host RestrictedProduct
open PI PI.HeckeProdW
variable {L : Type} [Field L] [NumberField L]
namespace PI.HeckeProdW
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : pv v (infDiag k) = 1 := by
  rw [infDiag_eq, map_prod]
  exact Finset.prod_eq_one fun w _ => infIdele_snd L w (atInf w k) v
end PI.HeckeProdW
