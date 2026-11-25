-- Prove2me | solution 1 for PI.HeckeProdW.Phi_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:03.459063+00:00
-- url     : https://prove2.me/submissions/ba6e2919-09f2-4837-8f24-34e53a6aa39c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Lemmata_MiscLemmasM_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_Kernel
import Theorems.Thm_PI_HeckeProdW_gI_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host RestrictedProduct Topology
open PI PI.HeckeProdW
variable (L : Type) [Field L] [NumberField L]
namespace PI.HeckeProdW
theorem _root_.solution : Continuous (Phi L) :=
  (Continuous.units_map _ (gI_cont L)).comp
    (ContinuousMulEquiv.piUnits (M := fun v : HeightOneSpectrum (𝓞 L) =>
      v.adicCompletionIntegers L)).symm.continuous
end PI.HeckeProdW
