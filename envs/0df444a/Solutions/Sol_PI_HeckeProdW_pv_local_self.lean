-- Prove2me | solution 1 for PI.HeckeProdW.pv_local_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:23.348594+00:00
-- url     : https://prove2.me/submissions/b114f895-5276-40af-908a-594fba57af80

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_Kernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_PvLocalSelf

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    pv v (localIdele L v x) = x := by
  classical
  show (RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletionIntegers L) v
    (x : v.adicCompletion L)) v = x
  simp
end PI.HeckeProdW
