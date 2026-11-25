-- Prove2me | solution 1 for PI.HeckeProdW.Phi_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:41:53.570805+00:00
-- url     : https://prove2.me/submissions/445b7bab-77af-43d1-915f-717732072125

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_Kernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_PvLocalSelf
import Theorems.Thm_Neutral_B1_localIdele_isSupportedAt
import Theorems.Thm_Neutral_B1_localIdele_snd_self


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
theorem _root_.solution [DecidableEq (HeightOneSpectrum (𝓞 L))] (v : HeightOneSpectrum (𝓞 L))
    (w : (v.adicCompletionIntegers L)ˣ) :
    Phi L (Pi.mulSingle v w) = localIdele L v (Units.map (v.adicCompletionIntegers L).subtype.toMonoidHom w) := by
  refine Units.ext (Prod.ext rfl (Subtype.ext (funext fun v' => ?_)))
  change (((Pi.mulSingle v w : Pu L) v' : v'.adicCompletionIntegers L) : v'.adicCompletion L) = pv v' (localIdele L v (Units.map (v.adicCompletionIntegers L).subtype.toMonoidHom w))
  by_cases h : v' = v
  · subst h
    rw [Pi.mulSingle_eq_same]
    exact (localIdele_snd_self L v' (Units.map (v'.adicCompletionIntegers L).subtype.toMonoidHom w)).symm
  · rw [Pi.mulSingle_eq_of_ne h]
    exact ((localIdele_isSupportedAt L v _).2 v' h).symm
end PI.HeckeProdW
