-- Prove2me | solution 1 for PI.AlgValsFin.W.ordAt_eU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:52:30.395743+00:00
-- url     : https://prove2.me/submissions/88b59acf-c0d8-4040-8297-5f9b2fbaf09a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_OrdFEqOfClassOf
import Theorems.Thm_PI_AlgValsFin_W_piU_spec
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_ordAt_localIdele


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
namespace PI.AlgValsFin.W
theorem _root_.solution (v w : HeightOneSpectrum (𝓞 L)) [Decidable (w = v)] :
    ordAt L w (eU v) = if w = v then 1 else 0 := by
  classical
  unfold eU
  rw [ordAt_localIdele L v w (piU v) (piU_spec v)]
  congr 1
end PI.AlgValsFin.W
