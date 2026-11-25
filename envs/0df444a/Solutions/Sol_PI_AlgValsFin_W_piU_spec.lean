-- Prove2me | solution 1 for PI.AlgValsFin.W.piU_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:19:18.793735+00:00
-- url     : https://prove2.me/submissions/89e473de-e432-44ef-9612-2b60a7de4abe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_OrdFEqOfClassOf
import Theorems.Thm_Neutral_B1_exists_isUniformiserAt


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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) :
    IsUniformiserAt L v ((piU v : (v.adicCompletion L)ˣ) : v.adicCompletion L) :=
  Classical.choose_spec (exists_isUniformiserAt L v)
end PI.AlgValsFin.W
