-- Prove2me | solution 1 for PI.WAU.intF_of_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:05:36.721206+00:00
-- url     : https://prove2.me/submissions/c8304afb-55da-4bba-9671-8e838b4539e3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CoordTmulOneMul
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_SmulEqAlgebraMapMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F]
namespace PI.WAU
theorem _root_.solution (a : 𝓞 F) : IntF (algebraMap (𝓞 F) F a) := by
  unfold IntF Ohat
  intro v
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v a
end PI.WAU
