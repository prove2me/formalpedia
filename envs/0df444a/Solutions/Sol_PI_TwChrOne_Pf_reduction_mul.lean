-- Prove2me | solution 1 for PI.TwChrOne.Pf.reduction_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:14.030842+00:00
-- url     : https://prove2.me/submissions/07e592cd-2adc-4365-9ab0-9612dd6aaf87

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwChrOne PI.TwChrOne.Pf
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
namespace PI.TwChrOne.Pf
theorem _root_.solution {a b : E} (ha : IntAt P a) (hb : IntAt P b) : redP P (a * b) = redP P a * redP P b :=
  (redH P).map_mul ⟨a, ha⟩ ⟨b, hb⟩
end PI.TwChrOne.Pf
