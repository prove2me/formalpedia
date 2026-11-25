-- Prove2me | solution 1 for PI.PinHostLoc.UnitaryGroupMassFormula.vF_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:03:34.1059+00:00
-- url     : https://prove2.me/submissions/9f227e2d-022c-4de2-8385-ee57998073ab

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PinHostLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalResidueCharacter_ResCharEq
import Theorems.Thm_PI_PinHostLoc_UnitaryGroupMassFormula_vF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField ValuativeRel WithZero
open PI PI.PinHostLoc PI.PinHostLoc.UnitaryGroupMassFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : Formalism.MainNotions.S.Loc.LocAt F E sig p)
namespace PI.PinHostLoc.UnitaryGroupMassFormula
theorem _root_.solution (x y : F) :
    valuation A.Fp (A.ιF x) < valuation A.Fp (A.ιF y) ↔ p.valuation F x < p.valuation F y := by
  rw [← not_le, ← not_le, vF A]
end PI.PinHostLoc.UnitaryGroupMassFormula
