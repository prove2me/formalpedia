-- Prove2me | solution 1 for PI.PinHostLoc.UnitaryGroupMassFormula.vF_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:03:18.865995+00:00
-- url     : https://prove2.me/submissions/d307ab7f-1d1e-4a5c-8b2a-48289f04ba38

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
    valuation A.Fp (A.ιF x) = valuation A.Fp (A.ιF y) ↔ p.valuation F x = p.valuation F y := by
  rw [le_antisymm_iff, le_antisymm_iff, vF A, vF A]
end PI.PinHostLoc.UnitaryGroupMassFormula
