-- Prove2me | solution 1 for PI.PinHostLoc.UnitaryGroupMassFormula.vF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:02:29.558224+00:00
-- url     : https://prove2.me/submissions/40a9fad5-bf8e-4211-992d-9a5fa7ae57e6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PinHostLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalResidueCharacter_ResCharEq

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
    valuation A.Fp (A.ιF x) ≤ valuation A.Fp (A.ιF y) ↔ p.valuation F x ≤ p.valuation F y := ((ValuativeRel.valuation A.Fp).vle_iff_le).symm.trans (A.val x y)
end PI.PinHostLoc.UnitaryGroupMassFormula
