-- Prove2me | solution 1 for PI.PinHostLoc.UnitaryGroupMassFormula.natVal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:36.273666+00:00
-- url     : https://prove2.me/submissions/2d292cd5-61e4-429b-8359-0d2d45a603f5

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
theorem _root_.solution (n : ℕ) : p.valuation F ((n : ℕ) : F) = p.intValuation ((n : ℕ) : 𝓞 F) := by
  have h := p.valuation_of_algebraMap (K := F) ((n : ℕ) : 𝓞 F)
  exact_mod_cast h
end PI.PinHostLoc.UnitaryGroupMassFormula
