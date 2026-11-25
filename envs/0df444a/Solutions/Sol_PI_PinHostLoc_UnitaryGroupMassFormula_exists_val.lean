-- Prove2me | solution 1 for PI.PinHostLoc.UnitaryGroupMassFormula.exists_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:03:08.010724+00:00
-- url     : https://prove2.me/submissions/558a5968-7687-4795-a6c1-24ebe85f6c02

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
theorem _root_.solution (a : A.Fp) (ha : a ≠ 0) :
    ∃ x : F, valuation A.Fp (A.ιF x) = valuation A.Fp a := by
  have := A.lf
  have hv : ValuativeRel.valuation A.Fp a ≠ 0 := (ValuativeRel.valuation A.Fp).ne_zero_iff.mpr ha
  obtain ⟨x, hx⟩ := A.dense.mem_nhds ((ValuativeRel.valuation A.Fp).locally_const hv)
  exact ⟨x, hx⟩
end PI.PinHostLoc.UnitaryGroupMassFormula
