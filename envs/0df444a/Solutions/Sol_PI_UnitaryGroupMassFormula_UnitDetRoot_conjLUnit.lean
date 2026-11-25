-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.conjLUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:47:28.581807+00:00
-- url     : https://prove2.me/submissions/46f837de-fbaa-4920-9d69-1698df6c855a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Lemmata_GeneralBFactLeftTer_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NormLeOneOfRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution : ConjLUnit := by
  rintro l x ⟨hx0, k, hk, h1, h2⟩
  refine ⟨(map_ne_zero _).mpr hx0, k, hk, ?_, ?_⟩
  · have h := h1.map (starRingEnd ℂ).toIntAlgHom
    change IsIntegral ℤ (conj ((k : ℂ) * x)) at h
    rwa [map_mul, map_natCast] at h
  · have h := h2.map (starRingEnd ℂ).toIntAlgHom
    change IsIntegral ℤ (conj ((k : ℂ) * x⁻¹)) at h
    rwa [map_mul, map_natCast, map_inv₀] at h
end PI.UnitaryGroupMassFormula.UnitDetRoot
