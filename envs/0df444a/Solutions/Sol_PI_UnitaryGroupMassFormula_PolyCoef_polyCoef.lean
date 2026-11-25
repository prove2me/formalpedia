-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.polyCoef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:59:57.682893+00:00
-- url     : https://prove2.me/submissions/a0710315-a015-45df-902b-b4b7306fef1c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeylForU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_IsPositiveDefiniteMatrixCoefficientOfMemAlgA
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_Ugood_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PolyCoef
open MeasureTheory PI.UpqRep
open scoped InnerProductSpace
namespace PI.UnitaryGroupMassFormula.PolyCoef
theorem _root_.solution : PI.PolyCoef := by
  intro N H _ _ σ S hrep hfin hst v hv w
  have hgood : (⟨v, hv⟩ : S) ∈ Ugood σ S := by
    rw [Ugood_eq_top hrep hfin hst]
    trivial
  obtain ⟨k, P, hP⟩ := hgood w
  refine ⟨k, P, fun g hg => ?_⟩
  exact hP ⟨g, (mem_Kset_iff g).mp hg⟩
end PI.UnitaryGroupMassFormula.PolyCoef
