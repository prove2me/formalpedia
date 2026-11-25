-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.orb_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:25:27.143665+00:00
-- url     : https://prove2.me/submissions/d4eeca6d-c394-4acd-b10d-01c83a6ae1a1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeylForU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_IsPositiveDefiniteMatrixCoefficientOfMemAlgA

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
variable {N : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H}
namespace PI.UnitaryGroupMassFormula.PolyCoef
theorem _root_.solution (hrep : IsURepOn (Kset (allPos N)) σ) (hst : IsKStableOn (allPos N) σ S) (u : S) :
    Continuous (orb hst u) := by
  refine Continuous.subtype_mk ?_ _
  exact (hrep.2.2 (u : H)).comp_continuous continuous_subtype_val fun x => memK x
end PI.UnitaryGroupMassFormula.PolyCoef
