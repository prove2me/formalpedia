-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.sigR_inclE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:53.542521+00:00
-- url     : https://prove2.me/submissions/2909c057-4cc7-43ae-9679-931ae1dfd72c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork
variable {F E : Type} [Field F] [CommRing E] [Algebra F E]
namespace PI.UnitaryApproxFinWork
theorem _root_.solution (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (e : E) :
    PI.UnitaryApproxDefs.sigR σ R (PI.UnitaryApproxDefs.inclE (F := F) R e) = PI.UnitaryApproxDefs.inclE (F := F) R (σ e) := by
  first
  | rfl
  | simp [PI.UnitaryApproxDefs.sigR, PI.UnitaryApproxDefs.inclE]
end PI.UnitaryApproxFinWork
