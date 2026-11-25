-- Prove2me | solution 1 for PI.GI.isCompact_mul_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:07.267987+00:00
-- url     : https://prove2.me/submissions/91ed6667-5b6b-4447-b43b-5cda1e881821

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaussianDualMeasure_SecondCountableTopologyAndT2Space

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory
noncomputable section
open PI PI.GI
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace PI.GI
theorem _root_.solution (x : F) : IsCompact ((fun u => x * u) '' (𝒪[F] : Set F)) := by
  have h : IsCompact (𝒪[F] : Set F) :=
    isCompact_iff_compactSpace.mpr (by exact (inferInstance : CompactSpace 𝒪[F]))
  exact h.image (continuous_const.mul continuous_id)
end PI.GI
