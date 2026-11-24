-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_F_Hk1_rpow_neg_two__f5e7837d33f8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:32:58.988522+00:00
-- url     : https://prove2.me/submissions/f08d6164-241a-4db7-a8a2-faa8e91bec2d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelIntegralValue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk1
namespace Formalism.L2.Th1.F.Hk1
theorem _root_.solution {u : ℝ} (hu : 0 < u) : u ^ (-2 : ℝ) = (u ^ 2)⁻¹ := by
  rw [Real.rpow_neg hu.le, Real.rpow_two]
end Formalism.L2.Th1.F.Hk1
