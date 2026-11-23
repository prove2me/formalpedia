-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhConvProj.Sand.urep_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:00.962816+00:00
-- url     : https://prove2.me/submissions/fc095765-3155-44e5-acd2-9f0cca444849

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_ConvProjOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_UrepMulApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhConvProj PI.UnitaryGroupMassFormula.PhConvProj.Sand
open PI.PhConvProj
variable {G : Type} [Group G] [TopologicalSpace G] {K : Type} [NormedAddCommGroup K]
  [InnerProductSpace ℂ K]
namespace PI.UnitaryGroupMassFormula.PhConvProj.Sand
theorem _root_.solution {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (a b : G) (v : K) :
    π (a * b) v = π a (π b v) := by
  rw [hπ.2.1 a b]
  rfl
end PI.UnitaryGroupMassFormula.PhConvProj.Sand
