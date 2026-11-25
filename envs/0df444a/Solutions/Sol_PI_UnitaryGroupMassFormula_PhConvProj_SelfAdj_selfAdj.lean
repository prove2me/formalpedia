-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj.selfAdj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:16.564823+00:00
-- url     : https://prove2.me/submissions/618d70cb-0421-41b6-b3f6-1b8889694670

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhConvProj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_ConvProjOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_SelfAdj
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhConvProj_SelfAdj_inner_symm

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhConvProj PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj
open PI.PhConvProj
variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
namespace PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj
theorem _root_.solution : Defs.SelfAdjStep := by
  intro G _ _ _ _ _ _ μ _ _ _ ph m _ hidem K _ _ π T hπ hT x y
  exact inner_symm μ ph hidem.2.1 hπ hT x y
end PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj
