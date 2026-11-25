-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.TBDisc.normFam_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:43:36.539261+00:00
-- url     : https://prove2.me/submissions/d2d8d3d6-7c33-4d00-a50c-399ae0a592c1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_RatIntUnifDiscrete
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_UniformDiscreteness_FgOfUnifDiscrete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.TBDisc
open NumberField ReciprocityTheory.ChartRestriction.G.TB
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
namespace PI.UnitaryGroupMassFormula.TBDisc
theorem _root_.solution (Nf : NormFam K V) (σ : K →+* ℂ) : Nf.N σ 0 = 0 := by
  have h := Nf.smul σ 0 0
  simpa using h
end PI.UnitaryGroupMassFormula.TBDisc
