-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhSchurConv.Main.star_inner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:09.62852+00:00
-- url     : https://prove2.me/submissions/a6347039-d2f3-4098-9362-e50a698f5c04

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhSchurConv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurConvolution_MapMulApply

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhSchurConv PI.UnitaryGroupMassFormula.PhSchurConv.Main
open PI.PhSchurConv
namespace PI.UnitaryGroupMassFormula.PhSchurConv.Main
theorem _root_.solution {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (a b : H) :
    star ⟪a, b⟫_ℂ = ⟪b, a⟫_ℂ := by
  exact inner_conj_symm b a
end PI.UnitaryGroupMassFormula.PhSchurConv.Main
