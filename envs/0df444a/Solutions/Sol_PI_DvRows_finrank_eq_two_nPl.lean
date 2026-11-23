-- Prove2me | solution 1 for PI.DvRows.finrank_eq_two_nPl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:04.477941+00:00
-- url     : https://prove2.me/submissions/1248382b-b78e-4686-90a4-71b482e69f32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv
variable {K : Type} [Field K] [NumberField K]
namespace PI.DvRows
theorem _root_.solution [NumberField.IsTotallyComplex K] :
    (Module.finrank ℚ K : ℝ) = 2 * (Formalism.HN.nPl K : ℝ) := by
  unfold Formalism.HN.nPl
  have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  have h2 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  have h3 := NumberField.IsTotallyComplex.nrRealPlaces_eq_zero K
  rw [← h1, h2, h3]
  push_cast
  ring
end PI.DvRows
