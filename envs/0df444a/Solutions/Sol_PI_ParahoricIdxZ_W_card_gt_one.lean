-- Prove2me | solution 1 for PI.ParahoricIdxZ.W.card_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:02:53.445612+00:00
-- url     : https://prove2.me/submissions/01ebb65a-e39a-44ed-b959-baeb85ffc069

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ParahoricIdxZ
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_nontriv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate Finset
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
namespace PI.ParahoricIdxZ.W
theorem _root_.solution (F : Type) [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O)
    (hloc : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) [Finite (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)] :
    1 < Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) := by
  have := Formalism.DoubleCosetMeasures.P.GLRed.nontriv O ϖ hϖ hloc
  exact Finite.one_lt_card
end PI.ParahoricIdxZ.W
