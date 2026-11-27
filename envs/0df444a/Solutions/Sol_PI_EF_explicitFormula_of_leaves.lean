-- Prove2me | solution 1 for PI.EF.explicitFormula_of_leaves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:14:49.867134+00:00
-- url     : https://prove2.me/submissions/1596264a-a757-4d50-b832-a16a4e90c9fd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ExplicitFormulaFromGluing
import Theorems.Thm_PI_EF_explicitFormula_of_perron_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex
namespace PI.EF
theorem _root_.solution

    (hK : PerronKernel) (hPS : ∃ C, 0 < C ∧ PerronSumBound C) (hRC : RectCauchy)
    (hZL : ZeroLocus) (hRP : RegularPart) (hZW : PI.ZerosWindow) (hLA : LocalAbstract)
    (hG : ∃ A C, 0 < A ∧ 0 < C ∧ LGrowth A C)

    (g1 : GluePerronTrunc) (g2 : GluePerronL) (g3 : GlueRectResidue) (g4 : GlueGoodHeight)
    (g5 : GlueTruncChange) (g6 : GlueZerosFinite) (g7 : GlueLocalLemma) (g8 : GlueHoriz)
    (g9 : GlueLeft) (g10 : GlueRegAtZero) (g11 : GlueContour) (g12 : GlueSides) (g13 : GlueShift) :
    PI.ExplicitFormula := by
  obtain ⟨κ, hκ, hGood⟩ := g4 hZW
  have hLL := g7 hLA hG hZL hZW
  have hZF := g6 hZW
  exact explicitFormula_of_perron_shift κ (g2 (g1 hK hPS))
    (g13 κ hκ hRP (g11 (g3 hRC) hZL hZF) (g12 κ hκ (g8 hZW hLL hZL κ hκ) (g9 hZW hLL hZL)) (g10 hZW hLL))
    hGood (g5 hZW) hZF
end PI.EF
