-- Prove2me | solution 1 for chk_lBoundRight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:47:00.945803+00:00
-- url     : https://prove2.me/submissions/bc5bb51c-1dec-4e7c-ab5c-5b448aac6dbe

import Definitions.Def_Formalism_PeriodIntegrals_DiscIn
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LandauLocal3
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LRight
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaGrowth
import Definitions.Def_Formalism_PeriodIntegrals_ExplicitFormulaCounts_AnalyticInputs
import Theorems.Thm_Formalism_FX_l_function_partial_sum
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_character_sum_Icc_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.LBoundRight := by
  intro q _ χ hχ s hs
  have h := Formalism.FX.l_function_partial_sum q χ hχ ((q : ℝ) + 1)
    (fun M => Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ M) s hs 1 le_rfl
  simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, map_one, Complex.one_cpow, mul_one,
    Real.one_rpow] at h
  calc ‖DirichletCharacter.LFunction χ s‖
      = ‖(1 : ℂ) + (DirichletCharacter.LFunction χ s - 1)‖ := by congr 1; ring
    _ ≤ ‖(1 : ℂ)‖ + ‖DirichletCharacter.LFunction χ s - 1‖ := norm_add_le _ _
    _ ≤ 1 + 2 * ((q : ℝ) + 1) * (1 + ‖s‖ / s.re) := by rw [norm_one]; linarith
