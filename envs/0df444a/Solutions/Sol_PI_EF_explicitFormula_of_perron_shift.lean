-- Prove2me | solution 1 for PI.EF.explicitFormula_of_perron_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:41:51.359576+00:00
-- url     : https://prove2.me/submissions/1b17c32a-52fd-453f-99aa-b19f719cb795

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ExplicitFormulaFromGluing
import Theorems.Thm_PI_EF_fractionFieldToGenericStalk_algebraMap_eq
import Theorems.Thm_PI_EF_first_character_sum_nonneg

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
theorem _root_.solution (κ : ℝ) (h1 : ∃ C, 0 < C ∧ PerronL C)
    (h2 : ∃ C, 0 < C ∧ ShiftBound κ C) (h3 : GoodHeightExists κ)
    (h4 : ∃ C, 0 < C ∧ TruncChange C) (h5 : ZerosFinite) : PI.ExplicitFormula := by
  obtain ⟨C1, hC1, H1⟩ := h1
  obtain ⟨C2, hC2, H2⟩ := h2
  obtain ⟨C4, hC4, H4⟩ := h4
  refine ⟨C1 + C2 + C4, by positivity, ?_⟩
  intro N _ χ hχ u T hT hTu
  refine ⟨h5 N χ hχ T, ?_⟩
  obtain ⟨T', hT1, hT2, hg⟩ := h3 N χ hχ T hT
  have e1 := H1 N χ u T T' hT hTu hT1 hT2
  have e2 := H2 N χ hχ u T T' hT hTu hT1 hT2 hg
  have e4 := H4 N χ hχ u T T' hT hTu hT1 hT2
  have hS : 0 ≤ S1 χ := first_character_sum_nonneg χ
  have key : psi0 χ u + zsum χ T u = (psiRaw χ u - vertInt χ u T') +
      (vertInt χ u T' - del1 χ * u + zsum χ T' u) - (zsum χ T' u - zsum χ T u) := by
    rw [fractionFieldToGenericStalk_algebraMap_eq]; ring
  show ‖psi0 χ u + zsum χ T u‖ ≤ (C1 + C2 + C4) * (Err N u T + S1 χ)
  rw [key]
  calc ‖(psiRaw χ u - vertInt χ u T') + (vertInt χ u T' - del1 χ * u + zsum χ T' u) -
        (zsum χ T' u - zsum χ T u)‖
      ≤ ‖psiRaw χ u - vertInt χ u T'‖ + ‖vertInt χ u T' - del1 χ * u + zsum χ T' u‖ +
        ‖zsum χ T' u - zsum χ T u‖ := (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ C1 * Err N u T + C2 * (Err N u T + S1 χ) + C4 * Err N u T := by gcongr
    _ ≤ (C1 + C2 + C4) * (Err N u T + S1 χ) := by
        nlinarith [mul_nonneg hC1.le hS, mul_nonneg hC4.le hS]
end PI.EF
