-- Prove2me | solution 1 for PI.EF.zerosFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:42:36.795801+00:00
-- url     : https://prove2.me/submissions/f30d04a4-2877-49d5-ba97-b79714906c47

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
import Theorems.Thm_PI_EF_isCompact_rect
import Theorems.Thm_PI_EF_mem_rect
import Theorems.Thm_PI_EF_differentiable_Lent
import Theorems.Thm_PI_EF_Lent_two_ne_zero
import Theorems.Thm_PI_EF_Lent_eq_zero_iff
import Theorems.Thm_PI_EF_finite_zeros_of_compact


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
open Complex Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution : ZerosFinite := by
  intro N _ χ hχ T
  have h := finite_zeros_of_compact (differentiable_Lent χ) (Lent_two_ne_zero χ)
    (isCompact_rect 0 1 (-T) T)
  refine h.subset ?_
  intro ρ hρ
  obtain ⟨hre0, hre1, him, hL⟩ := hρ
  have h1 : ρ ≠ 1 := fun e => by rw [e] at hre1; simp at hre1
  refine ⟨mem_rect.mpr ⟨⟨hre0.le, hre1.le⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · linarith [neg_abs_le ρ.im]
  · linarith [le_abs_self ρ.im]
  · exact (Lent_eq_zero_iff χ h1).mpr hL
end PI.EF
