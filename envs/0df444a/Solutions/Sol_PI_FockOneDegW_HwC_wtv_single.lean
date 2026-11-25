-- Prove2me | solution 1 for PI.FockOneDegW.HwC.wtv_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:39:59.669752+00:00
-- url     : https://prove2.me/submissions/6b44a7ca-4f5f-4102-9d33-e81b0d897e1e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_CoeffXMulPderivSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.HwC
namespace PI.FockOneDegW.HwC
theorem _root_.solution {p q r s : ℕ} (l : Ln p q r s) (c : Ix p q) :
    wtv (Finsupp.single l 1) c = (if l.1 = c then sgnL l else 0) + kShift r s c := by
  unfold wtv
  congr 1
  have key : ∀ d : Ix r s, sgnL ((c, d) : Ln p q r s) * ((Finsupp.single l 1 ((c, d) : Ln p q r s) : ℕ) : ℚ) =
      if d = l.2 ∧ l.1 = c then sgnL l else 0 := by
    intro d
    by_cases h1 : d = l.2 ∧ l.1 = c
    · obtain ⟨rfl, rfl⟩ := h1
      simp
    · rw [if_neg h1]
      have hne : l ≠ ((c, d) : Ln p q r s) := fun he => h1 ⟨by rw [he], by rw [he]⟩
      simp [Finsupp.single_apply, hne]
  simp_rw [key]
  by_cases h : l.1 = c <;> simp [h]
end PI.FockOneDegW.HwC
