-- Prove2me | solution 1 for PI.FockOneDegW.HwC.coeff_X_mul_pderiv_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:39:28.450206+00:00
-- url     : https://prove2.me/submissions/726c392e-a33b-4315-9fa5-2df83b6f316a

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
theorem _root_.solution {σ : Type*} (l l' : σ) (P : MvPolynomial σ ℂ) (γ : σ →₀ ℕ)
    (h : coeff γ (X l * pderiv l' P) ≠ 0) :
    ∃ β ∈ P.support, β + Finsupp.single l 1 = γ + Finsupp.single l' 1 := by
  classical
  rw [coeff_X_mul'] at h
  by_cases hs : l ∈ γ.support
  · rw [if_pos hs, coeff_pderiv] at h
    refine ⟨γ - Finsupp.single l 1 + Finsupp.single l' 1, ?_, ?_⟩
    · rw [mem_support_iff]
      exact left_ne_zero_of_mul h
    · have hle : Finsupp.single l 1 ≤ γ :=
        Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs))
      rw [add_right_comm, tsub_add_cancel_of_le hle]
  · rw [if_neg hs] at h
    exact absurd rfl h
end PI.FockOneDegW.HwC
