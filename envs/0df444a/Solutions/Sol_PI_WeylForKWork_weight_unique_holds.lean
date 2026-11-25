-- Prove2me | solution 1 for PI.WeylForKWork.weight_unique_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:41:54.478059+00:00
-- url     : https://prove2.me/submissions/6356646d-4650-41c8-bc7a-727ad1b607bb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_TrivKtype
import Definitions.Def_Lemmata_GeneralBFactLeftVariant_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Weights
import Theorems.Thm_PI_WeylForKWork_false_of_neg_smul_eq_smul
import Theorems.Thm_PI_WeylForKInhab_diag_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix
open scoped InnerProductSpace
namespace PI.WeylForKWork
theorem _root_.solution : WtUniq := by
  intro n H _ _ σ μ μ' w hw h1 h2
  funext a
  by_contra hne
  have hd : μ a - μ' a ≠ 0 := sub_ne_zero.mpr hne
  have hT := PI.WeylForKInhab.diag_mem (allPos n) (Pi.single a (Real.pi / (μ a - μ' a)))
  have e1 := h1 _ hT
  have e2 := h2 _ hT
  rw [e1] at e2
  have s : ∀ ν : Fin n → ℝ, ∑ b, ν b * (Pi.single a (Real.pi / (μ a - μ' a)) : Fin n → ℝ) b =
      ν a * (Real.pi / (μ a - μ' a)) := by
    intro ν
    rw [Finset.sum_eq_single a]
    · rw [Pi.single_eq_same]
    · intro b _ hb; rw [Pi.single_eq_of_ne hb]; ring
    · intro hh; exact absurd (Finset.mem_univ a) hh
  rw [s, s] at e2
  have hc : (μ a - μ' a) * (Real.pi / (μ a - μ' a)) = Real.pi := mul_div_cancel₀ _ hd
  have hxy : μ a * (Real.pi / (μ a - μ' a)) = μ' a * (Real.pi / (μ a - μ' a)) + Real.pi := by
    linear_combination hc
  rw [hxy, Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I] at e2
  exact false_of_neg_smul_eq_smul _ (Complex.exp_ne_zero _) w hw e2
end PI.WeylForKWork
