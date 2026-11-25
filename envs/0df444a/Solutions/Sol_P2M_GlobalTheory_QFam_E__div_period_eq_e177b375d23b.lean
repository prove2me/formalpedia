-- Prove2me | solution 1 for P2M_GlobalTheory_QFam_E__div_period_eq_e177b375d23b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:58:56.314533+00:00
-- url     : https://prove2.me/submissions/2695b480-6910-4c81-9326-94cd60f84eeb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGEis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapEisensteinDivPeriod
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_L1_g__eq_e1cebfa140ec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
theorem _root_.solution {Λ : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf Λ c τ) (Ω : ℂ) :
    E₆ τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 6 = -(216 * (Λ.g₃ / Ω ^ 6)) := by
  have h6 : Complex.I ^ 6 = -1 := by
    rw [show 6 = 4 + 2 from rfl, pow_add, Complex.I_pow_four, Complex.I_sq, one_mul]
  have hI : (2 * (Real.pi : ℂ) * Complex.I) ^ 6 = -(64 * (Real.pi : ℂ) ^ 6) := by
    rw [mul_pow, h6]; ring
  rw [ReciprocityTheory.ChartRestriction.L1.g₃_eq h, div_pow, hI, div_div_eq_mul_div, mul_pow]
  simp only [div_eq_mul_inv, mul_inv]
  ring
end GlobalTheory.QFam
