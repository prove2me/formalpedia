-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ProdUnitInert.norm_conic_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:58:35.737799+00:00
-- url     : https://prove2.me/submissions/2b96712f-651c-434d-bc03-c67b777b173f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertUnitProduct_NatCastNormLeOne
import Theorems.Thm_PI_UnitaryGroupMassFormula_ProdUnitInert_natCast_norm_le_one
import Theorems.Thm_PI_UnitaryGroupMassFormula_ProdUnitInert_y_norm_le_one
import Theorems.Thm_PI_UnitaryGroupMassFormula_ProdUnitInert_x_norm_le_one
import Theorems.Thm_PI_UnitaryGroupMassFormula_ProdUnitInert_normC_ratCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ProdUnitInert
variable {p : ℕ} [Fact p.Prime]
namespace PI.UnitaryGroupMassFormula.ProdUnitInert
theorem _root_.solution (d : ℕ) (hd : ¬ IsSquare (((-(d : ℤ) : ℤ) : ZMod p))) (x y : ℚ)
    (hxy : x ^ 2 + d * y ^ 2 = 1) (γ : ℂ_[p]) (hγ : γ ^ 2 = -(d : ℂ_[p])) :
    ‖(x : ℂ_[p]) + y * γ‖ = 1 := by
  have hQ : (x : ℚ_[p]) ^ 2 + d * (y : ℚ_[p]) ^ 2 = 1 := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℚ_[p])) hxy
  have hy := y_norm_le_one d hd _ _ hQ
  have hx := x_norm_le_one d _ _ hy hQ
  have hy' : ‖(y : ℂ_[p])‖ ≤ 1 := by rw [normC_ratCast]; exact hy
  have hx' : ‖(x : ℂ_[p])‖ ≤ 1 := by rw [normC_ratCast]; exact hx
  have hdC : ‖(d : ℂ_[p])‖ ≤ 1 := by
    have h1 := normC_ratCast (p := p) (d : ℚ)
    push_cast at h1
    rw [h1]
    exact natCast_norm_le_one d
  have hγ1 : ‖γ‖ ≤ 1 := by
    have h2 : ‖γ‖ ^ 2 ≤ 1 := by rw [← norm_pow, hγ, norm_neg]; exact hdC
    nlinarith [norm_nonneg γ]
  have hC : (x : ℂ_[p]) ^ 2 + d * (y : ℂ_[p]) ^ 2 = 1 := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℂ_[p])) hxy
  have hprod : ((x : ℂ_[p]) + y * γ) * ((x : ℂ_[p]) - y * γ) = 1 := by
    linear_combination hC - (y : ℂ_[p]) ^ 2 * hγ
  have hyγ : ‖(y : ℂ_[p]) * γ‖ ≤ 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg (y : ℂ_[p]), norm_nonneg γ]
  have hA : ‖(x : ℂ_[p]) + y * γ‖ ≤ 1 :=
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx' hyγ)
  have hB : ‖(x : ℂ_[p]) - y * γ‖ ≤ 1 :=
    sub_eq_add_neg (x : ℂ_[p]) (y * γ) ▸
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx' (by rwa [norm_neg]))
  have hAB : ‖(x : ℂ_[p]) + y * γ‖ * ‖(x : ℂ_[p]) - y * γ‖ = 1 := by
    rw [← norm_mul, hprod, norm_one]
  refine le_antisymm hA ?_
  nlinarith [norm_nonneg ((x : ℂ_[p]) + y * γ), norm_nonneg ((x : ℂ_[p]) - y * γ)]
end PI.UnitaryGroupMassFormula.ProdUnitInert
