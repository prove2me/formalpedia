-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.hom_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:50:39.138123+00:00
-- url     : https://prove2.me/submissions/38772ace-5689-4752-9ff6-3f137a22913b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_DivByPartialYAtZeroSubstAtXAtY
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divBy_partialYAtZero_subst_atX_atY
import Theorems.Thm_Formalism_LT_InvIntP_Low_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LawD_coeffY_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LawD_deriv_integral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LawD_deriv_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divBy_partialYAtZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_partialYAtZero_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
variable {lam₁ lam₂ : PowerSeries K} {Φ₁ Φ₂ : MvPowerSeries (Fin 2) K} {A₁ A₂ g : PowerSeries K}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (hl1 : ‖(l : K)‖ ≤ 1) (h₁ : LawD lam₁ Φ₁) (h₂ : LawD lam₂ Φ₂)
    (hg : HomCls l Φ₁ A₁ Φ₂ A₂ g) (h0 : ‖coeff 1 g‖ ≤ ‖(l : K)‖) :
    DivBy (l : K) (derivative K g) := by
  have h1 := divBy_partialYAtZero hg.add
  rw [partialYAtZero_sub, h₁.coeffY_subst] at h1
  have h2 := divBy_partialYAtZero_subst_atX_atY (x := (l : K)) h₂.Φint hg.g0 hg.gInt h0
  have h3 : DivBy (l : K) (derivative K g * d2 Φ₁) := by
    unfold DivBy at h1 h2 ⊢
    intro n
    have h4 := IsUltrametricDist.norm_add_le_max
      (coeff n (derivative K g * d2 Φ₁ - d2 (Φ₂.subst ![atX g, atY g])))
      (coeff n (d2 (Φ₂.subst ![atX g, atY g])))
    rw [← map_add, sub_add_cancel] at h4
    exact h4.trans (max_le (h1 n) (h2 n))
  have e : derivative K g = derivative K lam₁ * (derivative K g * d2 Φ₁) := by
    linear_combination (-derivative K g) * h₁.deriv_mul
  rw [e]
  have hl := h₁.deriv_integral
  unfold DivBy at h3 ⊢
  unfold IntegralPS at hl
  intro n
  rw [coeff_mul]
  refine Finset.sum_induction _ (fun y => ‖y‖ ≤ ‖(l : K)‖)
    (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb))
    (by simp) fun p _ => ?_
  rw [norm_mul]
  calc _ ≤ 1 * ‖(l : K)‖ := mul_le_mul (hl _) (h3 _) (norm_nonneg _) zero_le_one
    _ = ‖(l : K)‖ := one_mul _
end ReciprocityTheory.ChartRestriction.L1
