-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.hom_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:23.360403+00:00
-- url     : https://prove2.me/submissions/65e0909b-6cb3-45ef-b0bb-b52c80046d53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_DivByPartialYAtZeroSubstAtXAtY
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_homE_coeff_one_subst

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
theorem _root_.solution (hA₁ : constantCoeff A₁ = 0) (hA₂ : constantCoeff A₂ = 0)
    (hg : HomCls l Φ₁ A₁ Φ₂ A₂ g) (h : ‖coeff 1 A₁ - coeff 1 A₂‖ = 1) :
    ‖coeff 1 g‖ ≤ ‖(l : K)‖ := by
  have h0 := hg.eig
  unfold DivBy at h0
  have h1 := h0 1
  have e : coeff 1 g * coeff 1 A₁ - coeff 1 A₂ * coeff 1 g =
      coeff 1 g * (coeff 1 A₁ - coeff 1 A₂) := by ring
  rw [map_sub, homE_coeff_one_subst _ _ hA₁, homE_coeff_one_subst _ _ hg.g0, e, norm_mul, h,
    mul_one] at h1
  exact h1
end ReciprocityTheory.ChartRestriction.L1
