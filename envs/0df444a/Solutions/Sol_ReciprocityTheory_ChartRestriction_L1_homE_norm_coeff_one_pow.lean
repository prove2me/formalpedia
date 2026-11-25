-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.homE_norm_coeff_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:36:45.86911+00:00
-- url     : https://prove2.me/submissions/cd99f573-e33c-4c79-966a-02a3c8555ab1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_DivByPartialYAtZeroSubstAtXAtY

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
theorem _root_.solution {x : K} (hg0 : constantCoeff g = 0) (h0 : ‖coeff 1 g‖ ≤ ‖x‖) (j : ℕ) :
    ‖coeff 1 (g ^ j)‖ ≤ ‖x‖ := by
  rcases j with _ | _ | j
  · simp
  · simpa using h0
  · have hX : X ∣ g := X_dvd_iff.mpr hg0
    have h2 := pow_dvd_pow_of_dvd hX (j + 1 + 1)
    rw [X_pow_dvd_iff.mp h2 1 (by omega), norm_zero]
    exact norm_nonneg _
end ReciprocityTheory.ChartRestriction.L1
