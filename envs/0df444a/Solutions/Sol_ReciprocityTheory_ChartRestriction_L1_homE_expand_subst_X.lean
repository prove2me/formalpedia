-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.homE_expand_subst_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:44:31.922264+00:00
-- url     : https://prove2.me/submissions/2b7e45ee-75c1-4dbb-b33e-a5bfda1cd836

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
theorem _root_.solution (hl0 : l ≠ 0) (f : PowerSeries K) (i : Fin 2) :
    MvPowerSeries.expand l hl0 (f.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K)) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K)
        (f.subst ((X : PowerSeries K) ^ l) : PowerSeries K) := by
  rw [PowerSeries.expand_subst l hl0 (PowerSeries.HasSubst.X i), MvPowerSeries.expand_X,
    PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hl0) (PowerSeries.HasSubst.X i),
    PowerSeries.subst_pow (PowerSeries.HasSubst.X i), PowerSeries.subst_X (PowerSeries.HasSubst.X i)]
end ReciprocityTheory.ChartRestriction.L1
