-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.isFunEqType_of_mv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:44:36.163353+00:00
-- url     : https://prove2.me/submissions/16ee5c28-3c4e-4c24-98d2-5d10bcb6c5d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SemilinNormPowSubPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgFinA

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
omit [IsUltrametricDist K] [CharZero K]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {p q : ℕ} (hq : q ≠ 0) (τ : K →+* K) (f : PowerSeries K)
    (h : IsFunEqTypeMv (ι := Unit) p q hq τ f) : IsFunEqType p q τ f := by
  unfold IsFunEqType IsFunEqTypeMv at *
  have he : (PowerSeries.map τ f).subst ((X : PowerSeries K) ^ q)
      = MvPowerSeries.expand q hq (MvPowerSeries.map τ f) := by
    first
    | rfl
    | exact (MvPowerSeries.expand_eq_subst _ _ _).symm
    | (simp only [MvPowerSeries.expand, PowerSeries.subst]; rfl)
    | (unfold MvPowerSeries.expand; rw [MvPowerSeries.coe_substAlgHom]; rfl)
    | (unfold MvPowerSeries.expand; rw [MvPowerSeries.coe_substAlgHom]; congr 1)
    | (unfold MvPowerSeries.expand; rw [MvPowerSeries.coe_substAlgHom, PowerSeries.subst]; congr 1)
  rw [he]
  unfold IntegralPS
  intro n
  first
  | exact h (Finsupp.single () n)
  | exact (by unfold IntegralMv at h; exact h (Finsupp.single () n))
end ReciprocityTheory.ChartRestriction.L1
