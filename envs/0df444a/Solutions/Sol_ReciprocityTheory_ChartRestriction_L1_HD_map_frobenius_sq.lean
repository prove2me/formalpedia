-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.HD.map_frobenius_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:33:49.293279+00:00
-- url     : https://prove2.me/submissions/4b18f036-5e94-4482-b856-a7e4e401e4a2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SubstOfLog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_iff_divBy_one


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
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}
namespace ReciprocityTheory.ChartRestriction.L1
namespace HD
theorem _root_.solution (hF : FrobField K l σ) (h : HD σ lam Φ A a) :
    HD σ (PowerSeries.map (σ.comp σ) lam) (MvPowerSeries.map (σ.comp σ) Φ)
      (PowerSeries.map (σ.comp σ) A) a := by
  have hτa : (σ.comp σ) a = a := h.a_sq
  have e := congrArg (PowerSeries.map (σ.comp σ)) h.Alog
  rw [map_mul, PowerSeries.map_C, hτa] at e
  have e2 := congrArg (MvPowerSeries.map (σ.comp σ)) h.log
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, h.a_ne, h.a_sq⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h.lam0, map_zero]
  · rw [PowerSeries.coeff_map, h.lam1, map_one]
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.Φ0, map_zero]
  · refine (integralMv_iff_divBy_one _).mpr fun d => ?_
    rw [MvPowerSeries.coeff_map, RingHom.comp_apply, hF.isom, hF.isom]
    exact (integralMv_iff_divBy_one Φ).mp h.Φint d
  · have hX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
      fun i => PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
    unfold atX atY at e2 ⊢
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h.Φ0), map_add,
      PowerSeries.map_subst (hX 0), PowerSeries.map_subst (hX 1), MvPowerSeries.map_X,
      MvPowerSeries.map_X] at e2
    exact e2
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h.A0, map_zero]
  · unfold IntegralPS
    intro n
    rw [PowerSeries.coeff_map, RingHom.comp_apply, hF.isom, hF.isom]
    exact h.Aint n
  · have e' : MvPowerSeries.map (σ.comp σ) (lam.subst A) = C a * PowerSeries.map (σ.comp σ) lam := e
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' h.A0)] at e'
    exact e'
end HD
end ReciprocityTheory.ChartRestriction.L1
