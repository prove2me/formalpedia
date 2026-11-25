-- Prove2me | solution 1 for PI.OmLocU.Sd.vol_mul_vol_ann
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:01:30.098912+00:00
-- url     : https://prove2.me/submissions/fa8f6fe2-24f4-4e2c-b485-e9ea551a679b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnitaryOrbits_VolSqMulIndex
import Theorems.Thm_PI_VolStabSW_SdUniqW_transform_indicator


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmLocU PI.OmLocU.Sd
open MeasureTheory PI.VolStabSW.SdUniqW Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]
namespace PI.OmLocU.Sd
theorem _root_.solution {μ : Measure V} {χ : V → V → ℂ} (hμ : SelfDual μ χ)
    (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (h0 : ∀ y, χ y 0 = 1) (L L' : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V))
    (hL'c : IsCompact (L' : Set V)) (hL'o : IsOpen (L' : Set V)) (hA : ann χ (L : Set V) = L') :
    μ.real (L : Set V) * μ.real (L' : Set V) = 1 := by
  classical
  have := hμ.1
  set c : ℝ := μ.real (L : Set V) with hc
  have hcl : IsClopen (L : Set V) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  set Φ : V → ℂ := (L : Set V).indicator (fun _ => (1 : ℂ)) with hΦ
  have hΦc : Continuous Φ := by
    rw [hΦ, ← Set.piecewise_eq_indicator]
    exact continuous_const.piecewise (by simp [hcl.frontier_eq]) continuous_const
  have hΦs : HasCompactSupport Φ :=
    HasCompactSupport.intro hLc fun x hx => Set.indicator_of_notMem hx _
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂μ = (L' : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) y := by
    intro y
    rw [hΦ, transform_indicator μ χ hχ L hLo y, hA]
  have hI : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ := by
    have e : (fun y => ∫ x, Φ x * χ x y ∂μ) = (L' : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) :=
      funext hT
    rw [e, integrable_indicator_iff hL'o.measurableSet]
    exact integrableOn_const hL'c.measure_lt_top.ne
  have h1 := hμ.2 Φ hΦc hΦs hI 0
  have e1 : (fun y => (∫ x, Φ x * χ x y ∂μ) * χ y 0) =
      (L' : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) := by
    funext y
    rw [hT y, h0, mul_one]
  rw [e1, integral_indicator_const _ hL'o.measurableSet, neg_zero, hΦ,
    Set.indicator_of_mem (SetLike.mem_coe.2 L.zero_mem)] at h1
  have h2 : μ.real (L' : Set V) * c = 1 := by
    rw [Complex.real_smul] at h1
    exact_mod_cast h1
  rw [mul_comm]
  exact h2
end PI.OmLocU.Sd
