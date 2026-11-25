-- Prove2me | solution 1 for PI.VolStabW.VolAAW.vol_one_of_ann
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:03:10.932709+00:00
-- url     : https://prove2.me/submissions/640c4c0e-251c-4d16-9c5d-4af0d9f9c582

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolA
import Theorems.Thm_PI_VolStabW_SdUniqW_transform_indicator


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]
namespace PI.VolStabW.VolAAW
theorem _root_.solution {μ : Measure V} {χ : V → V → ℂ} (hμ : SelfDual μ χ)
    (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (L : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V)) (hA : ann χ (L : Set V) = L) :
    μ (L : Set V) = 1 := by
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
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂μ = (L : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) y := by
    intro y
    rw [hΦ, transform_indicator μ χ hχ L hLo y, hA]
  have hfin : μ (L : Set V) < ⊤ := hLc.measure_lt_top
  have hI : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ := by
    have e : (fun y => ∫ x, Φ x * χ x y ∂μ) = (L : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) :=
      funext hT
    rw [e, integrable_indicator_iff hLo.measurableSet]
    exact integrableOn_const hfin.ne
  have h0 := hμ.2 Φ hΦc hΦs hI 0
  have e1 : (fun y => (∫ x, Φ x * χ x y ∂μ) * χ y 0) = fun y => ((c : ℝ) : ℂ) * (Φ y * χ y 0) := by
    funext y
    rw [hT y]
    by_cases hy : y ∈ (L : Set V) <;> simp [hΦ, hy]
  rw [e1, integral_const_mul, hΦ, transform_indicator μ χ hχ L hLo 0, hA,
    Set.indicator_of_mem (SetLike.mem_coe.2 L.zero_mem), neg_zero,
    Set.indicator_of_mem (SetLike.mem_coe.2 L.zero_mem)] at h0
  have h1 : c * c = 1 := by exact_mod_cast h0
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hc1 : c = 1 := by nlinarith
  rw [hc, measureReal_def, ENNReal.toReal_eq_one_iff] at hc1
  exact hc1
end PI.VolStabW.VolAAW
