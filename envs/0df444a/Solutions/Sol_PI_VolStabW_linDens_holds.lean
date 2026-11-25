-- Prove2me | solution 1 for PI.VolStabW.linDens_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:03:52.233534+00:00
-- url     : https://prove2.me/submissions/d511ae0f-85a1-4896-989c-984ba25ac6f8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfLoc

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
open MeasureTheory Topology
namespace PI.VolStabW
theorem _root_.solution : LinDens := by
  intro n m μ ν hμ hν A hA φ hc hs _
  obtain ⟨B, hB⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hA)
  have hRI : Function.RightInverse B A := fun y => by
    simpa using congrArg (fun L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) => L y) hB
  let T := ContinuousLinearEquiv.equivOfRightInverse A B hRI
  let K := A.ker
  let lam : Measure K := Measure.addHaar
  have hT1 : ∀ x, (T x).1 = A x := fun x => rfl
  have hμT : (μ.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  obtain ⟨c, hsm⟩ : ∃ c : ENNReal, μ.map T = c • (ν.prod lam) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  let H : (Fin m → ℝ) × K → ℝ := fun w => φ (T.symm w)
  have hHc : Continuous H := hc.comp T.symm.continuous
  have hHs : HasCompactSupport H := hs.comp_homeomorph T.symm.toHomeomorph
  let s : Set K := Prod.snd '' tsupport H
  have hsc : IsCompact s := hHs.image continuous_snd
  let ψ : (Fin m → ℝ) → ℝ := fun y => ∫ k in s, H (y, k) ∂lam
  have hψc : Continuous ψ :=
    continuous_parametric_integral_of_continuous (f := fun y k => H (y, k)) hHc hsc
  have hψ : ∀ y, ∫ k, H (y, k) ∂lam = ψ y := by
    intro y
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun k hk => ?_).symm
    apply image_eq_zero_of_notMem_tsupport
    intro h'
    exact hk ⟨(y, k), h', rfl⟩
  refine ⟨fun y => c.toReal * ψ y, continuous_const.mul hψc, fun S hS => ?_⟩
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  simp only [Set.image_id]
  let Q : (Fin m → ℝ) × K → ℝ := (Prod.fst ⁻¹' S).indicator H
  have hQ : ∀ v, (A ⁻¹' S).indicator φ v = Q (T v) := by
    intro v
    simp only [Q, Set.indicator, H, ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have hQi : Integrable Q (ν.prod lam) :=
    (hHc.integrable_of_hasCompactSupport hHs).indicator (measurable_fst hSm)
  rw [← integral_indicator (hSm.preimage A.continuous.measurable)]
  simp_rw [hQ]
  have e2 : ∫ v, Q (T v) ∂μ = ∫ w, Q w ∂(μ.map T) := by
    rw [show (μ.map T) = μ.map T.toHomeomorph.toMeasurableEquiv from rfl, integral_map_equiv]
    rfl
  rw [e2, hsm, integral_smul_measure, integral_prod _ hQi, smul_eq_mul,
    ← integral_indicator hSm, ← integral_const_mul]
  congr 1
  funext y
  by_cases hy : y ∈ S
  · simp only [Q, Set.indicator, Set.mem_preimage, hy, if_true, ← hψ y]
  · simp [Q, Set.indicator, hy]
end PI.VolStabW
