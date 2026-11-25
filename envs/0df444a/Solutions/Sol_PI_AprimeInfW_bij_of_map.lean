-- Prove2me | solution 1 for PI.AprimeInfW.bij_of_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:18:28.977541+00:00
-- url     : https://prove2.me/submissions/2c4eb110-fcff-40a0-ae75-208238c45d6e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_DetMulRCReal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PiCoord
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PlaceAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW
open MeasureTheory Matrix
open scoped ENNReal NNReal
namespace PI.AprimeInfW
theorem _root_.solution {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F) [ν.IsAddHaarMeasure]
    (f : E →ₗ[ℝ] F) (c : ℝ≥0∞) (h0 : c ≠ 0) (htop : c ≠ ⊤) (h : μ.map f = c • ν) : Function.Bijective f := by
  have key : ∀ s : Set F, MeasurableSet s → μ ((f : E → F) ⁻¹' s) = c * ν s := by
    intro s hs
    have h1 := congrArg (fun ρ : Measure F => ρ s) h
    simp only [Measure.smul_apply, smul_eq_mul] at h1
    rwa [Measure.map_apply (LinearMap.continuous_of_finiteDimensional f).measurable hs] at h1
  have hsurj : Function.Surjective f := by
    by_contra hns
    have hr : LinearMap.range f ≠ ⊤ := fun hh => hns (LinearMap.range_eq_top.mp hh)
    have h0 : ν (LinearMap.range f : Set F) = 0 := Measure.addHaar_submodule ν _ hr
    have hm : MeasurableSet (LinearMap.range f : Set F) :=
      (Submodule.closed_of_finiteDimensional (LinearMap.range f)).measurableSet
    have h1 := key _ hm
    rw [h0, mul_zero] at h1
    have hpre : (f : E → F) ⁻¹' (LinearMap.range f : Set F) = Set.univ := by
      ext x
      simp
    rw [hpre] at h1
    exact (IsOpen.measure_pos μ isOpen_univ Set.univ_nonempty).ne' h1
  have hdim : Module.finrank ℝ E = Module.finrank ℝ F := by
    set K : Set F := Metric.closedBall 0 1 with hKdef
    have hKc : IsCompact K := isCompact_closedBall 0 1
    have hKm : MeasurableSet K := hKc.isClosed.measurableSet
    have hK0 : ν K ≠ 0 := (Metric.measure_closedBall_pos ν (0 : F) one_pos).ne'
    have hKt : ν K ≠ ⊤ := hKc.measure_lt_top.ne
    open Pointwise in
    have h2m : MeasurableSet ((2 : ℝ) • K) := (hKc.smul (2 : ℝ)).isClosed.measurableSet
    open Pointwise in
    have hpre : (f : E → F) ⁻¹' ((2 : ℝ) • K) = (2 : ℝ) • ((f : E → F) ⁻¹' K) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_smul_set]
      constructor
      · rintro ⟨y, hy, hxy⟩
        refine ⟨(1 / 2 : ℝ) • x, ?_, ?_⟩
        · rw [map_smul, ← hxy, smul_smul]
          norm_num
          exact hy
        · rw [smul_smul]
          norm_num
      · rintro ⟨y, hy, rfl⟩
        exact ⟨f y, hy, (map_smul f (2 : ℝ) y).symm⟩
    have e1 := key _ h2m
    rw [hpre, Measure.addHaar_smul, key K hKm, Measure.addHaar_smul] at e1
    set X := c * ν K with hX
    have hX0 : X ≠ 0 := mul_ne_zero h0 hK0
    have hXt : X ≠ ⊤ := ENNReal.mul_ne_top htop hKt
    have e2 : ENNReal.ofReal |(2 : ℝ) ^ Module.finrank ℝ E| * X =
        ENNReal.ofReal |(2 : ℝ) ^ Module.finrank ℝ F| * X := by
      rw [e1, hX]
      ring
    have hu : IsUnit X := isUnit_iff_exists_inv.mpr ⟨X⁻¹, ENNReal.mul_inv_cancel hX0 hXt⟩
    have e3 := hu.mul_left_inj.mp e2
    rw [ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at e3
    have e4 : (2 : ℕ) ^ Module.finrank ℝ E = 2 ^ Module.finrank ℝ F := by
      have e5 : ((2 : ℕ) : ℝ) ^ Module.finrank ℝ E = ((2 : ℕ) : ℝ) ^ Module.finrank ℝ F := by
        simpa using e3
      exact_mod_cast e5
    exact Nat.pow_right_injective (le_refl 2) e4
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩
end PI.AprimeInfW
