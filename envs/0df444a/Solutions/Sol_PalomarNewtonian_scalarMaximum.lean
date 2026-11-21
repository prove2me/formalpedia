-- Prove2me | solution 1 for PalomarNewtonian.scalarMaximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:04:59.927361+00:00
-- url     : https://prove2.me/submissions/b0becbdf-e8de-46fa-a153-e64ad615b4c6

module
public import Definitions.Def_NewtonianLipschitz
public import Definitions.Def_NewtonianLipschitz_Solution_74f12a8
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_cons
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_nil
public import Theorems.Thm_NewtonianLipschitz_candidateCoefficient_eq
public import Theorems.Thm_NewtonianLipschitz_candidateCoefficient_le_at_criticalPoint
public import Theorems.Thm_NewtonianLipschitz_candidateCriticalPoint_spec
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_two
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_zero
public import Theorems.Thm_NewtonianLipschitz_cycleVec_one
public import Theorems.Thm_NewtonianLipschitz_cycleVec_two
public import Theorems.Thm_NewtonianLipschitz_cycleVec_zero
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_one
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_two
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_zero
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_stationaryCubic_eq
public import Theorems.Thm_NewtonianLipschitz_stationaryCubic_root_unique_on_unitInterval
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_one
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_two
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_zero
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_one
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_two
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_zero
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_cons
attribute [local simp] NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_nil
attribute [local simp] NewtonianLipschitz.coordinateAbs_apply
attribute [local simp] NewtonianLipschitz.cycleIndex_one
attribute [local simp] NewtonianLipschitz.cycleIndex_two
attribute [local simp] NewtonianLipschitz.cycleIndex_zero
attribute [local simp] NewtonianLipschitz.cycleVec_one
attribute [local simp] NewtonianLipschitz.cycleVec_two
attribute [local simp] NewtonianLipschitz.cycleVec_zero
attribute [local simp] NewtonianLipschitz.normalizedVector_one
attribute [local simp] NewtonianLipschitz.normalizedVector_two
attribute [local simp] NewtonianLipschitz.normalizedVector_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.swapYZIndex_one
attribute [local simp] NewtonianLipschitz.swapYZIndex_two
attribute [local simp] NewtonianLipschitz.swapYZIndex_zero
attribute [local simp] NewtonianLipschitz.swapYZVec_one
attribute [local simp] NewtonianLipschitz.swapYZVec_two
attribute [local simp] NewtonianLipschitz.swapYZVec_zero
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero



set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace PalomarNewtonian
theorem _root_.solution :
    ∃ t : ℝ,
      (9 / 50 : ℝ) ≤ t ∧
      t ≤ (1 / 5 : ℝ) ∧
      2 * t ^ 3 - 8 * t ^ 2 - 4 * t + 1 = 0 ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        (2 + 6 * s - 2 * s ^ 2) /
          (Real.sqrt (1 + 2 * s ^ 2)) ^ 5 ≤
        (2 + 6 * t - 2 * t ^ 2) /
          (Real.sqrt (1 + 2 * t ^ 2)) ^ 5) ∧
      (∀ u : ℝ,
        (9 / 50 : ℝ) ≤ u →
        u ≤ (1 / 5 : ℝ) →
        2 * u ^ 3 - 8 * u ^ 2 - 4 * u + 1 = 0 →
        u = t) := by
  obtain ⟨hl, hr, hz⟩ := candidateCriticalPoint_spec
  refine ⟨candidateCriticalPoint, hl, hr, ?_, ?_, ?_⟩
  · simpa only [stationaryCubic_eq] using hz
  · intro s hs0 hs1
    have h :=
      candidateCoefficient_le_at_criticalPoint s ⟨hs0, hs1⟩
    simpa only [candidateCoefficient_eq] using h
  · intro u hul hur huz
    apply stationaryCubic_root_unique_on_unitInterval
      u candidateCriticalPoint
      ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩
    · simpa only [stationaryCubic_eq] using huz
    · exact hz
end PalomarNewtonian
