-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.exp_chart_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:54:37.911897+00:00
-- url     : https://prove2.me/submissions/2c20e7b4-9bc8-445d-b935-51ee2b2e260b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_exp_mem_grpN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_exp_chart_invariant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_exp_chart_embedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable {F : ℕ → Submodule ℝ A} {L : ℕ} {f g : A → A}
variable [FiniteDimensional ℝ A] {st : A →ₗ[ℝ] A} [MeasurableSpace A] [BorelSpace A]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
theorem _root_.solution (hF : IsFil F L) (hst : IsAdj F st) (μ : Measure (lieN F st))
    [μ.IsAddHaarMeasure] :
    let ν := μ.map (fun Y : lieN F st => NormedSpace.exp (Y : A))
    SigmaFinite ν ∧ ν ≠ 0 ∧ ν {x | x ∉ grpN F st} = 0 ∧ ∀ s ∈ grpN F st, ν.map (s * ·) = ν := by
  intro ν
  have hemb := exp_chart_embedding (st := st) hF
  refine ⟨hemb.sigmaFinite_map, ?_, ?_, ?_⟩
  · intro h0
    have h1 : ν Set.univ = μ Set.univ := by
      show Measure.map (fun Y : lieN F st => NormedSpace.exp (Y : A)) μ Set.univ = μ Set.univ
      rw [hemb.map_apply, Set.preimage_univ]
    rw [h0] at h1
    exact (isOpen_univ.measure_ne_zero μ Set.univ_nonempty) (by simpa using h1.symm)
  · show Measure.map (fun Y : lieN F st => NormedSpace.exp (Y : A)) μ {x | x ∉ grpN F st} = 0
    rw [hemb.map_apply]
    have e : (fun Y : lieN F st => NormedSpace.exp (Y : A)) ⁻¹' {x | x ∉ grpN F st} = ∅ := by
      ext Y
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact exp_mem_grpN hF hst Y.2
    rw [e, measure_empty]
  · intro s hs
    obtain ⟨Φ, hΦm, hΦ⟩ := exp_chart_invariant hF hst μ hs
    show Measure.map (s * ·) (Measure.map (fun Y : lieN F st => NormedSpace.exp (Y : A)) μ) =
      Measure.map (fun Y : lieN F st => NormedSpace.exp (Y : A)) μ
    rw [Measure.map_map (continuous_mul_left s).measurable hemb.measurable]
    have hcomp : (s * ·) ∘ (fun Y : lieN F st => NormedSpace.exp (Y : A)) =
        (fun Y : lieN F st => NormedSpace.exp (Y : A)) ∘ Φ := by
      funext Y
      simp [hΦ]
    rw [hcomp, ← Measure.map_map hemb.measurable hΦm.measurable, hΦm.map_eq]
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
