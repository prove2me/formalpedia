-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.shear_preserving
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:18:24.476452+00:00
-- url     : https://prove2.me/submissions/88445705-298c-417d-84a5-c36011a5cb9c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_det_of_shear

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
theorem _root_.solution (μ : Measure E) [μ.IsAddHaarMeasure] (G : ℕ → Submodule ℝ E) (L : ℕ)
    (hG0 : G 0 = ⊤) (hL : G L = ⊥) (Φ : E → E) (hΦ : Differentiable ℝ Φ)
    (hbij : Function.Bijective Φ)
    (hsh : ∀ j x y, x - y ∈ G j → Φ x - Φ y - (x - y) ∈ G (j + 1)) : MeasurePreserving Φ μ μ := by
  have hD : ∀ x, ∀ j, ∀ v ∈ G j, fderiv ℝ Φ x v - v ∈ G (j + 1) := by
    intro x j v hv
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    have h2 : HasFDerivAt Φ (fderiv ℝ Φ x) ((fun t : ℝ => x + t • v) 0) := by
      simpa using (hΦ x).hasFDerivAt
    have hd := h2.comp_hasDerivAt (0 : ℝ) h1
    have hS : IsClosed {w : E | w - v ∈ G (j + 1)} :=
      (Submodule.closed_of_finiteDimensional (G (j + 1))).preimage (continuous_id.sub continuous_const)
    refine hS.mem_of_tendsto hd.tendsto_slope_zero (eventually_nhdsWithin_of_forall fun t ht => ?_)
    have ht0 : t ≠ 0 := Set.mem_compl_singleton_iff.mp ht
    have hmem := hsh j (x + t • v) x (by rw [add_sub_cancel_left]; exact (G j).smul_mem t hv)
    rw [add_sub_cancel_left] at hmem
    show t⁻¹ • ((Φ ∘ fun t : ℝ => x + t • v) (0 + t) - (Φ ∘ fun t : ℝ => x + t • v) 0) - v ∈ G (j + 1)
    have e : t⁻¹ • ((Φ ∘ fun t : ℝ => x + t • v) (0 + t) - (Φ ∘ fun t : ℝ => x + t • v) 0) - v =
        t⁻¹ • (Φ (x + t • v) - Φ x - t • v) := by
      simp only [Function.comp_apply, zero_add, zero_smul, add_zero, smul_sub, smul_smul,
        inv_mul_cancel₀ ht0, one_smul]
    have hm2 := (G (j + 1)).smul_mem t⁻¹ hmem
    rw [← e] at hm2
    exact hm2
  have hmeas : Measurable Φ := hΦ.continuous.measurable
  refine ⟨hmeas, ?_⟩
  have key := MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar μ MeasurableSet.univ
    (f' := fderiv ℝ Φ) (fun x _ => (hΦ x).hasFDerivAt.hasFDerivWithinAt) hbij.1.injOn
  have hdet : (fun x => ENNReal.ofReal |(fderiv ℝ Φ x).det|) = fun _ => 1 := by
    funext x
    rw [det_of_shear G L hG0 hL _ (hD x), abs_one, ENNReal.ofReal_one]
  rw [hdet] at key
  have key' : Measure.map Φ ((μ.restrict (Set.univ : Set E)).withDensity fun _ => (1 : ENNReal)) =
      μ.restrict (Φ '' (Set.univ : Set E)) := key
  have h1 : μ.withDensity (fun _ => (1 : ENNReal)) = μ := withDensity_one
  rw [Measure.restrict_univ, Set.image_univ, hbij.2.range_eq, Measure.restrict_univ, h1] at key'
  exact key'
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
