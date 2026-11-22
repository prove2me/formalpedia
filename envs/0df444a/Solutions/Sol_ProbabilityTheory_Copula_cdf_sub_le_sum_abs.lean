-- Prove2me | solution 1 for ProbabilityTheory.Copula.cdf_sub_le_sum_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:36.365184+00:00
-- url     : https://prove2.me/submissions/10456bf1-3859-49c1-a983-152ba44ffb54

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_CDF_Continuity
public import Theorems.Thm_ProbabilityTheory_Copula_measure_preimage_eval


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval BigOperators NNReal
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (C : Copula d) (u v : Fin d → I) :
    C.cdf u - C.cdf v ≤ ∑ i, |(u i : ℝ) - (v i : ℝ)| := by
  let strip (i : Fin d) : Set (Fin d → I) :=
    (fun x => x i) ⁻¹' uIoc (v i) (u i)
  have hsub : Iic u \ Iic v ⊆ ⋃ i, strip i := by
    intro x hx
    obtain ⟨i, hi⟩ := not_forall.mp hx.2
    refine mem_iUnion.mpr ⟨i, ?_⟩
    exact mem_uIoc.mpr (Or.inl ⟨lt_of_not_ge hi, hx.1 i⟩)
  have hstrip (i : Fin d) : C.toMeasure.real (strip i) = |(u i : ℝ) - (v i : ℝ)| := by
    change (C.toMeasure ((fun x => x i) ⁻¹' uIoc (v i) (u i))).toReal = _
    rw [C.measure_preimage_eval i measurableSet_uIoc, unitInterval.volume_uIoc,
      edist_dist, ENNReal.toReal_ofReal dist_nonneg, Subtype.dist_eq, Real.dist_eq]
  calc
    C.cdf u - C.cdf v ≤ C.toMeasure.real (Iic u \ Iic v) := le_measureReal_sdiff
    _ ≤ C.toMeasure.real (⋃ i, strip i) := measureReal_mono hsub
    _ ≤ ∑ i, C.toMeasure.real (strip i) := measureReal_iUnion_fintype_le strip
    _ = ∑ i, |(u i : ℝ) - (v i : ℝ)| := Finset.sum_congr rfl (fun i _ => hstrip i)
end ProbabilityTheory.Copula
