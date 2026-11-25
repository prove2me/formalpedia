-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMult_mem_of_chartEval_mem_chartPoint_99b4780cbeae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:36:34.986392+00:00
-- url     : https://prove2.me/submissions/6bb977d0-4f1a-42b2-bdd2-f8d45f966182

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartEval_chartMonomial_10c9ec8f4f92
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_mem_orbitIdeal_of_chartEval_eq_zero_9b806fb3fb56
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMult
variable {ι : Type} {n : ι → ℕ}
variable (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
variable [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.OrbitChartMult
theorem _root_.solution (hc : ∀ k, x k (c k) ≠ 0)
    {V : Ideal (MvPolynomial (Coord n) ℤ)} [hVp : V.IsPrime] (hWV : orbitIdeal x ≤ V)
    (hV : ∀ v ∈ V, ∀ e, weightedHomogeneousComponent (coordDeg n) e v ∈ V)
    (hXV : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V)
    {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ} (hF : IsWeightedHomogeneous (coordDeg n) F d)
    (hFm : chartEval x c F ∈ chartPoint x c V) : F ∈ V := by
  classical
  obtain ⟨v, hv, hvF⟩ := (Ideal.mem_map_iff_of_surjective _ (chartEval_surjective x c)).mp hFm
  have hfin := weightedHomogeneousComponent_finsupp (w := coordDeg n) v
  set S := hfin.toFinset
  have hvsum : v = ∑ e ∈ S, weightedHomogeneousComponent (coordDeg n) e v := by
    conv_lhs => rw [← sum_weightedHomogeneousComponent (w := coordDeg n) v, finsum_eq_sum _ hfin]
  set E : ι → ℕ := d + ∑ e ∈ S, e
  have hdE : d ≤ E := le_self_add
  have heE : ∀ e ∈ S, e ≤ E := fun e he ↦
    (Finset.single_le_sum (f := fun e : ι → ℕ ↦ e) (fun _ _ ↦ zero_le) he).trans le_add_self
  set G := chartMonomial c (E - d) * F -
    ∑ e ∈ S, chartMonomial c (E - e) * weightedHomogeneousComponent (coordDeg n) e v
  have hG : IsWeightedHomogeneous (coordDeg n) G E := by
    rw [← mem_weightedHomogeneousSubmodule]
    refine Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun e he ↦ ?_)
    · rw [mem_weightedHomogeneousSubmodule]
      simpa [tsub_add_cancel_of_le hdE] using (isWeightedHomogeneous_chartMonomial c (E - d)).mul hF
    · rw [mem_weightedHomogeneousSubmodule]
      simpa [tsub_add_cancel_of_le (heE e he)] using
        (isWeightedHomogeneous_chartMonomial c (E - e)).mul
          (weightedHomogeneousComponent_isWeightedHomogeneous e v)
  have hG0 : chartEval x c G = 0 := by
    simp only [G, map_sub, map_sum, map_mul, chartEval_chartMonomial x c hc, one_mul]
    rw [← map_sum, ← hvsum, hvF, sub_self]
  have hGW := mem_orbitIdeal_of_chartEval_eq_zero x c hc hG hG0
  have hmem : chartMonomial c (E - d) * F ∈ V := by
    have e : chartMonomial c (E - d) * F = G +
        ∑ e ∈ S, chartMonomial c (E - e) * weightedHomogeneousComponent (coordDeg n) e v := by
      simp only [G, sub_add_cancel]
    rw [e]
    exact V.add_mem (hWV hGW) (V.sum_mem fun e _ ↦ V.mul_mem_left _ (hV v hv e))
  have hmon : chartMonomial c (E - d) ∉ V := by
    rw [chartMonomial]
    intro h
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hXV k (hVp.mem_of_pow_mem _ hk)
  exact (hVp.mem_or_mem hmem).resolve_left hmon
end GroundTheory.Heights₂.Heights.OrbitChartMult
