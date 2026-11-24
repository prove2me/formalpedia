-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HeightRecR_proof_a841a96c8521
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:25.69403+00:00
-- url     : https://prove2.me/submissions/21db11c8-138c-4753-b171-5836613245d8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitFiniteSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitArchSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_coordVec_ne_zero_c6e0cd13558e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockNonzero_sigma_8db15361a0fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_map_d62ae25f8d4a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finite_support_height_77d8b03ed41f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_log_places_eq_zero_ae84c0a90009


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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
namespace HeightRecR
theorem _root_.solution (hV : OrbitDivVertical.Statement) (hF : OrbitFiniteSum.Statement)
    (hA : OrbitArchSum.Statement) : HeightRecR.Statement := by
  intro ι _ _ _ n I A x s hx hs
  obtain ⟨a, _, hsa, hsW⟩ := id hs
  have ht : evalCone (coordVec x) s ≠ 0 := evalCone_coordVec_ne_zero x s a hsa hsW
  have e1 : Geo.recR I (orbitIdeal x) (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) A.toGeo s =
      (∑ᶠ V ∈ Geo.divSupp (orbitIdeal x) s,
        (Geo.multAt (orbitIdeal x ⊔ Ideal.span {s}) V : ℝ) *
          ((Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 : ℝ) * Real.log (Geo.charOf V))) -
      Geo.arInt (orbitIdeal x) s A.toGeo (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) := by
    unfold Geo.recR
    congr 1
    refine finsum_mem_congr rfl fun V hV' ↦ ?_
    rw [if_neg (hV ι n A x s hx hs V hV')]
    congr 4
    funext j
    exact j.elim0
  have hpos : ∀ σ : coordField x →+* ℂ, 0 < A.metric (fun k i ↦ σ (coordVec x k i)) :=
    fun σ ↦ A.metric_pos _ (blockNonzero_sigma hx σ)
  have e2 : ∀ σ : coordField x →+* ℂ,
      Real.log (‖evalCone (fun k i ↦ σ (coordVec x k i)) s‖ /
          A.metric (fun k i ↦ σ (coordVec x k i))) =
        Real.log ‖σ (evalCone (coordVec x) s)‖ -
          Real.log (A.metric (fun k i ↦ σ (coordVec x k i))) := fun σ ↦ by
    rw [evalCone_map, Real.log_div (norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr ht)) (hpos σ).ne']
  have hsupp1 : (Function.support fun v : FinitePlace (coordField x) ↦
      finiteTerm A v (coordVec x)).Finite := finite_support_height A x hx
  have hsupp2 : (Function.support fun v : FinitePlace (coordField x) ↦
      Real.log (v (evalCone (coordVec x) s))).Finite := by
    refine Set.Finite.subset (FinitePlace.hasFiniteMulSupport ht) fun v hv h ↦ hv ?_
    simp only [h, Real.log_one]
  have hprod := sum_log_places_eq_zero ht
  rw [e1, hF ι n A x s hx hs, hA ι n A x s hx hs, finsum_sub_distrib hsupp1 hsupp2,
    Finset.sum_congr rfl fun σ _ ↦ e2 σ, Finset.sum_sub_distrib, height]
  simp only [finiteTerm]
  linear_combination (-((Geo.degC (ι := blockIdx n) (orbitIdeal x) : ℝ) /
    Module.finrank ℚ (coordField x))) * hprod
end HeightRecR
end GroundTheory.Heights₂.Heights
