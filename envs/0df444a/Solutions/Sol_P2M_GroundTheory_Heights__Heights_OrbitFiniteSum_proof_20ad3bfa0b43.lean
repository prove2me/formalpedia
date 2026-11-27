-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitFiniteSum_proof_20ad3bfa0b43
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:07:45.99043+00:00
-- url     : https://prove2.me/submissions/d91864a1-31ac-4d2d-a162-ede85d09e27e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitFiniteSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegreeRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitLocalSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitFiniteSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_coordVec_ne_zero_c6e0cd13558e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finite_support_height_77d8b03ed41f


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
open ReciprocityTheory.ChartRestriction.G NumberField
namespace GroundTheory.Heights₂.Heights
namespace OrbitFiniteSum
theorem _root_.solution (hD : OrbitDegreeRatio.Statement) (hL : OrbitLocalSum.Statement)
    (hZ : OrbitCenterZero.Statement) : OrbitFiniteSum.Statement := by
  classical
  intro ι _ _ _ n A x s hx hs
  obtain ⟨a, _, hsa, hsW⟩ := id hs
  have ht : evalCone (coordVec x) s ≠ 0 := evalCone_coordVec_ne_zero x s a hsa hsW
  have hsupp2 : (Function.support fun v : FinitePlace (coordField x) ↦
      Real.log (v (evalCone (coordVec x) s))).Finite := by
    refine Set.Finite.subset (FinitePlace.hasFiniteMulSupport ht) fun v hv h ↦ hv ?_
    simp only [h, Real.log_one]
  have hS := ((finite_support_height A x hx).union hsupp2).subset
    (Function.support_sub (fun v : FinitePlace (coordField x) ↦ finiteTerm A v (coordVec x)) _)
  have hsubF : Function.support (fun v : FinitePlace (coordField x) ↦
      finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s))) ⊆ hS.toFinset := by
    simp
  have hK : (0 : ℝ) < Module.finrank ℚ (coordField x) := by exact_mod_cast Module.finrank_pos
  have hloc : ∀ V, ∑ᶠ v ∈ {v : FinitePlace (coordField x) | orbitCenter x v = V},
      (finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s))) =
      ∑ v ∈ hS.toFinset, if orbitCenter x v = V then
        finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s)) else 0 := by
    intro V
    rw [finsum_mem_def, finsum_eq_sum_of_support_subset _
      (by rw [Set.support_indicator]; exact Set.inter_subset_right.trans hsubF)]
    exact Finset.sum_congr rfl fun v _ ↦ by simp [Set.indicator_apply]
  have hterm : ∀ V ∈ (Geo.divSupp_finite (orbitIdeal x) s).toFinset,
      (Geo.multAt (orbitIdeal x ⊔ Ideal.span {s}) V : ℝ) *
          ((Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 : ℝ) * Real.log (Geo.charOf V)) =
        (∑ v ∈ hS.toFinset, if orbitCenter x v = V then
          finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s)) else 0) *
          (Module.finrank ℚ (ratioField x) / Module.finrank ℚ (coordField x) : ℝ) := fun V hV ↦ by
    have h := hL ι n A x s hx hs V ((Geo.divSupp_finite _ _).mem_toFinset.mp hV)
    rw [hloc V] at h
    rw [mul_div_assoc', eq_div_iff hK.ne', mul_comm _ (Module.finrank ℚ (ratioField x) : ℝ), ← h,
      mul_comm]
  rw [finsum_mem_eq_finite_toFinset_sum _ (Geo.divSupp_finite _ _), Finset.sum_congr rfl hterm,
    ← Finset.sum_mul, Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl fun v _ ↦ by
      split_ifs with h
      · rfl
      · exact (hZ ι n A x s hx hs v fun h' ↦ h ((Geo.divSupp_finite _ _).mem_toFinset.mpr h')).symm,
    ← finsum_eq_sum_of_support_subset _ hsubF, hD ι n x hx]
  ring
end OrbitFiniteSum
end GroundTheory.Heights₂.Heights
