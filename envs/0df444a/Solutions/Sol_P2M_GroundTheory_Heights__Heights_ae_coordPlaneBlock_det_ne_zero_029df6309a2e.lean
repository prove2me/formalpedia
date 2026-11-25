-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ae_coordPlaneBlock_det_ne_zero_029df6309a2e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:07:04.667813+00:00
-- url     : https://prove2.me/submissions/bb84dd03-b964-4e7e-bddd-eaacb716727c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_coordPlaneDetPoly_d84d2f98ec4d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coordPlaneDetPoly_ne_zero_7680b3290aa7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_measurePreserving_curry_matrix_e2df5b44d13a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_ae_eval_ne_zero_e1e014cbbf7d


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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (m k : ℕ) :
    ∀ᵐ π : Fin m → Fin (m + k) → ℂ, (coordPlaneBlock π).det ≠ 0 := by
  have hcover : (⋃ r : ℕ, LogInt.polydisc (Fin m × Fin (m + k)) r) = Set.univ := by
    refine Set.eq_univ_of_forall fun u => ?_
    obtain ⟨r, hr⟩ := exists_nat_ge (∑ ij, ‖u ij‖)
    refine Set.mem_iUnion.2 ⟨r, ?_⟩
    simp only [LogInt.polydisc, Set.mem_pi, Set.mem_univ, forall_const, Metric.mem_closedBall,
      dist_zero_right]
    intro ij
    exact (Finset.single_le_sum (fun ij _ => norm_nonneg (u ij)) (Finset.mem_univ ij)).trans hr
  have hpoly : ∀ᵐ u : Fin m × Fin (m + k) → ℂ, eval u (coordPlaneDetPoly m k) ≠ 0 := by
    rw [← Measure.restrict_univ (μ := (volume : Measure (Fin m × Fin (m + k) → ℂ))), ← hcover,
      ae_restrict_iUnion_iff]
    exact fun r => LogInt.ae_eval_ne_zero _ (coordPlaneDetPoly_ne_zero m k) r
  have hp := measurePreserving_curry_matrix m (m + k)
  change ∀ᵐ π ∂(Measure.pi fun _ : Fin m => (volume : Measure (Fin (m + k) → ℂ))), _
  rw [← hp.map_eq, (MeasurableEquiv.curry _ _ _).measurableEmbedding.ae_map_iff]
  filter_upwards [hpoly] with u hu
  rwa [eval_coordPlaneDetPoly] at hu
end GroundTheory.Heights₂.Heights
