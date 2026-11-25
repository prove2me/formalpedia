-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteFibreCentredEquation_centredPoly_coeff_top_145162f01264
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:32:06.985276+00:00
-- url     : https://prove2.me/submissions/54d46c10-9ba2-48f7-8e78-f2e9e42cc8fd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreCentredEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteFibreCentredEquation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteFibreCentredEquation_centredPoly_coeff_364200b5094e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace FiniteFibreCentredEquation
theorem _root_.solution (a : ℂ) {k : ℕ} (c : Fin k → ℂ) : (FiniteFibreCentredEquation.centredPoly a c).coeff k = 1 := by
  rw [FiniteFibreCentredEquation.centredPoly_coeff]
  have h1 : ((X - C a) ^ k).coeff k = 1 := by
    have h := ((monic_X_sub_C a).pow k).coeff_natDegree
    rwa [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one] at h
  have h2 : ∀ j : Fin k, ((X - C a) ^ (j : ℕ)).coeff k = 0 := fun j =>
    coeff_eq_zero_of_natDegree_lt (by
      rw [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one]; exact j.isLt)
  simp [h1, h2]
end FiniteFibreCentredEquation
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
