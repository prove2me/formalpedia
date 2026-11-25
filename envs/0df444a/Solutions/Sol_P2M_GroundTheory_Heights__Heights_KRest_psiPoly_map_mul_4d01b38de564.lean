-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KRest_psiPoly_map_mul_4d01b38de564
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:01:14.7946+00:00
-- url     : https://prove2.me/submissions/bf0c192d-e062-423d-836a-02678ffd99c1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RestCutBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_coeff_psiPoly_9cd5be07914d

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
open GroundTheory.Heights₂.Heights.KRest
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.KRest
theorem _root_.solution {σ : Type*} (ψ : ℝ →ₗ[ℚ] ℚ) (A : MvPolynomial σ ℚ)
    (P : MvPolynomial σ ℝ) : psiPoly ψ (map (algebraMap ℚ ℝ) A * P) = A * psiPoly ψ P := by
  classical
  ext β
  rw [coeff_psiPoly, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_map, coeff_psiPoly, ← Algebra.smul_def, ψ.map_smul, smul_eq_mul]
end GroundTheory.Heights₂.Heights.KRest
