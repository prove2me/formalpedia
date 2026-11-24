-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjChowNonzero_aeval_smul_of_isHomogeneous_95fca94e9459
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:47.238198+00:00
-- url     : https://prove2.me/submissions/162889ce-21c2-46a6-b910-77c8c2cf09d2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjChowNonzero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjChowNonzero

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ProjChowNonzero
namespace GroundTheory.Heights₂.Heights.ProjChowNonzero
theorem _root_.solution {Ω : Type*} [Field Ω] [Algebra ℂ Ω] {n m : ℕ}
    {φ : MvPolynomial (Fin n) ℂ} (hφ : φ.IsHomogeneous m) (c : Ω) (x : Fin n → Ω) :
    aeval (c • x) φ = c ^ m * aeval x φ := by
  simp only [aeval_def, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg := hφ.degree_eq_sum_deg_support hd
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hdeg]
  ring
end GroundTheory.Heights₂.Heights.ProjChowNonzero
