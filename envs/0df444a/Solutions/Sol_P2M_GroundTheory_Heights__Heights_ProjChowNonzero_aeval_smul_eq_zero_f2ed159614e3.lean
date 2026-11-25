-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjChowNonzero_aeval_smul_eq_zero_f2ed159614e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:47:33.287+00:00
-- url     : https://prove2.me/submissions/5860ef9d-0fdd-4bdb-a2e2-27077a34b318

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjChowNonzero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjChowNonzero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjChowNonzero_aeval_smul_of_isHomogeneous_95fca94e9459

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
theorem _root_.solution {Ω : Type*} [Field Ω] [Algebra ℂ Ω] {n : ℕ}
    {W : Ideal (MvPolynomial (Fin n) ℂ)} (hW : IsHomogIdeal W) {x : Fin n → Ω}
    (hx : ∀ q ∈ W, aeval x q = 0) (c : Ω) : ∀ q ∈ W, aeval (c • x) q = 0 := by
  intro q hq
  rw [← sum_homogeneousComponent q, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [aeval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous d q), hx _ (hW q hq d), mul_zero]
end GroundTheory.Heights₂.Heights.ProjChowNonzero
