-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_secForm_ecd84404e055
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:22:45.578175+00:00
-- url     : https://prove2.me/submissions/a8d9e7f1-c1cc-41e4-bfbd-b2885e96649f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_cx_85517b06cadd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_X_2b090bd40426

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.ChartDomain
variable {D : Type} [CommRing D] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)
namespace GroundTheory.Heights₂.Heights.Vertical.ChartDomain
theorem _root_.solution (i : Fin e) :
    fromPoly Q j e (∑ m, X (.inl (i, m)) * cx Q j e m) = 0 := by
  have hmem : secForm (X : Par e n → MvPolynomial (Par e n) D) i ∈ secI Q e :=
    Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
  rw [← toChart_eq_zero Q j hmem]
  simp only [map_sum, map_mul, fromPoly_X, fromPoly_cx, secForm, linForm]
end GroundTheory.Heights₂.Heights.Vertical.ChartDomain
