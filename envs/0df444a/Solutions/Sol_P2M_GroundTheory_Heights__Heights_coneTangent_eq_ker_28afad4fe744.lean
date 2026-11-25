-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_coneTangent_eq_ker_28afad4fe744
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:49.904436+00:00
-- url     : https://prove2.me/submissions/36393949-ff1c-49b2-8f74-25c6f4e6040f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeJacMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacCompress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeJacMeasurable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_ker_coneJacMat_f32e4b3739d8

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
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)} {k : ℕ}
    (g : Fin k → MvPolynomial (Fin n) ℂ) (hg : Submodule.span _ (Set.range g) = J)
    {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ coneSet h J) :
    coneTangent h J y = LinearMap.ker (Matrix.toEuclideanLin (coneJacMat h g y)) := by
  ext v
  rw [mem_ker_coneJacMat]
  constructor
  · intro hv i
    exact hv (g i) (hg ▸ Submodule.subset_span ⟨i, rfl⟩)
  · intro hv q hq
    rw [← hg] at hq
    induction hq using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hv i
    | zero => simp
    | add x z _ _ hx hz => simp [add_mul, Finset.sum_add_distrib, hx, hz]
    | smul a x hxmem hx =>
      have hx0 : eval (h.pointOf y) x = 0 := hy x (hg ▸ hxmem)
      calc ∑ j, eval (h.pointOf y) (pderiv j (a • x)) * h.pointOf v j
          = eval (h.pointOf y) a * ∑ j, eval (h.pointOf y) (pderiv j x) * h.pointOf v j := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [smul_eq_mul, pderiv_mul, map_add, map_mul, map_mul, hx0]
            ring
        _ = 0 := by rw [hx, mul_zero]
end GroundTheory.Heights₂.Heights
