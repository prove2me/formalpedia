-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjSecDegree_chartForm_projPar_2d49b4866f36
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:47:35.992877+00:00
-- url     : https://prove2.me/submissions/6e9931c2-cd65-4953-aae8-8b544c1c3c28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjSecDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjSecDegree

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
open GroundTheory.Heights₂.Heights.ProjSecDegree
variable {n e : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)
local notation "𝕂" => FractionRing (MvPolynomial (Fin (e + 1)) ℂ)
local notation "ℝt" => MvPolynomial (Fin (e + 1)) ℂ
namespace GroundTheory.Heights₂.Heights.ProjSecDegree
theorem _root_.solution :
    Vertical.chartForm (projPar A) =
      C (projVar e 0)⁻¹ * (ComplexSets.linPoly A 0).map (algebraMap ℂ 𝕂) := by
  simp only [Vertical.chartForm, linForm, projPar, ComplexSets.linPoly, map_sum, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, ← C_mul, div_eq_inv_mul]
end GroundTheory.Heights₂.Heights.ProjSecDegree
