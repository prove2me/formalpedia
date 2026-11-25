-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjSecDegree_secForm_projPar_ed49e802b14f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:47:44.10479+00:00
-- url     : https://prove2.me/submissions/da946082-8863-43ea-a51f-87a0c5804e8c

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
theorem _root_.solution (i : Fin e) :
    Vertical.secForm (projPar A) i =
      C (projVar e i.succ) * (ComplexSets.linPoly A 0).map (algebraMap ℂ 𝕂) -
        C (projVar e 0) * (ComplexSets.linPoly A i.succ).map (algebraMap ℂ 𝕂) := by
  simp only [Vertical.secForm, linForm, projPar, ComplexSets.linPoly, map_sum, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_X, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [C_sub, C_mul, C_mul]
  ring
end GroundTheory.Heights₂.Heights.ProjSecDegree
