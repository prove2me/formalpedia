-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjSecDegree_projHom_X_807c38aad575
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:47:42.183222+00:00
-- url     : https://prove2.me/submissions/879e155b-9509-4ff6-a12e-dd6046b475a0

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
theorem _root_.solution (i : Fin (e + 1)) :
    ComplexSets.projHom J A (X i) = Ideal.Quotient.mk J (ComplexSets.linPoly A i) := by
  simp [ComplexSets.projHom, ComplexSets.pullback]
end GroundTheory.Heights₂.Heights.ProjSecDegree
