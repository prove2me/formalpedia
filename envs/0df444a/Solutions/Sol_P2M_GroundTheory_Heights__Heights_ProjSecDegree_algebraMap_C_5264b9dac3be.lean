-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjSecDegree_algebraMap_C_5264b9dac3be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:47:53.481179+00:00
-- url     : https://prove2.me/submissions/215190b0-0598-42e6-bf69-9567ea6f59d2

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
theorem _root_.solution (c : ℂ) : algebraMap ℝt 𝕂 (C c) = algebraMap ℂ 𝕂 c := by
  rw [IsScalarTower.algebraMap_apply ℂ ℝt 𝕂 c, MvPolynomial.algebraMap_eq]
end GroundTheory.Heights₂.Heights.ProjSecDegree
