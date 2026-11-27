-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjSecDegree_proof_aeb814246b30
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:07:34.982004+00:00
-- url     : https://prove2.me/submissions/712ffccb-87fa-49ea-bbda-0bf32838ce68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjSecDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjSecDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjSecDegree_finrank_eq_990c4dd01280

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
namespace GroundTheory.Heights₂.Heights
namespace ProjSecDegree
theorem _root_.solution : ProjSecDegree.Statement := by
  intro n e J A
  let : Algebra (MvPolynomial (Fin (e + 1)) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (ComplexSets.projHom J A).toRingHom.toAlgebra
  exact ProjSecDegree.finrank_eq J A fun _ => rfl
end ProjSecDegree
end GroundTheory.Heights₂.Heights
