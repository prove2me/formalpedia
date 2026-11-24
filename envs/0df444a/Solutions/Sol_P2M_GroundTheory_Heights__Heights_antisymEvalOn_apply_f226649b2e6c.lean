-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_antisymEvalOn_apply_f226649b2e6c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:52.501801+00:00
-- url     : https://prove2.me/submissions/3647a998-4ee7-424d-a546-15dc188f2867

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymStability

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {T : Type*} {N : ℕ} (Ω : Set (T × Fin N → ℝ))
    (p : MvPolynomial (T × Fin N) ℝ) (x : Ω) : antisymEvalOn Ω p x = eval (x : T × Fin N → ℝ) p :=
  rfl
end GroundTheory.Heights₂.Heights
