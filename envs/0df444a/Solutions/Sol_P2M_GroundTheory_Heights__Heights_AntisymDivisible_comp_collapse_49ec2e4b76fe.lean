-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AntisymDivisible_comp_collapse_49ec2e4b76fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:34:18.617272+00:00
-- url     : https://prove2.me/submissions/2d37e3a5-9aff-486d-ac8d-5c0b23c0a7d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible

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
open GroundTheory.Heights₂.Heights.AntisymDivisible
variable {σ : Type*} [DecidableEq σ]
namespace GroundTheory.Heights₂.Heights.AntisymDivisible
theorem _root_.solution {u v : σ} (x : σ → ℝ) (hx : x u = x v) : x ∘ collapse u v = x := by
  funext w
  simp only [Function.comp, collapse]
  split_ifs with h
  · subst h; exact hx.symm
  · rfl
end GroundTheory.Heights₂.Heights.AntisymDivisible
