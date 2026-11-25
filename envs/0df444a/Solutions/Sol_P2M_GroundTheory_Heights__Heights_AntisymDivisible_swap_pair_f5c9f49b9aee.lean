-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AntisymDivisible_swap_pair_f5c9f49b9aee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:36:21.865888+00:00
-- url     : https://prove2.me/submissions/277f2c60-97ac-4044-93a5-ab038c06ce8d

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
variable {T : Type} [Fintype T] [DecidableEq T] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.AntisymDivisible
theorem _root_.solution (τ : T) (a b i : Fin N) :
    Equiv.swap (τ, a) (τ, b) (τ, i) = (τ, Equiv.swap a b i) := by
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  split_ifs <;> simp_all
end GroundTheory.Heights₂.Heights.AntisymDivisible
