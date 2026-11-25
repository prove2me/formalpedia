-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInner_comm_e9aaf395bfd3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:42:54.24175+00:00
-- url     : https://prove2.me/submissions/8c582196-af9e-49a1-b0d7-0be4a2559c82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Theta.SecondKind
open GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
variable {f : ℕ} {p q : Fin f → ℕ}
namespace GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
theorem _root_.solution {ι : Type*} [Fintype ι] (X Y : Matrix ι ι ℂ) : tInner X Y = tInner Y X := by
  have h := trace_conjTranspose (X * Yᴴ)
  rw [conjTranspose_mul, conjTranspose_conjTranspose] at h
  rw [tInner, tInner, h, Complex.star_def, Complex.conj_re]
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
