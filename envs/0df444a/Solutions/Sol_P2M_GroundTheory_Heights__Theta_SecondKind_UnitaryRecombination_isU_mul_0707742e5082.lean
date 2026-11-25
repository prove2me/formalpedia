-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_isU_mul_0707742e5082
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:42:46.000662+00:00
-- url     : https://prove2.me/submissions/1fa820d5-f873-46a3-833b-12df2fe061cf

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
variable (F : OrthoFrame)
namespace GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
theorem _root_.solution {p q : ℕ} {g h : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hg : IsU g)
    (hh : IsU h) : IsU (g * h) := by
  unfold IsU at *
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * indefJ p q * (g * h) = hᴴ * (gᴴ * indefJ p q * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = indefJ p q := by rw [hg, hh]
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
