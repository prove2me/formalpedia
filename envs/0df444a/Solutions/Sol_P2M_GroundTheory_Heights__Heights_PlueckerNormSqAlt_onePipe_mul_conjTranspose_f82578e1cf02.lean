-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PlueckerNormSqAlt_onePipe_mul_conjTranspose_f82578e1cf02
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:47:13.980869+00:00
-- url     : https://prove2.me/submissions/ce0e0248-0880-4bb1-8d33-f66e2646abf2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPlueckerNormSq

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
open Matrix Finset
noncomputable section
open GroundTheory.Heights₂.Heights.PlueckerNormSqAlt
namespace GroundTheory.Heights₂.Heights.PlueckerNormSqAlt
theorem _root_.solution {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) :
    onePipe Z * (onePipe Z)ᴴ = 1 + Z * Zᴴ := by
  ext a b
  simp only [mul_apply, conjTranspose_apply, onePipe, of_apply, Fin.sum_univ_add, Fin.append_left,
    Fin.append_right, Matrix.add_apply]
  congr 1
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Ne.symm hab]
end GroundTheory.Heights₂.Heights.PlueckerNormSqAlt
