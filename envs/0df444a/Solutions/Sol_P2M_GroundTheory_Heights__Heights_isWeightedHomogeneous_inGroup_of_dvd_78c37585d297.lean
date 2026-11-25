-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isWeightedHomogeneous_inGroup_of_dvd_78c37585d297
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:58:56.858234+00:00
-- url     : https://prove2.me/submissions/4f008673-8c26-41e8-a730-f4023c01ccd6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isWeightedHomogeneous_of_mul_left_246006f8ee8f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMultiHomog_iff_4e11cc8773b5

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
variable {k n : ℕ} {F : Type} [Field F]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {f g : MvPolynomial (Fin k × Fin n) F} {δ : ℕ}
    (hf : IsMultiHomog δ f) (hf0 : f ≠ 0) (hgf : g ∣ f) (i : Fin k) :
    ∃ a, IsWeightedHomogeneous (inGroup i) g a := by
  obtain ⟨r, rfl⟩ := hgf
  exact isWeightedHomogeneous_of_mul_left ((isMultiHomog_iff δ _).mp hf i) (left_ne_zero_of_mul hf0)
    (right_ne_zero_of_mul hf0)
end GroundTheory.Heights₂.Heights
