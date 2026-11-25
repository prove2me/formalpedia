-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultiHomog_iff_0f52654b96e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:41.315211+00:00
-- url     : https://prove2.me/submissions/592b8de6-ae12-454b-9428-2c1c33a06cc5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsMultiHomogOfIsChowForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_weight_groupWeight_5a5488b15ad2

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
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsChow
theorem _root_.solution {R : Type*} [CommSemiring R] {e δ : ℕ}
    (f : MvPolynomial (Fin (e + 1) × Fin n) R) : IsMultiHomog δ f ↔ IsMultihomog f δ := by
  simp only [IsMultiHomog, IsWeightedHomogeneous, IsMultihomog, mem_support_iff, weight_groupWeight,
    funext_iff]
end GroundTheory.Heights₂.Heights.ObjectsChow
