-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_MixedTwistShiftAlt_prod_map_filter_3bb7a2c79544
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:19:00.637943+00:00
-- url     : https://prove2.me/submissions/e96af8e7-4461-461d-b1de-82e4583b4374

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StMixedTwistShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StRestrLenEuler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StSubsetDiffConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PMixedTwistShift
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.MixedTwistShiftAlt
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.MixedTwistShiftAlt
theorem _root_.solution {R : Type*} [CommMonoid R] {n : ℕ} (g : Fin n → R) (T : Finset (Fin n)) :
    ∀ l : List (Fin n),
      ((l.filter (· ∈ T)).map g).prod = (l.map fun j => g j ^ (if j ∈ T then 1 else 0)).prod
  | [] => rfl
  | j :: l => by
    by_cases hj : j ∈ T <;> simp [hj, solution g T l]
end GroundTheory.Heights₂.Heights.Kleiman.MixedTwistShiftAlt
