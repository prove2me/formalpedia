-- Prove2me | solution 1 for ReciprocityTheory.Cheb.rsgn_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:57:36.635536+00:00
-- url     : https://prove2.me/submissions/e114f9b7-b972-46d2-ac11-32f406135386

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
import Theorems.Thm_ReciprocityTheory_Cheb_sign_add_of_abs_lt
import Theorems.Thm_P2M_ReciprocityTheory_Cheb_normAtPlace_le_norm__43bb5f9414e5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
variable {y k : mixedSpace E} {B a : ℝ}
namespace ReciprocityTheory.Cheb
theorem _root_.solution (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a) (hy : ∀ w, a ≤ normAtPlace w y) :
    rsgn (y + k) = rsgn y := by
  unfold rsgn
  refine Finset.prod_congr rfl fun w _ => ?_
  have h1 : |k.1 w| ≤ B := by
    have := normAtPlace_le_norm' w.1 k
    rw [normAtPlace_apply_of_isReal w.2] at this
    exact (Real.norm_eq_abs _ ▸ this).trans hk
  have h2 : a ≤ |y.1 w| := by
    have := hy w.1
    rwa [normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs] at this
  have h3 : SignType.sign ((y + k).1 w) = SignType.sign (y.1 w) := by
    rw [Prod.fst_add, Pi.add_apply]
    exact sign_add_of_abs_lt (a := y.1 w) (e := k.1 w) (by linarith)
  rw [h3]
end ReciprocityTheory.Cheb
