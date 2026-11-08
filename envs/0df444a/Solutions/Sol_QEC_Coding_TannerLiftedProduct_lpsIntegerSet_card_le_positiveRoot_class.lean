-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIntegerSet_card_le_positiveRoot_class
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:06:38.006116+00:00
-- url     : https://prove2.me/submissions/9e6ec709-4cd6-4381-a82e-9e24ac425a2f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerSet_card_le_negativeRoot_class

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (s : Finset ℤ) (r M : ℕ)
    (hs : ∀ x ∈ s, -(r : ℤ) ≤ x ∧ x ≤ (r : ℤ) ∧ (M : ℤ) ∣ x-(r : ℤ)) :
    s.card ≤ 2*r/M+1 := by
  classical
  have he : (s.image (fun x => -x)).card=s.card := Finset.card_image_of_injective s neg_injective
  rw [← he]
  apply lpsIntegerSet_card_le_negativeRoot_class _ r M
  intro y hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  have hh := hs x hx
  refine ⟨by omega, by omega, ?_⟩
  have hd : (M : ℤ) ∣ -(x-(r : ℤ)) := dvd_neg.mpr hh.2.2
  have he : -(x-(r : ℤ))=-x+(r : ℤ) := by ring
  rw [he] at hd
  exact hd
end QEC.Coding.TannerLiftedProduct
