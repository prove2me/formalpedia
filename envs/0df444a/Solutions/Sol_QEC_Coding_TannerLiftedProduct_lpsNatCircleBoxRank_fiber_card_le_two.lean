-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsNatCircleBoxRank_fiber_card_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:58:01.798803+00:00
-- url     : https://prove2.me/submissions/4d0d943d-9d97-41e1-97f6-358d7e903eb4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerCircleThinBox_no_three_distinct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatPair_intCast_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatSameQuotient_abs_sub_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatCircleBoxRank_eq_imp_quotients_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (s : Finset (ℕ × ℕ)) (n M L j : ℕ)
    (hL : 0 < L) (hsmall : 2*L^6 < n)
    (hs : ∀ a ∈ s, a.1^2+a.2^2=n)
    (hB : ∀ a ∈ s, a.1/L ≤ M ∧ a.2/L ≤ M) :
    (s.filter fun a => lpsNatCircleBoxRank M L a = j).card ≤ 2 := by
  classical
  by_contra h
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp (by omega :
    2 < (s.filter fun a => lpsNatCircleBoxRank M L a = j).card)
  obtain ⟨haS,haR⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbS,hbR⟩ := Finset.mem_filter.mp hb
  obtain ⟨hcS,hcR⟩ := Finset.mem_filter.mp hc
  have qab := lpsNatCircleBoxRank_eq_imp_quotients_eq a b n M L (hs a haS) (hs b hbS)
    (hB a haS) (hB b hbS) (haR.trans hbR.symm)
  have qac := lpsNatCircleBoxRank_eq_imp_quotients_eq a c n M L (hs a haS) (hs c hcS)
    (hB a haS) (hB c hcS) (haR.trans hcR.symm)
  have qbc := lpsNatCircleBoxRank_eq_imp_quotients_eq b c n M L (hs b hbS) (hs c hcS)
    (hB b hbS) (hB c hcS) (hbR.trans hcR.symm)
  have haZ : (a.1 : ℤ)^2+(a.2 : ℤ)^2=(n : ℤ) := by exact_mod_cast hs a haS
  have hbZ : (b.1 : ℤ)^2+(b.2 : ℤ)^2=(n : ℤ) := by exact_mod_cast hs b hbS
  have hcZ : (c.1 : ℤ)^2+(c.2 : ℤ)^2=(n : ℤ) := by exact_mod_cast hs c hcS
  have he := lpsIntegerCircleThinBox_no_three_distinct
    ((a.1 : ℤ),(a.2 : ℤ)) ((b.1 : ℤ),(b.2 : ℤ)) ((c.1 : ℤ),(c.2 : ℤ))
    (n : ℤ) (L : ℤ) (by positivity) (by positivity) (by exact_mod_cast hsmall)
    haZ hbZ hcZ
    (lpsNatSameQuotient_abs_sub_le _ _ L hL qab.1)
    (lpsNatSameQuotient_abs_sub_le _ _ L hL qab.2)
    (lpsNatSameQuotient_abs_sub_le _ _ L hL qac.1)
    (lpsNatSameQuotient_abs_sub_le _ _ L hL qac.2)
    (lpsNatSameQuotient_abs_sub_le _ _ L hL qbc.1)
    (lpsNatSameQuotient_abs_sub_le _ _ L hL qbc.2)
  rcases he with he | he | he
  · exact hab (lpsNatPair_intCast_injective he)
  · exact hac (lpsNatPair_intCast_injective he)
  · exact hbc (lpsNatPair_intCast_injective he)
end QEC.Coding.TannerLiftedProduct
