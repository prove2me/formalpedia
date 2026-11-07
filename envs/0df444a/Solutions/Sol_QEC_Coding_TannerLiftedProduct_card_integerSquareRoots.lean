-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_integerSquareRoots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:37:51.328218+00:00
-- url     : https://prove2.me/submissions/4c5c9411-637d-40ab-b0c4-806f522978ff

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_integerSquareRoots_sq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (n : ℕ) :
    (integerSquareRoots n).card =
      if n = 0 then 1 else if IsSquare n then 2 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · by_cases hs : IsSquare n
    · rw [isSquare_iff_exists_sq] at hs
      obtain ⟨m, rfl⟩ := hs
      have hm : 0 < m := by
        by_contra h
        push Not at h
        simp_all
      have hsq : IsSquare (m ^ 2) := by
        rw [isSquare_iff_exists_sq]
        exact ⟨m, rfl⟩
      rw [if_neg hn, if_pos hsq]
      exact card_integerSquareRoots_sq m hm
    · have hempty : integerSquareRoots n = ∅ := by
        ext z
        simp only [mem_integerSquareRoots_iff, Finset.notMem_empty, iff_false]
        intro hz
        apply hs
        rw [isSquare_iff_exists_sq]
        refine ⟨z.natAbs, ?_⟩
        rw [← Nat.cast_inj (R := ℤ), Nat.cast_pow, Int.natCast_natAbs,
          sq_abs, hz]
      simp [hn, hs, hempty]
end QEC.Coding.TannerLiftedProduct
