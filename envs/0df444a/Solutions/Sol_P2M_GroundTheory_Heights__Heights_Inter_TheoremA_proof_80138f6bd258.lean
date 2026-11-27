-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_TheoremA_proof_80138f6bd258
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:06:49.356094+00:00
-- url     : https://prove2.me/submissions/ae2303e1-2f8b-4bd1-930c-2fb715cbaa3a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_fam_lamLine_expand_e4a84c081deb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_tsgPoly_coeff_odd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_tsgPoly_coeff_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_tsgPoly_volPoly_coeff_even


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace TheoremA
theorem _root_.solution (hP0 : ProjectivePointSetting.Statement) (hA' : PropAPrime.Statement) : TheoremA.Statement := by
  intro I hI D S X A hX hA hAb c
  have hfam : IsIntersectionFamily (I T.YBlk S.YIdx) := hI T.YBlk S.YIdx
  have hXs : IsSmoothHerm X := hX.2.1
  obtain ⟨Q, hQdef⟩ : ∃ Q : Polynomial ℝ, Q = ∑ j ∈ Finset.range (D + 1 + 1),
      Polynomial.C (((D + 1).choose j : ℝ) * ((1 / 2 : ℝ) ^ j * I T.YBlk S.YIdx S.YY (D + 1) (mix j X A)) *
        ((-1) ^ j + 1)) * Polynomial.X ^ j := ⟨_, rfl⟩
  have hQc : ∀ m, Q.coeff m = ((D + 1).choose m : ℝ) *
      ((1 / 2 : ℝ) ^ m * I T.YBlk S.YIdx S.YY (D + 1) (mix m X A)) * ((-1) ^ m + 1) := by
    intro m
    rw [hQdef]
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · rfl
    · rw [Nat.choose_eq_zero_of_lt (by simpa using hm)]
      simp
  have hQ : Q = tsgPoly D kappa (volPoly D fun j =>
      (1 / 2 : ℝ) ^ j * ptsIntegral S.YY (pot (mix j X A : Fin D → HermLine S.YIdx)) (fun _ => 1)) := by
    ext m
    rw [hQc]
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · have h0 : I T.YBlk S.YIdx S.YY (D + 1) (mix 0 X A) = 0 := by
          have hm : (mix 0 X A : Fin (D + 1) → HermLine S.YIdx) = fun _ => A := funext fun i => by simp [mix]
          rw [hm]
          exact hP0 I hI D S A hA hAb
        rw [mul_zero, h0, tsgPoly_coeff_zero]
        simp
      · rw [tsgPoly_volPoly_coeff_even D _ kappa k hk, (even_two_mul k).neg_one_pow]
        by_cases hkD : 2 * k ≤ D + 1
        · rw [hA' I hI D S X A hX hA hAb k hk hkD]
          obtain ⟨i, hi⟩ : ∃ i, 2 * k = i + 1 := ⟨2 * k - 1, by omega⟩
          rw [hi, Nat.add_sub_cancel]
          ring
        · rw [Nat.choose_eq_zero_of_lt (by omega : D + 1 < 2 * k)]
          simp
    · rw [tsgPoly_coeff_odd, (odd_two_mul_add_one k).neg_one_pow]
      simp
  rw [fam_lamLine_expand hfam S.arithYY hA hXs c, fam_lamLine_expand hfam S.arithYY hA hXs (-c), ← mul_add,
    ← hQ, hQdef]
  congr 1
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Int.cast_neg, neg_neg]
  rw [neg_div, neg_pow, div_eq_mul_one_div (c : ℝ) 2, mul_pow]
  ring
end TheoremA
end GroundTheory.Heights₂.Heights.Inter
