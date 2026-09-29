-- Prove2me | solution 1 for TarchaBraids.thm_3_15_right_word_identification_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T09:49:01.484081+00:00
-- url     : https://prove2.me/submissions/ec6c540f-e05a-41a1-a198-08bb680aa03e

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_config_data_v1
import Definitions.Def_TarchaBraids_adjacent_word_loops_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma configProj_rightBraid_first_word_v1 {n : ℕ} (i j : Fin (n - 1)) (q : ℝ)
    (hq : q ≤ 1 / 2) :
    configProj n (rightBraidConfig n i j q) =
      configProj n (halfTwistConfig n j (2 * q)) := by
  apply congrArg (configProj n)
  apply Subtype.ext
  funext k
  change rightBraidFun n i j q k = halfTwistFun n j (2 * q) k
  unfold rightBraidFun
  rw [if_pos hq]

lemma configProj_rightBraid_middle_word_v1 {n : ℕ} (i j : Fin (n - 1)) (q : ℝ)
    (hq1 : ¬ q ≤ 1 / 2) (hq2 : q ≤ 3 / 4) :
    configProj n (rightBraidConfig n i j q) =
      configProj n (halfTwistConfig n i (4 * q - 2)) := by
  symm
  apply Quotient.sound
  refine ⟨Equiv.swap (strandIdx j) (strandIdxSucc j), ?_⟩
  funext k
  change rightBraidFun n i j q k =
    halfTwistFun n i (4 * q - 2) ((Equiv.swap (strandIdx j) (strandIdxSucc j)) k)
  unfold rightBraidFun
  rw [if_neg hq1, if_pos hq2]

lemma configProj_rightBraid_final_word_v1 {n : ℕ} (i j : Fin (n - 1)) (q : ℝ)
    (hq1 : ¬ q ≤ 1 / 2) (hq2 : ¬ q ≤ 3 / 4) :
    configProj n (rightBraidConfig n i j q) =
      configProj n (halfTwistConfig n j (4 * q - 3)) := by
  symm
  apply Quotient.sound
  refine ⟨(Equiv.swap (strandIdx i) (strandIdxSucc i)) *
      (Equiv.swap (strandIdx j) (strandIdxSucc j)), ?_⟩
  funext k
  change rightBraidFun n i j q k =
    halfTwistFun n j (4 * q - 3)
      ((Equiv.swap (strandIdx i) (strandIdxSucc i))
        ((Equiv.swap (strandIdx j) (strandIdxSucc j)) k))
  unfold rightBraidFun
  rw [if_neg hq1, if_neg hq2]

lemma configProj_rightBraid_eq_word_v1 {n : ℕ} (i j : Fin (n - 1))
    (q : unitInterval) :
    configProj n (rightBraidConfig n i j (q : ℝ)) = rightBraidWordLoop n i j q := by
  unfold rightBraidWordLoop
  rw [Path.trans_apply]
  split_ifs with hq1
  · change configProj n (rightBraidConfig n i j (q : ℝ)) =
      configProj n (halfTwistConfig n j (2 * (q : ℝ)))
    exact configProj_rightBraid_first_word_v1 i j (q : ℝ) hq1
  · rw [Path.trans_apply]
    split_ifs with hq2
    · have hq2' : (q : ℝ) ≤ 3 / 4 := by linarith
      change configProj n (rightBraidConfig n i j (q : ℝ)) =
        configProj n (halfTwistConfig n i (2 * (2 * (q : ℝ) - 1)))
      convert configProj_rightBraid_middle_word_v1 i j (q : ℝ) hq1 hq2' using 1 <;> ring
    · have hq2' : ¬ (q : ℝ) ≤ 3 / 4 := by
        intro h
        apply hq2
        linarith
      change configProj n (rightBraidConfig n i j (q : ℝ)) =
        configProj n (halfTwistConfig n j (2 * (2 * (q : ℝ) - 1) - 1))
      convert configProj_rightBraid_final_word_v1 i j (q : ℝ) hq1 hq2' using 1 <;> ring

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (q : unitInterval),
      configProj n (rightBraidConfig n i j (q : ℝ)) = rightBraidWordLoop n i j q := by
  exact fun i j q => configProj_rightBraid_eq_word_v1 i j q
