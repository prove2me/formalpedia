-- Prove2me | solution 1 for TarchaBraids.thm_3_15_left_word_identification_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T09:49:03.85613+00:00
-- url     : https://prove2.me/submissions/c4e997b5-7f02-4495-bd1c-df56b5102600

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_config_data_v1
import Definitions.Def_TarchaBraids_adjacent_word_loops_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma configProj_leftBraid_first_word_v1 {n : ℕ} (i j : Fin (n - 1)) (q : ℝ)
    (hq : q ≤ 1 / 2) :
    configProj n (leftBraidConfig n i j q) =
      configProj n (halfTwistConfig n i (2 * q)) := by
  apply congrArg (configProj n)
  apply Subtype.ext
  funext k
  change leftBraidFun n i j q k = halfTwistFun n i (2 * q) k
  unfold leftBraidFun
  rw [if_pos hq]

lemma configProj_leftBraid_middle_word_v1 {n : ℕ} (i j : Fin (n - 1)) (q : ℝ)
    (hq1 : ¬ q ≤ 1 / 2) (hq2 : q ≤ 3 / 4) :
    configProj n (leftBraidConfig n i j q) =
      configProj n (halfTwistConfig n j (4 * q - 2)) := by
  symm
  apply Quotient.sound
  refine ⟨Equiv.swap (strandIdx i) (strandIdxSucc i), ?_⟩
  funext k
  change leftBraidFun n i j q k =
    halfTwistFun n j (4 * q - 2) ((Equiv.swap (strandIdx i) (strandIdxSucc i)) k)
  unfold leftBraidFun
  rw [if_neg hq1, if_pos hq2]

lemma configProj_leftBraid_final_word_v1 {n : ℕ} (i j : Fin (n - 1)) (q : ℝ)
    (hq1 : ¬ q ≤ 1 / 2) (hq2 : ¬ q ≤ 3 / 4) :
    configProj n (leftBraidConfig n i j q) =
      configProj n (halfTwistConfig n i (4 * q - 3)) := by
  symm
  apply Quotient.sound
  refine ⟨(Equiv.swap (strandIdx j) (strandIdxSucc j)) *
      (Equiv.swap (strandIdx i) (strandIdxSucc i)), ?_⟩
  funext k
  change leftBraidFun n i j q k =
    halfTwistFun n i (4 * q - 3)
      ((Equiv.swap (strandIdx j) (strandIdxSucc j))
        ((Equiv.swap (strandIdx i) (strandIdxSucc i)) k))
  unfold leftBraidFun
  rw [if_neg hq1, if_neg hq2]

lemma configProj_leftBraid_eq_word_v1 {n : ℕ} (i j : Fin (n - 1))
    (q : unitInterval) :
    configProj n (leftBraidConfig n i j (q : ℝ)) = leftBraidWordLoop n i j q := by
  unfold leftBraidWordLoop
  rw [Path.trans_apply]
  split_ifs with hq1
  · change configProj n (leftBraidConfig n i j (q : ℝ)) =
      configProj n (halfTwistConfig n i (2 * (q : ℝ)))
    exact configProj_leftBraid_first_word_v1 i j (q : ℝ) hq1
  · rw [Path.trans_apply]
    split_ifs with hq2
    · have hq2' : (q : ℝ) ≤ 3 / 4 := by linarith
      change configProj n (leftBraidConfig n i j (q : ℝ)) =
        configProj n (halfTwistConfig n j (2 * (2 * (q : ℝ) - 1)))
      convert configProj_leftBraid_middle_word_v1 i j (q : ℝ) hq1 hq2' using 1 <;> ring
    · have hq2' : ¬ (q : ℝ) ≤ 3 / 4 := by
        intro h
        apply hq2
        linarith
      change configProj n (leftBraidConfig n i j (q : ℝ)) =
        configProj n (halfTwistConfig n i (2 * (2 * (q : ℝ) - 1) - 1))
      convert configProj_leftBraid_final_word_v1 i j (q : ℝ) hq1 hq2' using 1 <;> ring

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (q : unitInterval),
      configProj n (leftBraidConfig n i j (q : ℝ)) = leftBraidWordLoop n i j q := by
  exact fun i j q => configProj_leftBraid_eq_word_v1 i j q
