-- Prove2me | solution 1 for TwoDegenerateGraphs.exists_entropy_exclusion_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/84d9fe85-3b9c-4f05-9117-5e09de927e8a

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_entropySlack_pos
import Theorems.Thm_TwoDegenerateGraphs_logTwo_pairLayer_card_add_one_le
import Theorems.Thm_TwoDegenerateGraphs_exists_empiricalEntropyError_base

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution :
    ∃ L₀ : ℕ, 4 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L →
        empiricalEntropyError L < entropySlack ∧
        (L : ℝ) +
            3 * logTwo ((L.choose 2 + 1 : ℕ) : ℝ) -
              entropySlack * (L.choose 2 : ℝ) < -1 := by
  obtain ⟨Lerror, _, herror⟩ := exists_empiricalEntropyError_base
  let C : ℝ := 1 + 6 / Real.log 2
  obtain ⟨N, hN⟩ :=
    exists_nat_gt (4 * (C + entropySlack + 1) / entropySlack)
  refine ⟨max 4 (max Lerror N), le_max_left _ _, ?_⟩
  intro L hL
  have hrest : max Lerror N ≤ L :=
    (le_max_right 4 (max Lerror N)).trans hL
  have herrorL : Lerror ≤ L := (le_max_left Lerror N).trans hrest
  have hNL : N ≤ L := (le_max_right Lerror N).trans hrest
  refine ⟨herror L herrorL, ?_⟩
  have hLfour : 4 ≤ L :=
    (le_max_left 4 (max Lerror N)).trans hL
  have hLreal : (4 : ℝ) ≤ L := by exact_mod_cast hLfour
  have hLpos : 0 < (L : ℝ) := by linarith
  have hNreal : (N : ℝ) ≤ L := by exact_mod_cast hNL
  have hthreshold :
      4 * (C + entropySlack + 1) / entropySlack < (L : ℝ) :=
    hN.trans_le hNreal
  have hbig :
      4 * (C + entropySlack + 1) < entropySlack * (L : ℝ) := by
    have h := (div_lt_iff₀ entropySlack_pos).mp hthreshold
    nlinarith
  have hscaled := mul_lt_mul_of_pos_right hbig hLpos
  have hlog := logTwo_pairLayer_card_add_one_le L (by omega)
  have hlinear :
      (L : ℝ) + 3 * logTwo ((L.choose 2 + 1 : ℕ) : ℝ) ≤
        C * (L : ℝ) := by
    calc
      (L : ℝ) + 3 * logTwo ((L.choose 2 + 1 : ℕ) : ℝ) ≤
          (L : ℝ) + 3 * (2 * (L : ℝ) / Real.log 2) := by
            gcongr
      _ = C * (L : ℝ) := by
        dsimp [C]
        ring
  have hchoose : (L.choose 2 : ℝ) =
      (L : ℝ) * ((L : ℝ) - 1) / 2 :=
    Nat.cast_choose_two ℝ L
  rw [hchoose]
  nlinarith [mul_pos entropySlack_pos hLpos]
end TwoDegenerateGraphs
