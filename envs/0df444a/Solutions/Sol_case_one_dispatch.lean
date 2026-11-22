-- Prove2me | solution 1 for case_one_dispatch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:51:34.851114+00:00
-- url     : https://prove2.me/submissions/ef25a628-fd82-4049-aa7f-c0b451f64fff

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
import Theorems.Thm_case_one_small_g
import Theorems.Thm_case_one_interval
import Theorems.Thm_case_one_residues
import Theorems.Thm_case_one_divisible

set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)
theorem _root_.solution (g : ℕ) (hm : m ≥ 289) (hg_ge : 2 ≤ g) (hg_le : g ≤ m / 2) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  -- (1a): small g
  by_cases hg4 : g ≤ 4
  · exact case_one_small_g m g hm (by grind)
  · push Not at hg4
    -- For g ≥ 5, let s be the smallest multiple of 3 such that g > ⌈m/s⌉.
    -- The paper shows: for m ≥ 289, either g < 2⌊m/s⌋ (subcase 1b) or
    -- s = 6 and 2⌊m/6⌋ ≤ g ≤ ⌈m/3⌉ (subcases 1c/1d).
    -- We split on whether g falls in the (1c)/(1d) range.
    by_cases hg_lb6 : 2 * (m / 6) ≤ g
    · by_cases hg_ub3 : g ≤ (m + 2) / 3
      · -- s = 6: subcases (1c) and (1d)
        by_cases h3 : m % 3 = 0
        · exact case_one_divisible m g hm (by grind)
        · exact case_one_residues m g hm h3 ⟨hg_lb6, hg_ub3⟩
      · -- g > ⌈m/3⌉: (1b) with s = 3
        push Not at hg_ub3
        exact case_one_interval m 3 g (by grind) ⟨1, rfl⟩ (by grind) (by grind : g < 2 * (m / 3))
    · -- g < 2⌊m/6⌋: (1b), find appropriate s
      push Not at hg_lb6
      -- s is the smallest multiple of 3 with g > ⌈m/s⌉.
      -- The condition g < 2⌊m/s⌋ follows from g ≤ ⌈m/(s-3)⌉.
      by_cases h6 : (m + 5) / 6 < g
      · -- s = 6 works: ⌈m/6⌉ < g and g < 2⌊m/6⌋
        exact case_one_interval m 6 g (by grind) ⟨2, rfl⟩ h6 hg_lb6
      · -- s ≥ 9: use s = 3⌈m/(3(g-1))⌉
        push Not at h6
        have h3g1 : 0 < 3 * (g - 1) := by grind
        set q := (m - 1) / (3 * (g - 1))
        have hq_lb : q * (3 * (g - 1)) ≤ m - 1 := Nat.div_mul_le_self _ _
        have hq2 : q ≥ 2 := by
          by_contra! hlt
          exact absurd ((Nat.div_lt_iff_lt_mul h3g1).mp hlt) (by grind)
        have hq_ub : m - 1 < 3 * (g - 1) * (q + 1) := Nat.lt_mul_div_succ _ h3g1
        have hm_lb : m ≥ q * (3 * (g - 1)) + 1 := by grind
        exact case_one_interval m (3 * (q + 1)) g (by grind) ⟨q + 1, rfl⟩ (by -- ⌈m/s⌉ < g
            rw [Nat.div_lt_iff_lt_mul (by grind)]
            have : g * (3 * (q + 1)) = (g - 1 + 1) * (3 * (q + 1)) := by grind
            grind)
          (by -- g < 2⌊m/s⌋
            suffices h : (g + 2) / 2 ≤ m / (3 * (q + 1)) by grind
            rw [Nat.le_div_iff_mul_le (by grind)]
            suffices (g + 2) * (3 * (q + 1)) ≤ 2 * m by
              have := Nat.div_mul_le_self (g + 2) 2; nlinarith
            by_cases hg10 : g ≥ 10
            · have : g ≥ 1 := by grind
              zify [this] at hm_lb ⊢; nlinarith
            · have : g = 5 ∨ g = 6 ∨ g = 7 ∨ g = 8 ∨ g = 9 := by grind
              grind)
