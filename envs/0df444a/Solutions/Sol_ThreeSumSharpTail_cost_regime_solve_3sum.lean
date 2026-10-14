-- Prove2me | solution 1 for ThreeSumSharpTail.cost_regime_solve_3sum
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T21:32:26.877322+00:00
-- url     : https://prove2.me/submissions/5a8578d3-cb3d-486b-9224-93424d75083f

import Definitions.Def_APSP299791_Defs5
import Theorems.Thm_ThreeSumSharpTail_rational_power_representation
import Theorems.Thm_ThreeSumSharpTail_full_d_parameter_host
import Theorems.Thm_ThreeSumSharpTail_full_d_explicit_time
import Theorems.Thm_ThreeSumSharpTail_full_d_uniformize
import Theorems.Thm_ThreeSumSharpTail_pruned_lop_detection
import Theorems.Thm_ThreeSumSharpTail_uniform_three_sum_transfer

theorem solution
    (G : Light.Sec4.RatParams) (a s r : ℚ)
    (ha0 : 0 < a) (ha1 : a < 1) (hs0 : 0 < s) (hsHalf : s < 1 / 2)
    (hcost : ∃ C : ℝ, 0 ≤ C ∧ ∀ N D : ℕ,
      1 ≤ D → (D : ℝ) ≤ (N : ℝ) ^ (a : ℝ) →
      Light.Sec4.CostsWithinP G C N D
        ((N : ℝ) ^ 2 * (Real.log D + 1) ^ 2 / (D : ℝ) ^ (s : ℝ))
        ((D : ℝ) ^ (1 / 2 - (s : ℝ)) * (Real.log D + 1)))
    (hprime : Real.log 7 / Real.log 2 + 3 * (a : ℝ) / 2 < 3 - (a : ℝ) * s / 2)
    (hbuild : 2 + (a : ℝ) * (1 + (s : ℝ) / 2) < 3 - (a : ℝ) * s / 2)
    (hr : 2 - a * s / 4 < r) :
    EndStatement.ThreeSum.SolvedInTime r := by
  have ha0R : 0 < (a : ℝ) := by exact_mod_cast ha0
  have ha1R : (a : ℝ) < 1 := by exact_mod_cast ha1
  have hs0R : 0 < (s : ℝ) := by exact_mod_cast hs0
  have hsHalfR : (s : ℝ) < 1 / 2 := by
    have h : (s : ℝ) < ((1 / 2 : ℚ) : ℝ) := Rat.cast_lt.mpr hsHalf
    norm_num at h
    exact h
  obtain ⟨A, B, c, e, hB, he, hab, hce, haRep, hsRep, _⟩ :=
    ThreeSumSharpTail.rational_power_representation a s ha0 ha1 hs0 hsHalf
  obtain ⟨h17, hD, hg⟩ := ThreeSumSharpTail.full_d_parameter_host A B c e hB he hab hce
  let D : ℕ → ℕ := ThreeSumApsp.paramDr A B
  let g : ℕ → ℕ := fun n => ThreeSumApsp.paramGr c e (D n)
  have hDf : ∀ n, D n = ⌊(n : ℝ) ^ (a : ℝ)⌋₊ := by
    intro n
    dsimp [D]
    rw [hD n, haRep]
  have hgf : ∀ n, 1 ≤ D n → g n = ⌈(D n : ℝ) ^ ((s : ℝ) / 2)⌉₊ := by
    intro n hn
    dsimp [g]
    rw [hg (D n) hn, hsRep]
  have hprime' : Real.logb 2 7 + 3 * (a : ℝ) / 2 ≤ 3 - (a : ℝ) * (s : ℝ) / 2 := by
    simpa only [Real.logb] using hprime.le
  have hbuild' : (a : ℝ) * (1 + (s : ℝ)) ≤ 1 := by nlinarith [hbuild]
  obtain ⟨n₀, hex⟩ := ThreeSumSharpTail.full_d_explicit_time Light.lightModel (a : ℝ) (s : ℝ) D g
    ha0R ha1R.le hs0R.le hsHalfR.le hDf hgf hprime' hbuild' h17
    (ThreeSumSharpTail.pruned_lop_detection G a s ha0 ha1 hs0 hsHalf hcost)
  have hδ0 : 0 ≤ (a : ℝ) * (s : ℝ) / 2 := by positivity
  have hδ1 : (a : ℝ) * (s : ℝ) / 2 ≤ 1 := by nlinarith
  have hu := ThreeSumSharpTail.full_d_uniformize _ 2 n₀ hδ0 hδ1 hex
  have hrR : 2 - (a : ℝ) * (s : ℝ) / 4 < (r : ℝ) := by exact_mod_cast hr
  have hr' : 2 - ((a : ℝ) * (s : ℝ) / 2) / 2 < (r : ℝ) := by linarith
  exact ThreeSumSharpTail.uniform_three_sum_transfer _ r 2 hδ1 hr' hu

#print axioms solution
