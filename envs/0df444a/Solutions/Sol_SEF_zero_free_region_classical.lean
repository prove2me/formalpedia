-- Prove2me | solution 1 for SEF.zero_free_region_classical
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-20T23:56:15.752639+00:00
-- url     : https://prove2.me/submissions/d72f137a-3187-4fe0-acda-24cddf4d343a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlpoGeChallenge_LFunction_eq_zero_re_of_isPrimitive
import Theorems.Thm_GRH_grh_critical_line_iff

namespace HubZ

/-- `ζ(s) ≠ 0` for `Re s > 1/2`, from the hub (critical line for primitive characters) and the proved equivalence. -/
theorem zeta_ne_zero_of_half_lt {s : ℂ} (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
  rcases le_or_gt 1 s.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · have hs1 : s ≠ 1 := fun h => by simp [h] at h1
    have h := GRH.grh_critical_line_iff.mp AlpoGeChallenge.LFunction_eq_zero_re_of_isPrimitive
      1 (1 : DirichletCharacter ℂ 1) s (by exact_mod_cast hs) (fun h => hs1 h.2)
    rwa [DirichletCharacter.LFunction_modOne_eq] at h

end HubZ

theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ σ t : ℝ, 1 - c / Real.log (|t| + 2) ≤ σ → riemannZeta ⟨σ, t⟩ ≠ 0 := by
  refine ⟨1 / 8, by norm_num, fun σ t h => HubZ.zeta_ne_zero_of_half_lt ?_⟩
  have hL : 1 / 2 < Real.log (|t| + 2) := by
    have h2 : Real.log 2 ≤ Real.log (|t| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
    linarith [Real.log_two_gt_d9]
  have hq : 1 / 8 / Real.log (|t| + 2) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  show 1 / 2 < σ
  linarith
