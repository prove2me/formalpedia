-- Prove2me | solution 1 for SEF.zero_free_region_vinogradov_korobov
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-20T23:56:17.400169+00:00
-- url     : https://prove2.me/submissions/b0a7d0d2-b31b-404f-9de6-aa0b868e44ed
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
      ∀ σ t : ℝ, 3 ≤ |t| →
        1 - c / ((Real.log |t|) ^ (2 / 3 : ℝ) * (Real.log (Real.log |t|)) ^ (1 / 3 : ℝ)) ≤ σ →
          riemannZeta ⟨σ, t⟩ ≠ 0 := by
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hll3 : 0 < Real.log (Real.log 3) := Real.log_pos hlog3
  set a := (Real.log (Real.log 3)) ^ (1 / 3 : ℝ) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hll3 _
  refine ⟨a / 4, by positivity, fun σ t ht h => HubZ.zeta_ne_zero_of_half_lt ?_⟩
  have hL : Real.log 3 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht
  have hL1 : 1 ≤ (Real.log |t|) ^ (2 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hLL : Real.log (Real.log 3) ≤ Real.log (Real.log |t|) := Real.log_le_log (by linarith) hL
  have hA : a ≤ (Real.log (Real.log |t|)) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow hll3.le hLL (by norm_num)
  have hD : a ≤ (Real.log |t|) ^ (2 / 3 : ℝ) * (Real.log (Real.log |t|)) ^ (1 / 3 : ℝ) := by
    nlinarith
  have hq : a / 4 / ((Real.log |t|) ^ (2 / 3 : ℝ) * (Real.log (Real.log |t|)) ^ (1 / 3 : ℝ)) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  show 1 / 2 < σ
  linarith
