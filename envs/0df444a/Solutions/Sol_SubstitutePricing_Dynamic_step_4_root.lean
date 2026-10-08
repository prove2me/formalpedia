-- Prove2me | solution 1 for SubstitutePricing.Dynamic.step_4_root
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:12:25.714379+00:00
-- url     : https://prove2.me/submissions/928fad7a-ab43-4eed-9df7-a320530956d0

import Definitions.Def_SubstitutePricing_Dynamic_Model
namespace SubstitutePricing.Dynamic
/-- Step 4: equation (21) has exactly one real solution, above the MNL scale. -/
theorem step_4_root (μ u0 σ : ℝ) (hμ : 0 < μ) (hσ : 0 < σ) :
    (∃! m : ℝ, (m / μ - 1) * Real.exp ((m + u0) / μ) = σ) ∧
    (∀ m : ℝ, (m / μ - 1) * Real.exp ((m + u0) / μ) = σ → μ < m) := by
  let F : ℝ → ℝ := fun m => (m / μ - 1) * Real.exp ((m + u0) / μ)
  have above (m : ℝ) (hm : F m = σ) : μ < m := by
    have hp : 0 < m / μ - 1 := (mul_pos_iff_of_pos_right (Real.exp_pos ((m + u0) / μ))).mp (by change 0 < F m; rw [hm]; exact hσ)
    have hh : 1 < m / μ := by linarith
    simpa using (lt_div_iff₀ hμ).mp hh
  have mono : StrictMonoOn F (Set.Ioi μ) := by
    intro a ha b hb hab
    have hd : a / μ < b / μ := (div_lt_div_iff_of_pos_right hμ).mpr hab
    have he : Real.exp ((a + u0) / μ) < Real.exp ((b + u0) / μ) :=
      Real.exp_lt_exp.mpr ((div_lt_div_iff_of_pos_right hμ).mpr (by linarith))
    have ha' : 0 ≤ b / μ - 1 := by
      have := (lt_div_iff₀ hμ).mpr (show 1 * μ < b by simpa using hb)
      linarith
    exact mul_lt_mul (by linarith : a / μ - 1 < b / μ - 1) he.le
      (Real.exp_pos _) ha'
  let e := Real.exp ((μ + u0) / μ)
  have he : 0 < e := Real.exp_pos _
  let b := μ * (1 + σ / e)
  have hb : μ ≤ b := by
    dsimp [b]
    nlinarith [div_pos hσ he]
  have hbdiv : b / μ - 1 = σ / e := by
    dsimp [b]
    field_simp
    ring
  have hFb : σ ≤ F b := by
    have he' : e ≤ Real.exp ((b + u0) / μ) := Real.exp_le_exp.mpr
      ((div_le_div_iff_of_pos_right hμ).mpr (by linarith))
    dsimp [F]
    rw [hbdiv]
    have hh := mul_le_mul_of_nonneg_left he' (div_pos hσ he).le
    simpa [ne_of_gt he] using hh
  have hc : Continuous F := by dsimp [F]; fun_prop
  have hFμ : F μ = 0 := by simp [F, ne_of_gt hμ]
  obtain ⟨m, hm, hroot⟩ := intermediate_value_Icc hb hc.continuousOn
    (show σ ∈ Set.Icc (F μ) (F b) by rw [hFμ]; exact ⟨hσ.le, hFb⟩)
  refine ⟨⟨m, hroot, ?_⟩, above⟩
  intro y hy
  exact mono.injOn (above y hy) (above m hroot) (hy.trans hroot.symm)

end SubstitutePricing.Dynamic

theorem solution (μ u0 σ : ℝ) (hμ : 0 < μ) (hσ : 0 < σ) :
    (∃! m : ℝ, (m / μ - 1) * Real.exp ((m + u0) / μ) = σ) ∧
    (∀ m : ℝ, (m / μ - 1) * Real.exp ((m + u0) / μ) = σ → μ < m)  := by
  exact SubstitutePricing.Dynamic.step_4_root μ u0 σ hμ hσ

#print axioms solution
