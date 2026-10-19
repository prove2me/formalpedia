-- Prove2me | solution 1 for SoficGroups.exists_positive_antitone_slow_overlap_scales
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/1b0ec23c-83ef-473e-a2e9-8d1be8c8439f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_exists_positive_antitone_slow_vanishing_threshold

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    (e : ℕ → ℝ) (he_nonneg : ∀ n, 0 ≤ e n)
    (he : Tendsto e atTop (nhds 0)) :
    ∃ eta H : ℕ → ℝ,
      (∀ n, 0 < eta n) ∧ Antitone eta ∧
      Tendsto eta atTop (nhds 0) ∧
      (∀ n, 0 < H n) ∧ Antitone H ∧
      Tendsto H atTop (nhds 0) ∧
      Tendsto (fun n => e n / eta n) atTop (nhds 0) ∧
      Tendsto (fun n => eta n / H n) atTop (nhds 0) := by
  obtain ⟨eta, heta_pos, heta_antitone, heta_zero, herror_zero⟩ :=
    exists_positive_antitone_slow_vanishing_threshold e he_nonneg he
  let H : ℕ → ℝ := fun n => Real.sqrt (eta n)
  have hH_pos (n : ℕ) : 0 < H n := by
    exact Real.sqrt_pos.2 (heta_pos n)
  have hH_antitone : Antitone H := by
    intro a b hab
    exact Real.sqrt_le_sqrt (heta_antitone hab)
  have hH_zero : Tendsto H atTop (nhds 0) := by
    simpa only [H, Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp heta_zero
  have hquot (n : ℕ) : eta n / H n = H n := by
    dsimp [H]
    apply (div_eq_iff (Real.sqrt_pos.2 (heta_pos n)).ne').2
    nlinarith [Real.sq_sqrt (heta_pos n).le]
  have hquot_zero : Tendsto (fun n => eta n / H n) atTop (nhds 0) := by
    have hfun : (fun n => eta n / H n) = H := funext hquot
    rw [hfun]
    exact hH_zero
  exact ⟨eta, H, heta_pos, heta_antitone, heta_zero,
    hH_pos, hH_antitone, hH_zero, herror_zero, hquot_zero⟩
end SoficGroups
