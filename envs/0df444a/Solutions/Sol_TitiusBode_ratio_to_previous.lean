-- Prove2me | solution 1 for TitiusBode.ratio_to_previous
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T19:32:33.377978+00:00
-- url     : https://prove2.me/submissions/0094961e-0c26-4d10-ac54-a6d41c9f41df

import Definitions.Def_TitiusBode_Defs
import Mathlib
open Filter Topology
open TitiusBode

theorem solution :
    tbAU ((0 : ℕ) : WithBot ℕ) < 2 * tbAU ⊥ ∧
    (∀ n : ℕ, tbCanonical (n + 1) < 2 * tbCanonical n) ∧
    Tendsto (fun n : ℕ => tbCanonical (n + 1) / tbCanonical n) atTop (𝓝 2) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [tbAU, twoPowExt]
  · intro n
    simp only [tbCanonical, pow_succ]
    nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) n]
  · have hform : ∀ n : ℕ, tbCanonical (n + 1) / tbCanonical n
        = 2 - 0.4 / tbCanonical n := by
      intro n
      have hp : 0 < tbCanonical n := by unfold tbCanonical; positivity
      field_simp
      simp only [tbCanonical, pow_succ]
      ring
    simp_rw [hform]
    have htop : Tendsto tbCanonical atTop atTop := by
      unfold tbCanonical
      apply tendsto_atTop_add_const_left
      apply Tendsto.const_mul_atTop (by norm_num)
      exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have h0 : Tendsto (fun n => (0.4 : ℝ) / tbCanonical n) atTop (𝓝 0) :=
      htop.const_div_atTop _
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).sub h0
