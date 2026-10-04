-- Prove2me | solution 2 for ZetaNine.irrational_zeta_nine
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-25T02:44:24.152809+00:00
-- url     : https://prove2.me/submissions/0da22fdd-858a-4f10-bc22-d779b7aefbf3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_ZetaNine_irrational_of_two_small_integer_forms
import Theorems.Thm_ZetaNine_exponentially_small_independent_forms_of_zeta_nine

open Filter
open scoped Topology

theorem solution : Irrational ((riemannZeta (9 : ℂ)).re) := by
  apply ZetaNine.irrational_of_two_small_integer_forms
  intro ε hε
  obtain ⟨c, hcpos, hc⟩ := ZetaNine.exponentially_small_independent_forms_of_zeta_nine
  have hlt1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have htend : Tendsto (fun n : ℕ => (Real.exp (-c)) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-c)).le hlt1
  have hev : ∀ᶠ n : ℕ in atTop, (Real.exp (-c)) ^ n < ε :=
    (tendsto_order.1 htend).2 ε hε
  obtain ⟨n, hnε, b₁, a₁, b₂, a₂, hind, hs₁, hs₂⟩ := (hev.and hc).exists
  have hexp : Real.exp (-(c * (n : ℝ))) = (Real.exp (-c)) ^ n := by
    rw [show -(c * (n : ℝ)) = (n : ℝ) * (-c) by ring, Real.exp_nat_mul]
  exact ⟨b₁, a₁, b₂, a₂, hind, (hs₁.trans_eq hexp).trans hnε,
    (hs₂.trans_eq hexp).trans hnε⟩
