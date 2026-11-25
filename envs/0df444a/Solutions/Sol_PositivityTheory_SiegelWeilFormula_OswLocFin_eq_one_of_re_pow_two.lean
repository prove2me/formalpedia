-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.OswLocFin.eq_one_of_re_pow_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:25.441132+00:00
-- url     : https://prove2.me/submissions/e5c45b14-2039-4710-90dd-2f525bd73c6c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalInvariantNeighborhoods_SmallSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.OswLocFin
namespace PositivityTheory.SiegelWeilFormula.OswLocFin
theorem _root_.solution (w : ℂ) (hw : ‖w‖ = 1) (hre : ∀ k : ℕ, 1 / 2 < (w ^ (2 ^ k)).re) :
    w = 1 := by
  have hsq : ∀ u : ℂ, ‖u‖ = 1 → u.re ^ 2 + u.im ^ 2 = 1 := by
    intro u hu
    have h := Complex.normSq_eq_norm_sq u
    rw [hu, Complex.normSq_apply] at h
    nlinarith [h]
  have hnorm : ∀ k : ℕ, ‖w ^ (2 ^ k)‖ = 1 := fun k => by rw [norm_pow, hw, one_pow]
  have hstep : ∀ k : ℕ, (w ^ (2 ^ (k + 1))).re = 2 * (w ^ (2 ^ k)).re ^ 2 - 1 := by
    intro k
    have e : w ^ (2 ^ (k + 1)) = w ^ (2 ^ k) * w ^ (2 ^ k) := by rw [← pow_add]; congr 1; ring
    rw [e, Complex.mul_re]
    have := hsq _ (hnorm k)
    nlinarith [this]
  have hle : ∀ k : ℕ, (w ^ (2 ^ k)).re ≤ 1 := fun k => (Complex.re_le_norm _).trans (hnorm k).le
  have hd0 : 0 ≤ 1 - w.re := by have := hle 0; simp at this; linarith
  have hgrow : ∀ k : ℕ, ((k : ℝ) + 1) * (1 - w.re) ≤ 1 - (w ^ (2 ^ k)).re := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [hstep k]
      have h1 := hre k
      have h2 := hle k
      have h3 : 0 ≤ (1 - (w ^ (2 ^ k)).re) * (w ^ (2 ^ k)).re :=
        mul_nonneg (by linarith) (by linarith)
      push_cast
      nlinarith [ih, h1, h2, hd0, h3]
  have hd_eq : 1 - w.re = 0 := by
    by_contra hne
    have hpos : 0 < 1 - w.re := lt_of_le_of_ne hd0 (Ne.symm hne)
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / (1 - w.re))
    have h1 := hgrow k
    have h2 := hre k
    have h4 := hle k
    have : (1 : ℝ) < ((k : ℝ) + 1) * (1 - w.re) := by
      rw [div_lt_iff₀ hpos] at hk; nlinarith
    linarith
  have hre1 : w.re = 1 := by linarith
  have him : w.im = 0 := by have := hsq w hw; rw [hre1] at this; nlinarith
  exact Complex.ext (by simp [hre1]) (by simp [him])
end PositivityTheory.SiegelWeilFormula.OswLocFin
