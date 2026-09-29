-- Prove2me | solution 1 for UndecidableSpectralGap.usg_gs_energy_with_promise
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T10:30:19.635159+00:00
-- url     : https://prove2.me/submissions/d617e4d3-ad9d-40e4-928d-c0a9086ad76e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_UndecidableSpectralGap_usg_diverging_gs_energy

set_option autoImplicit false
open scoped ComplexOrder

open UndecidableSpectralGap

namespace UndecidableSpectralGapSolution

/-- If `0 < δ₂`, `0 < δ₁`, `1 ≤ L` and `(δ₁ + 1)/δ₂ ≤ L`, then `1 ≤ L² δ₂ - L δ₁`. -/
theorem quad_lower_bound {δ₁ δ₂ L : ℝ} (h₂ : 0 < δ₂) (hL1 : 1 ≤ L)
    (hL : (δ₁ + 1) / δ₂ ≤ L) : 1 ≤ L ^ 2 * δ₂ - L * δ₁ := by
  have hstep : δ₁ + 1 ≤ L * δ₂ := by
    have := (div_le_iff₀ h₂).mp hL
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hstep (le_trans zero_le_one hL1)]

end UndecidableSpectralGapSolution

open UndecidableSpectralGapSolution

theorem solution (u : Nat.Partrec.Code) :
    ∃ (d : ℕ) (h1 : ℕ → Matrix (Fin d) (Fin d) ℂ)
      (hrow hcol : ℕ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (Lbound : ℕ → ℕ),
      (∀ n : ℕ,
        (h1 n).IsHermitian ∧ (hrow n).IsHermitian ∧ (hcol n).IsHermitian ∧
        opNorm (h1 n) ≤ 1 / 2 ∧ opNorm (hrow n) ≤ 1 / 2 ∧ opNorm (hcol n) ≤ 1 / 2 ∧
        (∀ i j, IsAlgebraic ℚ ((h1 n) i j)) ∧
        (∀ i j, IsAlgebraic ℚ ((hrow n) i j)) ∧
        (∀ i j, IsAlgebraic ℚ ((hcol n) i j))) ∧
      ∀ n : ℕ,
        (¬ (u.eval n).Dom → ∀ L : ℕ, 0 < L →
          gsEnergy (latticeHam L d (h1 n) (hrow n) (hcol n)) ≤ 0) ∧
        ((u.eval n).Dom → ∀ L ≥ Lbound n,
          1 ≤ gsEnergy (latticeHam L d (h1 n) (hrow n) (hcol n))) := by
  classical
  obtain ⟨d, h1, hrow, hcol, δ₁, δ₂, hprop, hmain⟩ :=
    usg_diverging_gs_energy u 1 (by norm_num)
  refine ⟨d, h1, hrow, hcol,
    fun n => if h : (u.eval n).Dom then
        max ((hmain n).2 h).choose (max 1 ⌈(δ₁ n + 1) / δ₂ n⌉₊) else 0,
    fun n => ?_, fun n => ⟨?_, ?_⟩⟩
  · obtain ⟨a, b, c, e, f, g, i, j, k, -, -⟩ := hprop n
    exact ⟨a, b, c, e, f, g, i, j, k⟩
  · -- non-halting: the energy is at most `-L/2 ≤ 0`
    intro hnd L hL
    have := (hmain n).1 hnd L hL
    have hL' : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    push_cast at this
    linarith
  · -- halting: beyond the threshold the quadratic lower bound exceeds `1`
    intro hd L hL
    simp only [ge_iff_le, dif_pos hd] at hL
    have hL0 : ((hmain n).2 hd).choose ≤ L := le_trans (le_max_left _ _) hL
    have hrest : max 1 ⌈(δ₁ n + 1) / δ₂ n⌉₊ ≤ L := le_trans (le_max_right _ _) hL
    have hone : (1 : ℕ) ≤ L := le_trans (le_max_left _ _) hrest
    have hceil : ⌈(δ₁ n + 1) / δ₂ n⌉₊ ≤ L := le_trans (le_max_right _ _) hrest
    have hbound := ((hmain n).2 hd).choose_spec L hL0
    have hδ₂ : 0 < δ₂ n := (hprop n).2.2.2.2.2.2.2.2.2.2
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hone
    have hLdiv : (δ₁ n + 1) / δ₂ n ≤ (L : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hceil)
    exact le_trans (quad_lower_bound hδ₂ hL1 hLdiv) hbound
