-- Prove2me | solution 1 for PlankProblem.exists_nat_near_grid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:47:32.977923+00:00
-- url     : https://prove2.me/submissions/555b7cee-b501-4028-afd4-66bc3ce4a0db

module
public import Definitions.Def_BallPlank_ShiftedPlanks
public import Definitions.Def_BallPlank_BallPlankFinal

set_option autoImplicit true
@[expose] public section
public section
open Set
open scoped BigOperators InnerProductSpace Pointwise
noncomputable section
open PlankProblem
variable {n : ℕ}
local notation "Rn" => EuclideanSpace ℝ (Fin n)
namespace PlankProblem
theorem _root_.solution {x α s : ℝ} {k : ℕ} (hk : 1 ≤ k) (hs : 0 ≤ s) (hα : α ≤ x)
    (hx : x ≤ α + k * s) : ∃ t : ℕ, t < k ∧ |x - (α + (t + 1 / 2) * s)| ≤ s / 2 := by
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨0, hk, ?_⟩
    have : x = α := le_antisymm (by simpa using hx) hα
    simp [this]
  · set q := (x - α) / s with hqdef
    have hq0 : 0 ≤ q := div_nonneg (by linarith) hpos.le
    have hxq : x - α = q * s := by rw [hqdef]; field_simp
    have hqk : q ≤ k := by rw [hqdef, div_le_iff₀ hpos]; linarith
    refine ⟨min ⌊q⌋₊ (k - 1), by omega, ?_⟩
    rw [abs_le]
    rcases le_total ⌊q⌋₊ (k - 1) with h | h
    · rw [min_eq_left h]
      have h1 := Nat.floor_le hq0
      have h2 := Nat.lt_floor_add_one q
      constructor <;> nlinarith
    · rw [min_eq_right h]
      have h1 : ((k - 1 : ℕ) : ℝ) ≤ q := le_trans (by exact_mod_cast h) (Nat.floor_le hq0)
      push_cast [Nat.cast_sub hk] at h1 ⊢
      constructor <;> nlinarith
end PlankProblem
