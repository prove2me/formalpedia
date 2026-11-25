-- Prove2me | solution 1 for Subadditive.tendsto_div_atBot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:26:50.795818+00:00
-- url     : https://prove2.me/submissions/a569737f-5ad1-42ba-8b71-cc3641a08d7d

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_Fekete_Superadditive

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
namespace Subadditive
theorem _root_.solution {u : ℕ → ℝ} (h : Subadditive u)
    (hbdd : ¬ BddBelow (range fun n ↦ u n / n)) :
    Tendsto (fun n ↦ u n / n) atTop atBot := by
  refine tendsto_atBot.2 fun b ↦ ?_
  set a := min b 0 - 1
  have ha : a < 0 := by linarith [min_le_right b 0]
  -- truncating `u` at the line `a * n` keeps it subadditive and bounds `u n / n` below
  set w : ℕ → ℝ := fun n ↦ max (u n) (a * n)
  have hw : Subadditive w := fun m n ↦ by
    simp only [w, Nat.cast_add, mul_add]
    exact (max_le_max (h m n) le_rfl).trans max_add_add_le_max_add_max
  have hdiv : ∀ n : ℕ, n ≠ 0 → w n / n = max (u n / n) a := fun n hn ↦ by
    have hn' : (0 : ℝ) < n := by positivity
    rw [← mul_div_cancel_right₀ a hn'.ne', max_div_div_right hn'.le]
  have hbddw : BddBelow (range fun n ↦ w n / n) := ⟨a, by
    rintro _ ⟨n, rfl⟩
    rcases eq_or_ne n 0 with rfl | hn
    · simp [ha.le]
    · exact (le_max_right _ _).trans_eq (hdiv n hn).symm⟩
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := not_bddBelow_iff.1 hbdd a
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; linarith
  have hlim : hw.lim ≤ a := by
    simpa [hdiv k hk0, max_eq_right hk.le] using hw.lim_le_div hbddw hk0
  filter_upwards [(hw.tendsto_lim hbddw).eventually (gt_mem_nhds (show hw.lim < a + 1 by linarith))]
    with n hn
  calc u n / n ≤ w n / n := div_le_div_of_nonneg_right (le_max_left _ _) n.cast_nonneg
    _ ≤ b := by linarith [min_le_left b 0]
end Subadditive
