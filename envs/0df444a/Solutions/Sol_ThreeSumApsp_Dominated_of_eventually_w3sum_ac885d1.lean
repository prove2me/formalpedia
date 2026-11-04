-- Prove2me | solution 1 for ThreeSumApsp.Dominated.of_eventually_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:15:09.048333+00:00
-- url     : https://prove2.me/submissions/59adeac8-c8a4-4dbb-9abe-0e4167da7385

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Theorems.Thm_ThreeSumApsp_Dominated_trans

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
open ThreeSumApsp.Dominated
variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}
namespace ThreeSumApsp.Dominated
theorem _root_.solution {f g : ℕ → ℝ} {C : ℝ} (hfg : ∀ᶠ n in atTop, f n ≤ C * g n) {n₀ : ℕ}
    (hg : ∀ n, n₀ ≤ n → 0 < g n) : Dominated (fun n => n₀ ≤ n) f g := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hfg
  have hterm : ∀ m, 0 ≤ |f m| / |g m| := fun m => div_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsum : 0 ≤ ∑ m ∈ Finset.range N, |f m| / |g m| := Finset.sum_nonneg fun m _ => hterm m
  refine ⟨|C| + ∑ m ∈ Finset.range N, |f m| / |g m|, add_nonneg (abs_nonneg C) hsum, fun n hn => ?_⟩
  have hgn : 0 < g n := hg n hn
  rw [add_mul]
  obtain hlt | hge := lt_or_ge n N
  · calc f n ≤ |f n| / |g n| * g n := by
          rw [abs_of_pos hgn, div_mul_cancel₀ _ hgn.ne']
          exact le_abs_self _
      _ ≤ (∑ m ∈ Finset.range N, |f m| / |g m|) * g n :=
          mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun m => |f m| / |g m|)
            (fun m _ => hterm m) (Finset.mem_range.2 hlt)) hgn.le
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg (abs_nonneg C) hgn.le)
  · exact ((hN n hge).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hgn.le)).trans
      (le_add_of_nonneg_right (mul_nonneg hsum hgn.le))
end ThreeSumApsp.Dominated
