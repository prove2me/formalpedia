-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSumApsp.Dominated.of_eventually
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:12:28.544154+00:00
-- url     : https://prove2.me/submissions/e2c83f88-6a88-4315-bc7d-1e32a1454e6b

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Lean
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Asymptotics
end Asymptotics
namespace Filter
end Filter
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSum1960614.Machine.ThreeSumApsp.Dominated
end ThreeSum1960614.Machine.ThreeSumApsp.Dominated
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Dominated
end ThreeSumApsp.Dominated

section
open _root_.Filter
open _root_.Asymptotics
open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp

open _root_.ThreeSum1960614.Machine.ThreeSumApsp.Dominated

variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}
section

/-- A bound that holds from some unknown point on. If `g` is positive from `n₀` on, the finitely
many values in between cost only a larger constant. -/
theorem ThreeSum1960614.Machine.ThreeSumApsp.Dominated.of_eventually__implementation_b160db49ab {f g : ℕ → ℝ} {C : ℝ} (hfg : ∀ᶠ n in atTop, f n ≤ C * g n) {n₀ : ℕ}
    (hg : ∀ n, n₀ ≤ n → 0 < g n) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.Dominated (fun n => n₀ ≤ n) f g := by
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
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSumApsp.Dominated.of_eventually__implementation_b160db49ab) := (@ThreeSum1960614.Machine.ThreeSumApsp.Dominated.of_eventually__implementation_b160db49ab)

#print axioms solution
