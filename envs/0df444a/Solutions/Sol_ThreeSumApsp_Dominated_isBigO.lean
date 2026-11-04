-- Prove2me | solution 1 for ThreeSumApsp.Dominated.isBigO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:15:10.22878+00:00
-- url     : https://prove2.me/submissions/74252130-c63e-4fb7-9206-7806bd5fb22a

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
theorem _root_.solution {f g : ℕ → ℝ} {n₀ : ℕ} (hfg : Dominated (fun n => n₀ ≤ n) (fun n => |f n|) g) :
    f =O[atTop] g := by
  obtain ⟨C, hC, hle⟩ := hfg
  refine IsBigO.of_bound C (eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact (hle n hn).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC)
end ThreeSumApsp.Dominated
