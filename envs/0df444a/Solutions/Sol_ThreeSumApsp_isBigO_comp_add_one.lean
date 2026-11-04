-- Prove2me | solution 1 for ThreeSumApsp.isBigO_comp_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:23:05.707462+00:00
-- url     : https://prove2.me/submissions/4a685465-6fb1-42c8-bc56-e9cfa463c05c

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Theorems.Thm_ThreeSumApsp_Dominated_comp
import Theorems.Thm_ThreeSumApsp_Dominated_of_eventually_add_one
import Theorems.Thm_ThreeSumApsp_Dominated_isBigO

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
namespace ThreeSumApsp
theorem _root_.solution {G g : ℕ → ℝ} (hG : G =O[atTop] g) (hg : ∀ s, 0 ≤ g s)
    (size : ℕ → ℕ) : (fun n => G (size n)) =O[atTop] fun n => g (size n) + 1 := by
  obtain ⟨C, hC⟩ := hG.bound
  have hall : Dominated (fun _ => True) (fun s => |G s|) fun s => g s + 1 :=
    .of_eventually_add_one (C := C) (hC.mono fun s hs => by
      rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hg s)] at hs) hg
  exact Dominated.isBigO (n₀ := 0) (hall.comp size fun _ _ => trivial)
end ThreeSumApsp
