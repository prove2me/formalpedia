-- Prove2me | solution 1 for ThreeSumApsp.Dominated.of_le_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:59:22.447805+00:00
-- url     : https://prove2.me/submissions/53267157-0ca5-4cdf-abfc-e2a6380e31f3

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
open ThreeSumApsp.Dominated
variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}
namespace ThreeSumApsp.Dominated
theorem _root_.solution {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ x, dom x → f x ≤ C * g x) :
    Dominated dom f g :=
  ⟨C, hC, hfg⟩
end ThreeSumApsp.Dominated
