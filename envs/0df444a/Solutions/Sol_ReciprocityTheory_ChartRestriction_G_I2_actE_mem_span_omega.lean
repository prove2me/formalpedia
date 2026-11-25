-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.actE_mem_span_omega
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:22:58.553051+00:00
-- url     : https://prove2.me/submissions/095f8d1a-89c5-4c84-969c-24e5a349a028

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_zero_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_qsmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
variable {dim : (E →+* ℂ) → ℕ}
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {n : ℕ} (ω : Fin n → E) {β : E}
    (hβ : β ∈ Submodule.span ℚ (Set.range ω)) (x : Vsp dim) :
    actE β x ∈ Submodule.span ℝ (Set.range fun j => actE (ω j) x) := by
  induction hβ using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact Submodule.subset_span ⟨j, rfl⟩
  | zero => rw [actE_zero_left]; exact zero_mem _
  | add y z _ _ hy hz => rw [actE_add_left]; exact add_mem hy hz
  | smul q y _ hy => rw [actE_qsmul]; exact Submodule.smul_mem _ _ hy
end ReciprocityTheory.ChartRestriction.G.I2
