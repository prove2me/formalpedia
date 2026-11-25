-- Prove2me | solution 1 for PositivityTheory.CW.AdjointWordFiltration.mul_E_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:24:59.708629+00:00
-- url     : https://prove2.me/submissions/fd15eb20-824d-4067-969e-7bed5ca741cc

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CasimirPowerCommute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.AdjointWordFiltration
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace PositivityTheory.CW.AdjointWordFiltration
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) {j : ℕ} {w : Module.End ℂ V}
    (hw : w ∈ U E j) : w * E a b ∈ U E (j + 1) := by
  unfold U at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨l ++ [(a, b)], by simp; omega, ?_⟩
    simp [List.prod_append]
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx
end PositivityTheory.CW.AdjointWordFiltration
