-- Prove2me | solution 1 for PositivityTheory.KReal.filtX_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:47.368971+00:00
-- url     : https://prove2.me/submissions/3ee3dcc8-4774-4a55-93f0-dd8bfb9f0cea

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {K I : Type} {M : Type} [AddCommGroup M] [Module ℂ M] {V : Type} [AddCommGroup V] [Module ℂ V]
namespace PositivityTheory.KReal
theorem _root_.solution (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) : filtX X ι 0 = LinearMap.range ι := by
  apply le_antisymm
  · rw [filtX, Submodule.span_le]
    rintro _ ⟨l, v, hl, rfl⟩
    have : l = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)
    subst this
    exact ⟨v, by simp [wordX]⟩
  · rintro _ ⟨v, rfl⟩
    exact Submodule.subset_span ⟨[], v, le_rfl, by simp [wordX]⟩
end PositivityTheory.KReal
