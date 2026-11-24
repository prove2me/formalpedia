-- Prove2me | solution 1 for PositivityTheory.KReal.filtX_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:47.290985+00:00
-- url     : https://prove2.me/submissions/cd4197f7-f809-4694-92c8-892333e94923

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
theorem _root_.solution (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) {m n : ℕ} (h : m ≤ n) :
    filtX X ι m ≤ filtX X ι n := by
  refine Submodule.span_mono ?_
  rintro _ ⟨l, v, hl, rfl⟩
  exact ⟨l, v, hl.trans h, rfl⟩
end PositivityTheory.KReal
