-- Prove2me | solution 1 for PositivityTheory.KReal.filtX_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:48.885828+00:00
-- url     : https://prove2.me/submissions/b77d314d-bb7d-490b-b236-467bb155a759

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasB
import Theorems.Thm_PositivityTheory_KReal_wordX_cons

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
theorem _root_.solution (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) (i : I) :
    ∀ x ∈ filtX X ι n, X i x ∈ filtX X ι (n + 1) := by
  have : filtX X ι n ≤ (filtX X ι (n + 1)).comap (X i) := by
    rw [filtX, Submodule.span_le]
    rintro _ ⟨l, v, hl, rfl⟩
    exact Submodule.subset_span ⟨i :: l, v, by simpa using hl, (wordX_cons X i l _).symm⟩
  exact fun x hx => this hx
end PositivityTheory.KReal
