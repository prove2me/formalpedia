-- Prove2me | solution 1 for PositivityTheory.KReal.filtX_fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:26:59.54004+00:00
-- url     : https://prove2.me/submissions/89b6e57e-0c8b-4409-b7b2-e69472065f37

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasB
import Theorems.Thm_PositivityTheory_KReal_wordX_cons
import Theorems.Thm_PositivityTheory_KReal_filtX_zero

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
theorem _root_.solution [Fintype I] [FiniteDimensional ℂ V] (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) :
    FiniteDimensional ℂ (filtX X ι n) := by
  induction n with
  | zero => rw [filtX_zero]; infer_instance
  | succ n ih =>
    classical
    have hle : filtX X ι (n + 1) ≤ filtX X ι n ⊔ ⨆ i, (filtX X ι n).map (X i) := by
      rw [filtX, Submodule.span_le]
      rintro _ ⟨l, v, hl, rfl⟩
      cases l with
      | nil => exact Submodule.mem_sup_left (Submodule.subset_span ⟨[], v, Nat.zero_le _, rfl⟩)
      | cons a l =>
        refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem a ?_)
        exact ⟨wordX X l (ι v), Submodule.subset_span ⟨l, v, by simpa using hl, rfl⟩, (wordX_cons X a l _).symm⟩
    exact Submodule.finiteDimensional_of_le hle
end PositivityTheory.KReal
