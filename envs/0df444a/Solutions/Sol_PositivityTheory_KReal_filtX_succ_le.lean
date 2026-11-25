-- Prove2me | solution 1 for PositivityTheory.KReal.filtX_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:28:13.579903+00:00
-- url     : https://prove2.me/submissions/aa66b9e6-7186-45b3-a582-b9bc7b07edfd

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
theorem _root_.solution (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) :
    filtX X ι (n + 1) ≤ filtX X ι n ⊔
      Submodule.span ℂ {y | ∃ (w : Fin (n + 1) → I) (v : V), y = wordX X (List.ofFn w) (ι v)} := by
  conv_lhs => rw [filtX]
  rw [Submodule.span_le]
  rintro _ ⟨l, v, hl, rfl⟩
  by_cases h : l.length ≤ n
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨l, v, h, rfl⟩)
  · have h' : l.length = n + 1 := by omega
    refine Submodule.mem_sup_right (Submodule.subset_span ⟨fun i => l.get (i.cast h'.symm), v, ?_⟩)
    congr 2
    apply List.ext_getElem
    · simp [h']
    · intro m h1 h2
      rw [List.getElem_ofFn]
      simp
end PositivityTheory.KReal
