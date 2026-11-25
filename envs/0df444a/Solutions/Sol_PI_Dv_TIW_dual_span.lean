-- Prove2me | solution 1 for PI.Dv.TIW.dual_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:35:23.813674+00:00
-- url     : https://prove2.me/submissions/4ecf7fba-0e90-434b-a8f1-404af2d21e6f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
namespace PI.Dv.TIW
theorem _root_.solution {ι : Type} (ψ : ι → Module.Dual K V) (h : ∀ v, (∀ i, ψ i v = 0) → v = 0) :
    Submodule.span K (Set.range ψ) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := (Submodule.span K (Set.range ψ)).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)
  set v := (Module.evalEquiv K V).symm f with hvd
  have hv : ∀ φ : Module.Dual K V, f φ = φ v := by
    intro φ
    have : Module.evalEquiv K V v = f := by rw [hvd, LinearEquiv.apply_symm_apply]
    rw [← this]
    rfl
  have hv0 : v = 0 := h v (fun i => by rw [← hv]; exact hle (Submodule.subset_span ⟨i, rfl⟩))
  apply hf0
  ext φ
  rw [hv, hv0, map_zero]
  rfl
end PI.Dv.TIW
