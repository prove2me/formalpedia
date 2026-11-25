-- Prove2me | solution 1 for PI.Dv.TIW.finrank_le_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:53:02.251436+00:00
-- url     : https://prove2.me/submissions/efbe6bbc-0643-417f-8736-ab1a2671a3ed

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan
import Theorems.Thm_PI_Dv_TIW_span_orbit

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
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]
namespace PI.Dv.TIW
theorem _root_.solution (τ : Representation K G W) (hirr : Function.Surjective τ.asAlgebraHom)
    [Nontrivial W] : Module.finrank K W ≤ Fintype.card G := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  rw [← finrank_top, ← span_orbit τ hirr w hw]
  exact finrank_range_le_card _
end PI.Dv.TIW
