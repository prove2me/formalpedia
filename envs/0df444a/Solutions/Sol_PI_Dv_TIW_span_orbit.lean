-- Prove2me | solution 1 for PI.Dv.TIW.span_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:40:01.707309+00:00
-- url     : https://prove2.me/submissions/67adb727-1f90-4af6-bc80-e1958284ea30

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan
import Theorems.Thm_PI_Dv_TIW_asAlgebraHom_mem_span
import Theorems.Thm_PI_Dv_TIW_exists_end_map

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
theorem _root_.solution (τ : Representation K G W) (hirr : Function.Surjective τ.asAlgebraHom) (w : W) (hw : w ≠ 0) :
    Submodule.span K (Set.range fun x => τ x w) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  obtain ⟨M, hM⟩ := exists_end_map (K := K) w u hw
  obtain ⟨z, hz⟩ := hirr M
  have := asAlgebraHom_mem_span τ z w
  rwa [hz, hM] at this
end PI.Dv.TIW
