-- Prove2me | solution 1 for PI.Dv.TIW.exists_end_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:35:48.000894+00:00
-- url     : https://prove2.me/submissions/d417cce5-2776-44d3-ad87-7eb13ff398dd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan
import Theorems.Thm_PI_Dv_TIW_exists_dual_one

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
theorem _root_.solution (w u : W) (hw : w ≠ 0) : ∃ M : Module.End K W, M w = u := by
  obtain ⟨φ, hφ⟩ := exists_dual_one (K := K) w hw
  exact ⟨φ.smulRight u, by rw [LinearMap.smulRight_apply, hφ, one_smul]⟩
end PI.Dv.TIW
