-- Prove2me | solution 1 for PositivityTheory.ThKG.CayleyTransformDarboux.low_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:29:58.906273+00:00
-- url     : https://prove2.me/submissions/b5e30f2a-20cf-4903-b578-62c6756ccb9c

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ToralCohomology_ShiftLow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action PositivityTheory.KReal
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.CayleyTransformDarboux
variable {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.ThKG.CayleyTransformDarboux
theorem _root_.solution {M' : Type} [AddCommGroup M'] [Module ℂ M'] {T : Module.End ℂ M} {T' : Module.End ℂ M'} {lam : ℂ}
    (φ : M →ₗ[ℂ] M') (hφ : ∀ x, φ (T x) = T' (φ x)) {x : M} (hx : x ∈ low T lam) : φ x ∈ low T' lam := by
  refine (iSup_le fun t y hy => ?_ : low T lam ≤ (low T' lam).comap φ) hx
  refine Submodule.mem_iSup_of_mem t ?_
  rw [Module.End.mem_eigenspace_iff] at hy ⊢
  rw [← hφ, hy, map_smul]
end PositivityTheory.ThKG.CayleyTransformDarboux
