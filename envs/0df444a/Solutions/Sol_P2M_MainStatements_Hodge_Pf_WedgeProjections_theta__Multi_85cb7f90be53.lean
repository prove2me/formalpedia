-- Prove2me | solution 1 for P2M_MainStatements_Hodge_Pf_WedgeProjections_theta__Multi_85cb7f90be53
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:22.495453+00:00
-- url     : https://prove2.me/submissions/0fc2895f-880d-475d-b409-2703d5a55c82

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianWedgeProducts_ThetaMulti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MainStatements MainStatements.Hodge MainStatements.Hodge.Pf MainStatements.Hodge.Pf.WedgeProjections
variable {K : Type} [Field K] {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  (p q : V →ₗ[K] W) (r₁ r₂ : W →ₗ[K] V)
namespace MainStatements.Hodge.Pf.WedgeProjections
theorem _root_.solution (g : Fin 2 → Module.Dual K V) (v : Fin 2 → W) :
    theta r₁ r₂ g (exteriorPower.ιMulti K 2 v) =
      g 0 (r₁ (v 0)) * g 1 (r₂ (v 1)) - g 1 (r₂ (v 0)) * g 0 (r₁ (v 1)) := by
  simp [theta, Matrix.det_fin_two]
end MainStatements.Hodge.Pf.WedgeProjections
