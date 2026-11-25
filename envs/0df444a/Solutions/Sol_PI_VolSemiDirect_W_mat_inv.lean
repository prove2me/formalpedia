-- Prove2me | solution 1 for PI.VolSemiDirect.W.mat_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:57:59.219296+00:00
-- url     : https://prove2.me/submissions/a98df0a0-bb81-44e7-85a9-f5a7fc43966d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjHA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjCont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
namespace PI.VolSemiDirect.W
theorem _root_.solution (g : HA R σ J) : HA.mat R σ J g⁻¹ = (HA.mat R σ J g)⁻¹ := rfl
end PI.VolSemiDirect.W
