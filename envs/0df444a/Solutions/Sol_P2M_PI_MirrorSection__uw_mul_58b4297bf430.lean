-- Prove2me | solution 1 for P2M_PI_MirrorSection__uw_mul_58b4297bf430
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:58:56.866569+00:00
-- url     : https://prove2.me/submissions/e1ad8f2c-137f-4588-9082-ed2fe11215c2

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
import Theorems.Thm_P2M_PI_MirrorSection__uh_mul_4992d70a4799

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.MirrorSection₂
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.MirrorSection₂
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {a b : B.Mat k r} (ha : a ∈ UWset k r z) (hb : b ∈ UWset k r z) :
    a * b ∈ UWset k r z := by
  refine ⟨uh_mul ha.1 hb.1, fun c => ⟨?_, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, (hb.2.1 c).1, (ha.2.1 c).1]
  · rw [← Matrix.mulVec_mulVec, (hb.2.1 c).2, (ha.2.1 c).2]
  · rw [← Matrix.mulVec_mulVec, hb.2.2, ha.2.2]
end PI.MirrorSection₂
