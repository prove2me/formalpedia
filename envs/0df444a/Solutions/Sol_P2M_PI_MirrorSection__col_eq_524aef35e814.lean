-- Prove2me | solution 1 for P2M_PI_MirrorSection__col_eq_524aef35e814
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:00:56.234902+00:00
-- url     : https://prove2.me/submissions/6b3ced48-4acf-4f46-aa97-c8daef6c1d39

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI

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
theorem _root_.solution (g : B.Mat k r) (j : Fin (2 * r + k + 1)) : g *ᵥ bvec j = fun i => g i j := by
  funext i
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
end PI.MirrorSection₂
