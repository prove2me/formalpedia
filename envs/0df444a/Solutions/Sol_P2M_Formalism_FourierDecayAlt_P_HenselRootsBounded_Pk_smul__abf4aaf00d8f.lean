-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_smul__abf4aaf00d8f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:13.374622+00:00
-- url     : https://prove2.me/submissions/ce595bba-55bd-4305-bd7d-77a857b1a573

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HenselRootsBounded
variable {K : Type} [CommRing K] {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.HenselRootsBounded
theorem _root_.solution {k : ℤ} {x r : K} (hr : r ∈ R) (hx : x ∈ Pk R ϖ k) : r * x ∈ Pk R ϖ k := by
  rw [mul_comm]; exact Pk_smul hx hr
end Formalism.FourierDecayAlt.P.HenselRootsBounded
