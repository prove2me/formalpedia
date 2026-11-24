-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_B4_op_eq_op__514f38137870
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:59:31.844136+00:00
-- url     : https://prove2.me/submissions/81318453-334f-4559-aa78-e23d00934618

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_hasDerivAt_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cast_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {f f' : Mat k r → E} {U : Set (Mat k r)} {X : Mat k r} (m : ℕ) (b : Bool)
    (hU : IsOpen U) (hf : ContDiffOn ℝ (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) f' U)
    (hff : ∀ h ∈ U, h ∈ GV k r → f h = f' h) (hX : inLie k r X) :
    ∀ g ∈ U, g ∈ GV k r → op b X f g = op' b X f' g := by
  intro g hg hgG
  have hd : DifferentiableAt ℝ f' g :=
    (hf.contDiffAt (hU.mem_nhds hg)).differentiableAt (cast_ne_zero m)
  exact (hasDerivAt_ext b hU hg hgG hd hff hX).deriv
end Formalism.FourierDecayAlt.P.B4
