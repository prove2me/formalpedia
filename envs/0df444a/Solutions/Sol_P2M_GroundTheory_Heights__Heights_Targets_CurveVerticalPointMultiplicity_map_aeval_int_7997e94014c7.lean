-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointMultiplicity_map_aeval_int_7997e94014c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:33:51.422987+00:00
-- url     : https://prove2.me/submissions/ff16beda-9db1-4e47-9c5d-c7017e4fb7c5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertPointNagata
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CurveCountObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointMultChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointMultChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointMultiplicity
variable {K : Type} {ι : K → Type}
namespace GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointMultiplicity
theorem _root_.solution {S T : Type*} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T] (φ : S →+* T) (r : (Σ k, ι k) → S)
    (f : MRing ι) : φ (aeval r f) = aeval (fun p => φ (r p)) f := by
  induction f using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]
end GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointMultiplicity
