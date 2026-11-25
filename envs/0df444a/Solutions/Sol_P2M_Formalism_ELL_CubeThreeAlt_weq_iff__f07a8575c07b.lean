-- Prove2me | solution 1 for P2M_Formalism_ELL_CubeThreeAlt_weq_iff__f07a8575c07b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:37:09.828988+00:00
-- url     : https://prove2.me/submissions/ec27127b-5d4d-4268-bb8c-6903e2faad30

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.CubeThreeAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
variable {W : WeierstrassCurve K} {σ : Type}
namespace Formalism.ELL.CubeThreeAlt
theorem _root_.solution (W : WeierstrassCurve K) (s v : MvPowerSeries σ K) :
    WEqAt W s v ↔ GG W s v = 0 := by
  unfold Formalism.ELL.WEqAt GG Formalism.ELL.WeierstrassChordSeries.G
  simp only [MvPowerSeries.smul_eq_C_mul]
  constructor <;> intro h <;> linear_combination -h
end Formalism.ELL.CubeThreeAlt
