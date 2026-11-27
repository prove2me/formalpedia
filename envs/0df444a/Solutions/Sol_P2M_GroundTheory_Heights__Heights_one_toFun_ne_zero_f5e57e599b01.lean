-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_one_toFun_ne_zero_f5e57e599b01
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:12:21.966992+00:00
-- url     : https://prove2.me/submissions/a4fb0344-576e-414e-b62b-dcb0501e7d88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (P : ArithVariety n) : (IntegralSection.one P).toFun ≠ 0 := by
  change P.mkF 1 / P.mkF 1 ≠ 0
  rw [map_one, div_one]
  exact one_ne_zero
end GroundTheory.Heights₂.Heights
