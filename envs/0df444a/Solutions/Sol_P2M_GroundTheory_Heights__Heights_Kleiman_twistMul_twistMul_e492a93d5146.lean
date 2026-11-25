-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_twistMul_twistMul_e492a93d5146
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:52:55.399721+00:00
-- url     : https://prove2.me/submissions/cbf89a66-6291-4ff5-be4d-d37f3e8b6a45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMul_sub_ecdec4e29c5d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_sub_mul_ed3d7223ab6a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_sub_pow_419ff662fef3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (M : SubSystem S x Ω) (q n : ℕ) (m a : ℤ) :
    twistMul (twistMul M q m) n a = twistMul M (n * q) (n * m + a) := by
  refine SubSystem.ext_sub fun I => ?_
  rw [twistMul_sub, twistMul_sub, twistMul_sub, mul_pow, twistSys_sub_pow, ← pow_mul,
    ← mul_assoc, twistSys_sub_mul, mul_comm q n, add_comm a]
end GroundTheory.Heights₂.Heights.Kleiman
