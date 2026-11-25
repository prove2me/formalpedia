-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_ampleChart_pow_ff3b4f7f14e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:21:35.843268+00:00
-- url     : https://prove2.me/submissions/e77cde5c-d3b3-4375-a15e-115859ac9ad9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleTwistGenerated
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ampleChart_mul_65e82fd4e0bb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_ampleChart_of_mem_chartRing_4fd891325c2e

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
open scoped Pointwise
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {H : SubSystem k x Ω} {m : ℕ} {hh : Ω} {I : Chart x} {z : Ω}
    (hz : z ∈ ampleChart H m hh I) (n : ℕ) : z ^ n ∈ ampleChart H m hh I := by
  induction n with
  | zero => rw [pow_zero]; exact mem_ampleChart_of_mem_chartRing (one_mem _)
  | succ n ih => rw [pow_succ]; exact ampleChart_mul ih hz
end GroundTheory.Heights₂.Heights.Kleiman
