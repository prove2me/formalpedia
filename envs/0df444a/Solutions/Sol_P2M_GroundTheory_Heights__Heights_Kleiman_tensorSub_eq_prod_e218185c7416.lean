-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_tensorSub_eq_prod_e218185c7416
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:36:47.855908+00:00
-- url     : https://prove2.me/submissions/0e8bc945-e1f7-4371-8f1e-f010bde5111b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumAdditive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumEventual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterSumTopVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_InterSumEventuallyEqInterNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumAdditive
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_foldl_twist_eq_mul_3a1641a715cf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_prod_map_filter_043c3da86e4d

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
open MvPolynomial Filter
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
attribute [local instance] twistMonoid
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {n : ℕ} (L : Fin n → SubSystem S x Ω) (T : Finset (Fin n)) :
    tensorSub L T = ∏ j ∈ T, L j := by
  unfold tensorSub
  rw [foldl_twist_eq_mul]
  change 1 * _ = _
  rw [one_mul, prod_map_filter, ← Fin.prod_univ_def, ← Finset.prod_filter]
  congr 1
  ext j
  simp
end GroundTheory.Heights₂.Heights.Kleiman
