-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_redAt_isUnit_of_isUnit_e99246644bde
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:46:46.0538+00:00
-- url     : https://prove2.me/submissions/2a72e138-284c-4a0b-ad68-c47cded680a7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LineBundleRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLineBundleRestrict
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_chartRing_sub_locAt_a84ca9ba7312
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_mul_614d2e1fada9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_one_d19ae30e21d8


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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
include hsp
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {I J : Chart y} (h : I.1 ⊆ J.1)
    (a : chartRing k x (liftChart hxy I))
    (ha : IsUnit (chartIncl (S := k) (x := x) (I := liftChart hxy I) (J := liftChart hxy J) h a)) :
    (a : Ω) ∈ locAt k x y ∧ ∃ b ∈ chartRing k y J, redAt k x y a * b = 1 := by
  obtain ⟨c, hc⟩ := ha.exists_right_inv
  have hc' : (a : Ω) * (c : Ω) = 1 := congrArg Subtype.val hc
  have haL := chartRing_sub_locAt hsp hxy I a.2
  have hcL := chartRing_sub_locAt hsp hxy J c.2
  refine ⟨haL.1, _, hcL.2, ?_⟩
  rw [← (locAt_mul hsp haL.1 hcL.1).2, hc', (locAt_one hsp).2]
end GroundTheory.Heights₂.Heights.Kleiman
