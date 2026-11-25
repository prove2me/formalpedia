-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locAt_div_084462a2e36e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:33:13.064601+00:00
-- url     : https://prove2.me/submissions/207e2b7c-0f5b-46fb-ac1c-ba05c1203d57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_mul_614d2e1fada9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_inv_eb034c1f50b6

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
variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} (x : Fin (N + 1) → Ω) (y : Fin (N + 1) → K')
variable {k x y}
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
include hsp
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {a b : Ω} (ha : a ∈ locAt k x y) (hb : b ∈ locAt k x y) (hr : redAt k x y b ≠ 0) :
    a / b ∈ locAt k x y ∧ redAt k x y (a / b) = redAt k x y a / redAt k x y b := by
  obtain ⟨-, h1, h2⟩ := locAt_inv hsp hb hr
  obtain ⟨h3, h4⟩ := locAt_mul hsp ha h1
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact ⟨h3, by rw [h4, h2]⟩
end GroundTheory.Heights₂.Heights.Kleiman
