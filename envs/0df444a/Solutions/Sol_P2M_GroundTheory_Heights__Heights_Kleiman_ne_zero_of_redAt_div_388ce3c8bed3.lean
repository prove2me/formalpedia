-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_ne_zero_of_redAt_div_388ce3c8bed3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:32:22.588351+00:00
-- url     : https://prove2.me/submissions/31926d8e-4d3f-4d80-afd6-21706d89b6c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionSystems
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
  (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
  {Nb : LineBundle k x} {r : ℕ} {h : Fin (r + 1) → Ω}
include hsp
variable {g : Ω}
variable {σ : Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hσ : σ / g ∈ locAt k x y) (hσr : redAt k x y (σ / g) ≠ 0) : σ ≠ 0 :=
  fun h0 => (locAt_inv hsp hσ hσr).1 (by rw [h0, zero_div])
end GroundTheory.Heights₂.Heights.Kleiman
