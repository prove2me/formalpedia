-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_eq_zero_of_mul_of_coprime_16bf724ac7de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:05:13.10949+00:00
-- url     : https://prove2.me/submissions/22799da3-e70d-4efc-b3cc-1326758d6cb1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsLocSectionsInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PLocSectionsInj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry Opposite
noncomputable section
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {B : Type*} [CommRing B] (p : ℕ) (hp : p.Prime) (e N' : ℕ) (u : ℤ)
    (hu : ¬ (p : ℤ) ∣ u) (hN' : IsUnit (N' : B)) (t : B)
    (h1 : ((p ^ e * N' : ℕ) : B) * t = 0) (h2 : (u : B) * t = 0) : t = 0 := by
  have hc : IsCoprime u ((p : ℤ) ^ e) :=
    ((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr hu).symm.pow_right
  obtain ⟨x, y, hxy⟩ := hc
  have hxy' := congrArg (Int.cast : ℤ → B) hxy
  push_cast at hxy' h1
  have h3 : (N' : B) * t = 0 := by
    linear_combination (-(N' : B) * t) * hxy' + (x : B) * (N' : B) * h2 + (y : B) * h1
  exact hN'.mul_right_eq_zero.mp h3
end GroundTheory.Heights₂.Heights.Model
