-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_dvd_pow_of_ne_zero_of_not_isUnit_81bea8ad7a4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:24:20.867263+00:00
-- url     : https://prove2.me/submissions/d46b63f2-8c78-46be-bd70-d63261571a98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBTorsionFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {r x : R} (hr : r ≠ 0) (hx : x ≠ 0) (hxu : ¬IsUnit x) :
    ∃ k : ℕ, r ∣ x ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.associated_pow_irreducible hr hϖ
  obtain ⟨b, hb⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx hϖ
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hxu (associated_one_iff_isUnit.mp (by simpa using hb))
  refine ⟨a, ha.dvd.trans ((pow_dvd_pow ϖ (Nat.le_mul_of_pos_left a (Nat.pos_of_ne_zero hb0))).trans ?_)⟩
  rw [pow_mul]
  exact (hb.pow_pow (n := a)).symm.dvd
end GroundTheory.Heights₂.Heights.Vertical
