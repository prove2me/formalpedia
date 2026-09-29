-- Prove2me | solution 1 for PDivisibleGroup.nsmul_eq_zero_iff_exists_pointsMkAdd_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/921be716-12ce-5056-8150-cac9b795675b

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_nsmul_eq_zero_iff_exists_pointsMkAdd_eq

set_option autoImplicit false

open PDivisibleGroup

namespace PDivPtsTorsion

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
variable {L : Type} [CommRing L] [Algebra R L]

theorem nsmul_eq_zero_iff (n : ℕ) (z : G.Points L) :
    (p ^ n) • z = 0 ↔ ∃ x : G.Point L n, G.pointsMkAdd L n (Additive.ofMul x) = z := by
  constructor
  · intro hz
    obtain ⟨m, y, rfl⟩ := Points.exists_mkAdd G z

    set w := max m n with hw
    have hy : G.pointsMkAdd L w (Additive.ofMul (G.pointInclLE L (le_max_left m n) y)) =
        G.pointsMkAdd L m (Additive.ofMul y) := G.pointsMkAdd_pointInclLE _ y
    rw [← hy] at hz ⊢
    set y' := G.pointInclLE L (le_max_left m n) y with hy'

    have hpow : y' ^ (p ^ n) = 1 := by
      apply G.pointsMkAdd_injective w
      change G.pointsMkAdd L w (Additive.ofMul (y' ^ p ^ n)) = G.pointsMkAdd L w (Additive.ofMul 1)
      rw [ofMul_pow, map_nsmul, hz, ofMul_one, map_zero]

    obtain ⟨x, hx⟩ := G.exists_pointInclLE_eq_of_pow_eq_one (le_max_right m n) y' hpow
    exact ⟨x, by rw [← hx, pointsMkAdd_pointInclLE]⟩
  · rintro ⟨x, rfl⟩
    exact G.nsmul_pointsMkAdd_eq_zero n x

end PDivPtsTorsion

theorem solution
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (L : Type) [CommRing L] [Algebra R L] (n : ℕ) (z : G.Points L) :
    (p ^ n) • z = 0 ↔ ∃ x : G.Point L n, G.pointsMkAdd L n (Additive.ofMul x) = z :=
  PDivPtsTorsion.nsmul_eq_zero_iff G n z

end S_PDivisibleGroup_nsmul_eq_zero_iff_exists_pointsMkAdd_eq
end P2MW
export P2MW.S_PDivisibleGroup_nsmul_eq_zero_iff_exists_pointsMkAdd_eq (solution)
