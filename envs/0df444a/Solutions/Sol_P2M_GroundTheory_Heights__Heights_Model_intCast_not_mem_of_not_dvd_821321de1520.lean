-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_intCast_not_mem_of_not_dvd_821321de1520
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:05:10.675276+00:00
-- url     : https://prove2.me/submissions/90753bc6-16a7-4b25-ba30-fcecafc3d93e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLoc

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
open ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {A : Type*} [CommRing A] {Q : Ideal A} (hQ : Q ≠ ⊤) {p : ℕ}
    (hp : p.Prime) (hpQ : (p : A) ∈ Q) {s : ℤ} (hs : ¬ (p : ℤ) ∣ s) : (s : A) ∉ Q := by
  intro hsQ
  have hcop : IsCoprime (p : ℤ) s := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : ¬ p ∣ s.natAbs := fun h => hs (Int.natCast_dvd.mpr h)
    simpa [Int.gcd] using (Nat.Prime.coprime_iff_not_dvd hp).mpr this
  obtain ⟨u, v, huv⟩ := hcop
  have h1 := congrArg (Int.cast : ℤ → A) huv
  push_cast at h1
  apply hQ
  rw [Ideal.eq_top_iff_one, ← h1]
  exact add_mem (Q.mul_mem_left _ hpQ) (Q.mul_mem_left _ hsQ)
end GroundTheory.Heights₂.Heights.Model
