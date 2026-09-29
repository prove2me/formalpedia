-- Prove2me | solution 1 for PDivisibleGroup.natCard_torsionBy_points_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a2c7e835-2b7f-5118-ad4d-59ccfc50c01c

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_natCard_torsionBy_points_eq_pow

set_option autoImplicit false

open PDivisibleGroup

namespace PDivPtsCount

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

private theorem _root_.PDivPtsCount.mem_torsionBy_iff (n : ℕ) (z : G.Points L) :
    z ∈ Submodule.torsionBy ℤ (G.Points L) ((p ^ n : ℕ) : ℤ) ↔
      ∃ x : G.Point L n, G.pointsMkAdd L n (Additive.ofMul x) = z := by
  rw [Submodule.mem_torsionBy_iff, ← nsmul_eq_zero_iff G n z, natCast_zsmul]

p2m_export "PDivPtsCount" "mem_torsionBy_iff"

noncomputable def pointEquivTorsionBy (n : ℕ) :
    G.Point L n ≃ Submodule.torsionBy ℤ (G.Points L) ((p ^ n : ℕ) : ℤ) :=
  Equiv.ofBijective (fun x => ⟨G.pointsMkAdd L n (Additive.ofMul x), (mem_torsionBy_iff G n _).2 ⟨x, rfl⟩⟩)
    ⟨fun x y hxy => G.pointsMkAdd_injective n (congrArg Subtype.val hxy),
     fun z => by
      obtain ⟨x, hx⟩ := (mem_torsionBy_iff G n z.1).1 z.2
      exact ⟨x, Subtype.ext hx⟩⟩

section Count

variable (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]

theorem natCard_point (n : ℕ) : Nat.card (G.Point K n) = p ^ (n * h) := by
  rw [← G.finrank_level n]
  change Nat.card (WithConv (G.level n →ₐ[R] K)) = _
  rw [Nat.card_congr (WithConv.equiv (G.level n →ₐ[R] K))]
  exact HopfAlgebra.natCard_algHom_eq_finrank_of_charZero R (G.level n) K

theorem natCard_torsionBy (n : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (G.Points K) ((p ^ n : ℕ) : ℤ)) = p ^ (n * h) := by
  rw [← natCard_point G K n]
  exact (Nat.card_congr (pointEquivTorsionBy G n)).symm

end Count

end PDivPtsCount

theorem solution
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L] (n : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (G.Points L) ((p ^ n : ℕ) : ℤ)) = p ^ (n * h) :=
  PDivPtsCount.natCard_torsionBy G L n

end S_PDivisibleGroup_natCard_torsionBy_points_eq_pow
end P2MW
export P2MW.S_PDivisibleGroup_natCard_torsionBy_points_eq_pow (solution)
