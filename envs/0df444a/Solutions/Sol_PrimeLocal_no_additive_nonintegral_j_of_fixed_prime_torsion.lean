-- Prove2me | solution 1 for PrimeLocal.no_additive_nonintegral_j_of_fixed_prime_torsion
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T00:18:08.089953+00:00
-- url     : https://prove2.me/submissions/f0fe2a13-3c6e-463c-9382-df5e20bc80ae

import Mathlib
import Theorems.Thm_PrimeLocal_exists_tate_sign_data_of_nonintegral_j
import Theorems.Thm_PrimeLocal_exists_inertia_negating_tate_sign_of_additive_nonintegral_j
import Theorems.Thm_PrimeLocal_tatePrimeTorsion_inertia_coordinates_of_ne_residueChar
import Theorems.Thm_PrimeLocal_dvd_discr_and_dvd_c4_iff_hasAdditiveReduction
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_tateCurve_signTwist_of_variableChange_galois_signBehavior
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal
universe u v

namespace PrimeLocal
theorem _root_.solution (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p q : ℕ} [Fact q.Prime] (hmin : WeierstrassCurve.IsMinimal ℤ_[q] (W.map (Int.castRingHom ℚ_[q]))) (hp : p.Prime) (hp5 : 5 ≤ p) (hqp : q ≠ p) (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : (q : ℤ) ∣ W.c₄) (hj : ¬ ((q : ℤ) ^ padicValInt q W.Δ ∣ W.c₄ ^ 3)) (x y : ℚ) (h : (W.map (Int.castRingHom ℚ)).toAffine.Nonsingular x y) (hP : addOrderOf (WeierstrassCurve.Affine.Point.some x y h) = p) : False  := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨qT, hqT0, hqT1, d, s, C, hs, hC, hCσ⟩ :=
    exists_tate_sign_data_of_nonintegral_j W hΔ q hj
  obtain ⟨σ, hσ, hσs⟩ :=
    exists_inertia_negating_tate_sign_of_additive_nonintegral_j
      W hΔ q hj qT hqT0 hqT1 d s C hs hC hCσ hmin hqΔ hqc₄
  obtain ⟨ψ, hψ⟩ :=
    WeierstrassCurve.exists_addEquiv_point_tateCurve_signTwist_of_variableChange_galois_signBehavior
      W q qT s C hC hCσ
  let P₀ : (W⁄ℚ).Point := Point.some x y h
  let Pq : ((W.map (Int.castRingHom ℚ_[q]))⁄ℚ_[q]).Point :=
    Point.baseChange (W' := W.toAffine) ℚ ℚ_[q] P₀
  let P : ((W.map (Int.castRingHom ℚ_[q]))⁄(AlgebraicClosure ℚ_[q])).Point :=
    Point.baseChange (W' := (W.map (Int.castRingHom ℚ_[q])).toAffine)
      ℚ_[q] (AlgebraicClosure ℚ_[q]) Pq
  have hPqtor : p • Pq = 0 := by
    have htor : p • P₀ = 0 := by
      rw [← hP]
      exact addOrderOf_nsmul_eq_zero P₀
    change p • Point.baseChange (W' := W.toAffine) ℚ ℚ_[q] P₀ = 0
    rw [← map_nsmul, htor, _root_.map_zero]
  have hPtor : p • P = 0 := by
    change p • Point.baseChange (W' := (W.map (Int.castRingHom ℚ_[q])).toAffine)
      ℚ_[q] (AlgebraicClosure ℚ_[q]) Pq = 0
    rw [← map_nsmul, hPqtor, _root_.map_zero]
  have hPne : P ≠ 0 := by
    intro hzero
    have hzeroq : Pq = 0 :=
      Point.map_injective (Algebra.ofId ℚ_[q] (AlgebraicClosure ℚ_[q]))
        (hzero.trans (_root_.map_zero _).symm)
    have hzero₀ : P₀ = 0 :=
      Point.map_injective (W' := W.toAffine) (Algebra.ofId ℚ ℚ_[q])
        (hzeroq.trans (_root_.map_zero _).symm)
    change Point.some x y h = 0 at hzero₀
    cases hzero₀
  have hPfix : σ • P = P := by
    change Point.map σ.toAlgHom
      (Point.baseChange (W' := (W.map (Int.castRingHom ℚ_[q])).toAffine)
        ℚ_[q] (AlgebraicClosure ℚ_[q]) Pq) = _
    exact Point.map_baseChange σ.toAlgHom Pq
  let T : Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[q])).Point p :=
    ⟨ψ P, by
      rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul, ← map_nsmul, hPtor, _root_.map_zero]⟩
  have hTsign : σ • T = -T := by
    apply Subtype.ext
    change σ • ψ P = -ψ P
    have hh := (hψ σ).2 hσs P
    rw [hPfix] at hh
    simpa only [neg_neg] using (congrArg Neg.neg hh).symm
  obtain ⟨ζ, t, hζ, ht, φ, hφadd, hφσ⟩ :=
    tatePrimeTorsion_inertia_coordinates_of_ne_residueChar q p hp5 hqp.symm qT hqT0 hqT1
  let e : (ZMod p × ZMod p) ≃+
      Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[q])).Point p :=
    { φ with map_add' := fun a b => Subtype.ext (hφadd a b) }
  obtain ⟨c, hc⟩ := hφσ σ hσ
  obtain ⟨ij, hij⟩ := e.surjective T
  rcases ij with ⟨i, j⟩
  have heq : (i + c • j, j) = -(i, j) := by
    apply e.injective
    rw [map_neg]
    change φ (i + c • j, j) = -(φ (i, j))
    rw [← hc i j]
    change σ • e (i, j) = -e (i, j)
    rw [hij, hTsign]
  have hjneg : j = -j := congrArg Prod.snd heq
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
    omega
  have hjzero : j = 0 := by
    have hz : (2 : ZMod p) * j = 0 := by
      calc
        2 * j = j + j := two_mul j
        _ = -j + j := congrArg (fun z => z + j) hjneg
        _ = 0 := neg_add_cancel j
    exact (mul_eq_zero.mp hz).resolve_left htwo
  have hineg : i = -i := by simpa [hjzero] using congrArg Prod.fst heq
  have hizero : i = 0 := by
    have hz : (2 : ZMod p) * i = 0 := by
      calc
        2 * i = i + i := two_mul i
        _ = -i + i := congrArg (fun z => z + i) hineg
        _ = 0 := neg_add_cancel i
    exact (mul_eq_zero.mp hz).resolve_left htwo
  have hTzero : T = 0 := by
    rw [← hij, hizero, hjzero]
    exact e.map_zero
  apply hPne
  apply ψ.injective
  exact (congrArg Subtype.val hTzero).trans ψ.map_zero.symm
end PrimeLocal
