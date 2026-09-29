-- Prove2me | solution 1 for TateCurve.tateTorsionPoint_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b6c87816-9b65-5da2-bfb7-4f20e9fdf717

import Mathlib
import Definitions.Def_TateCurve_TorsionParametrization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_tateTorsionPoint_map

open scoped NNReal WeierstrassCurve.Affine
open WeierstrassCurve

namespace TateCurve
p2m_export "TateCurve" "tateParam_ne_zero tateParam_offLattice zeta_pow_mod tateTorsionPoint tateTorsionPoint_spec map_pointX_tateParam map_pointY_tateParam nonsingular_point pointX pointY curve"
p2m_open "TateCurve"

private lemma ps_congr {K : Type*} [Field K] [DecidableEq K]
    {W : WeierstrassCurve K} {x x' y y' : K}
    (hx : x = x') (hy : y = y')
    (h : W.toAffine.Nonsingular x y) (h' : W.toAffine.Nonsingular x' y') :
    (Affine.Point.some x y h : W.toAffine.Point) = Affine.Point.some x' y' h' := by
  subst hx; subst hy; rfl

end TateCurve

p2m_open "TateCurve P2MW.S_TateCurve_tateTorsionPoint_map.TateCurve"

theorem solution
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] [IsAlgClosed K] [DecidableEq K]
    {q ζ t : K} (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    (σ : K →+* K) (hσ : Isometry ⇑σ) (hσq : σ q = q)
    {e c : ℕ} (hσζ : σ ζ = ζ ^ e) (hσt : σ t = ζ ^ c * t)
    {i j : ℕ} (hi : i < p) (hj : j < p) (hij : ¬(i = 0 ∧ j = 0))
    (hns' : (TateCurve.curve q).toAffine.Nonsingular
      (σ (TateCurve.pointX q (ζ ^ i * t ^ j))) (σ (TateCurve.pointY q (ζ ^ i * t ^ j)))) :
    (WeierstrassCurve.Affine.Point.some
        (σ (TateCurve.pointX q (ζ ^ i * t ^ j))) (σ (TateCurve.pointY q (ζ ^ i * t ^ j))) hns'
      : (TateCurve.curve q).toAffine.Point)
      = TateCurve.tateTorsionPoint q ζ t hq0 hq1 hp hζ ht ((e * i + c * j) % p) j := by
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have ht0 : t ≠ 0 := fun h0 => hq0 (by rw [← ht, h0, zero_pow hp.ne_zero])

  have hX : σ (pointX q (ζ ^ i * t ^ j)) = pointX q (ζ ^ ((e * i + c * j) % p) * t ^ j) := by
    rw [map_pointX_tateParam hq0 hq1 hp hζ ht σ hσ hσq hσζ hσt i j,
        zeta_pow_mod hζp (e * i + c * j)]
  have hY : σ (pointY q (ζ ^ i * t ^ j)) = pointY q (ζ ^ ((e * i + c * j) % p) * t ^ j) := by
    rw [map_pointY_tateParam hq0 hq1 hp hζ ht σ hσ hσq hσζ hσt i j,
        zeta_pow_mod hζp (e * i + c * j)]

  set i₂ := (e * i + c * j) % p with hi₂def
  have hi₂ : i₂ < p := Nat.mod_lt _ hp.pos
  have hpe : ¬ p ∣ e := by
    intro hdvd
    obtain ⟨k, rfl⟩ := hdvd
    have h1 : ζ ^ (p * k) = 1 := by rw [pow_mul, hζp, one_pow]
    have h2 : σ ζ = σ 1 := by rw [hσζ, h1, map_one]
    exact hζ.ne_one (by omega) (σ.injective h2)
  have hij₂ : ¬(i₂ = 0 ∧ j = 0) := by
    rintro ⟨h1, h2⟩
    subst h2
    have hi0 : i ≠ 0 := fun h => hij ⟨h, rfl⟩
    rw [hi₂def, mul_zero, add_zero] at h1
    have hdvd : p ∣ e * i := Nat.dvd_of_mod_eq_zero h1
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · exact hpe h
    · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) h) (by omega)

  have hns₂ : (curve q).toAffine.Nonsingular (pointX q (ζ ^ i₂ * t ^ j))
      (pointY q (ζ ^ i₂ * t ^ j)) :=
    nonsingular_point hq0 hq1 (tateParam_ne_zero hζ0 ht0)
      (tateParam_offLattice hq0 hq1 hζ ht hi₂ hj hij₂)
  rw [tateTorsionPoint_spec hq0 hq1 hp hζ ht hi₂ hj hij₂]
  exact ps_congr hX hY hns' _

end S_TateCurve_tateTorsionPoint_map
end P2MW
export P2MW.S_TateCurve_tateTorsionPoint_map (solution)
