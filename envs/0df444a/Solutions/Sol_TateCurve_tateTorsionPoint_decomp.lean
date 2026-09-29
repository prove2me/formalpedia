-- Prove2me | solution 1 for TateCurve.tateTorsionPoint_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d5ce4f63-4801-5e12-a3a1-6bb04dc6711b

import Mathlib
import Definitions.Def_TateCurve_TorsionParametrization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_tateTorsionPoint_decomp

open scoped NNReal WeierstrassCurve.Affine
open WeierstrassCurve

namespace TateCurve
p2m_export "TateCurve" "tateParam_ne_zero tateParam_offLattice tateTorsionPoint tateTorsionPoint_spec tateTorsionPoint_zero_zero tateTorsionPoint_zeta_mul nonsingular_point OffLattice pointX pointY curve"
p2m_open "TateCurve"

private lemma ps_congr {K : Type*} [Field K] [DecidableEq K]
    {W : WeierstrassCurve K} {x x' y y' : K}
    (hx : x = x') (hy : y = y')
    (h : W.toAffine.Nonsingular x y) (h' : W.toAffine.Nonsingular x' y') :
    (Affine.Point.some x y h : W.toAffine.Point) = Affine.Point.some x' y' h' := by
  subst hx; subst hy; rfl

end TateCurve

p2m_open "TateCurve P2MW.S_TateCurve_tateTorsionPoint_decomp.TateCurve"

theorem solution
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] [IsAlgClosed K] [DecidableEq K]
    {q ζ t : K} (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    {i j : ℕ} (hi : i < p) (hj : j < p) :
    TateCurve.tateTorsionPoint q ζ t hq0 hq1 hp hζ ht i j
      = TateCurve.tateTorsionPoint q ζ t hq0 hq1 hp hζ ht i 0
        + TateCurve.tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 0 j := by
  rcases Nat.eq_zero_or_pos i with hi0 | hi1
  ·
    rw [hi0, tateTorsionPoint_zero_zero, zero_add]
  · rcases Nat.eq_zero_or_pos j with hj0 | hj1
    ·
      rw [hj0, tateTorsionPoint_zero_zero, add_zero]
    ·
      have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
      have ht0 : t ≠ 0 := fun h0 => hq0 (by rw [← ht, h0, zero_pow hp.ne_zero])
      have htj0 : t ^ j ≠ 0 := pow_ne_zero j ht0
      have hij : ¬(i = 0 ∧ j = 0) := by omega
      have hi00 : ¬(i = 0 ∧ (0 : ℕ) = 0) := by omega
      have h0j : ¬((0 : ℕ) = 0 ∧ j = 0) := by omega

      have hparam_i0 : ζ ^ i * t ^ 0 = ζ ^ i := by rw [pow_zero, mul_one]
      have hparam_0j : ζ ^ 0 * t ^ j = t ^ j := by rw [pow_zero, one_mul]

      have htj_off : OffLattice q (t ^ j) := by
        have h := tateParam_offLattice (q := q) hq0 hq1 hζ ht (i := 0) (j := j) hp.pos hj h0j
        rwa [hparam_0j] at h
      have hζi_off : OffLattice q (ζ ^ i) := by
        have h := tateParam_offLattice (q := q) hq0 hq1 hζ ht (i := i) (j := 0) hi hp.pos hi00
        rwa [hparam_i0] at h
      have hζitj_off : OffLattice q (ζ ^ i * t ^ j) :=
        tateParam_offLattice (q := q) hq0 hq1 hζ ht hi hj hij

      have h₁ : (curve q).toAffine.Nonsingular (pointX q (ζ ^ i * t ^ j))
          (pointY q (ζ ^ i * t ^ j)) :=
        nonsingular_point hq0 hq1 (tateParam_ne_zero hζ0 ht0) hζitj_off
      have h₂ : (curve q).toAffine.Nonsingular (pointX q (ζ ^ i)) (pointY q (ζ ^ i)) :=
        nonsingular_point hq0 hq1 (pow_ne_zero i hζ0) hζi_off
      have h₃ : (curve q).toAffine.Nonsingular (pointX q (t ^ j)) (pointY q (t ^ j)) :=
        nonsingular_point hq0 hq1 htj0 htj_off

      have hmain := tateTorsionPoint_zeta_mul hq0 hq1 hp hp5 hζ hi1 hi
        htj0 htj_off hζitj_off h₁ h₂ h₃

      have eij : tateTorsionPoint q ζ t hq0 hq1 hp hζ ht i j
          = Affine.Point.some (pointX q (ζ ^ i * t ^ j)) (pointY q (ζ ^ i * t ^ j)) h₁ := by
        rw [tateTorsionPoint_spec hq0 hq1 hp hζ ht hi hj hij]
      have ei0 : tateTorsionPoint q ζ t hq0 hq1 hp hζ ht i 0
          = Affine.Point.some (pointX q (ζ ^ i)) (pointY q (ζ ^ i)) h₂ := by
        rw [tateTorsionPoint_spec hq0 hq1 hp hζ ht hi hp.pos hi00]
        exact ps_congr (congrArg (pointX q) hparam_i0) (congrArg (pointY q) hparam_i0) _ h₂
      have e0j : tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 0 j
          = Affine.Point.some (pointX q (t ^ j)) (pointY q (t ^ j)) h₃ := by
        rw [tateTorsionPoint_spec hq0 hq1 hp hζ ht hp.pos hj h0j]
        exact ps_congr (congrArg (pointX q) hparam_0j) (congrArg (pointY q) hparam_0j) _ h₃
      rw [eij, ei0, e0j]
      exact hmain

end S_TateCurve_tateTorsionPoint_decomp
end P2MW
export P2MW.S_TateCurve_tateTorsionPoint_decomp (solution)
