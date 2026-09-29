-- Prove2me | solution 1 for TateCurve.tateTorsionPoint_snd_eq_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/631c9c63-318d-54c2-91ae-e7d33a3eaa98

import Mathlib
import Definitions.Def_TateCurve_TorsionParametrization
import Theorems.Thm_TateCurve_tpow_succ_point_eq_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_tateTorsionPoint_snd_eq_nsmul

open scoped NNReal WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine

namespace TateCurve
p2m_export "TateCurve" "tateParam_offLattice tateTorsionPoint tateTorsionPoint_spec tateTorsionPoint_zero_zero nonsingular_point OffLattice pointX pointY curve tpow_succ_point_eq_add"
p2m_open "TateCurve"

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [IsAlgClosed K] [DecidableEq K]
variable {q ζ t : K} {p : ℕ}

private lemma ps_congr {W : WeierstrassCurve K} {x x' y y' : K}
    (hx : x = x') (hy : y = y')
    (h : W.toAffine.Nonsingular x y) (h' : W.toAffine.Nonsingular x' y') :
    (Point.some x y h : W.toAffine.Point) = Point.some x' y' h' := by
  subst hx; subst hy; rfl

private lemma ttp_0j_eq_point (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) (hp : p.Prime)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q) {j : ℕ} (hj1 : 1 ≤ j) (hjp : j < p)
    (hns : (curve q).toAffine.Nonsingular (pointX q (t ^ j)) (pointY q (t ^ j))) :
    tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 0 j
      = Point.some (pointX q (t ^ j)) (pointY q (t ^ j)) hns := by
  rw [tateTorsionPoint_spec hq0 hq1 hp hζ ht hp.pos hjp (by omega)]
  exact ps_congr (congrArg (pointX q) (by rw [pow_zero, one_mul]))
    (congrArg (pointY q) (by rw [pow_zero, one_mul])) _ hns

private lemma tpow_point_eq_nsmul (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    (h₂ : (curve q).toAffine.Nonsingular (pointX q t) (pointY q t)) :
    ∀ j : ℕ, 1 ≤ j → j < p →
      ∀ (hns : (curve q).toAffine.Nonsingular (pointX q (t ^ j)) (pointY q (t ^ j))),
        (Point.some (pointX q (t ^ j)) (pointY q (t ^ j)) hns : (curve q).toAffine.Point)
          = j • Point.some (pointX q t) (pointY q t) h₂ := by
  have ht0 : t ≠ 0 := fun h0 => hq0 (by rw [← ht, h0, zero_pow hp.ne_zero])
  intro j
  induction j with
  | zero => intro h1; omega
  | succ n ih =>
    intro _ hjp hns
    rcases Nat.eq_zero_or_pos n with hn0 | hn1
    ·
      subst hn0
      rw [one_nsmul]
      exact ps_congr (congrArg (pointX q) (pow_one t)) (congrArg (pointY q) (pow_one t)) hns h₂
    ·
      have htjoff : OffLattice q (t ^ n) := by
        have h := tateParam_offLattice (q := q) (ζ := ζ) hq0 hq1 hζ ht (i := 0) (j := n)
          hp.pos (by omega) (by omega)
        rwa [pow_zero, one_mul] at h
      have hns_n : (curve q).toAffine.Nonsingular (pointX q (t ^ n)) (pointY q (t ^ n)) :=
        nonsingular_point hq0 hq1 (pow_ne_zero n ht0) htjoff
      have hstep := tpow_succ_point_eq_add (ζ := ζ) hq0 hq1 hp hp5 hζ ht
        (j := n) hn1 hjp hns h₂ hns_n
      calc (Point.some (pointX q (t ^ (n + 1))) (pointY q (t ^ (n + 1))) hns :
            (curve q).toAffine.Point)
          = Point.some (pointX q t) (pointY q t) h₂
              + Point.some (pointX q (t ^ n)) (pointY q (t ^ n)) hns_n := hstep
        _ = Point.some (pointX q t) (pointY q t) h₂
              + n • Point.some (pointX q t) (pointY q t) h₂ := by
            rw [ih hn1 (by omega) hns_n]
        _ = (n + 1) • Point.some (pointX q t) (pointY q t) h₂ := by
            rw [add_comm, ← succ_nsmul]

end TateCurve

p2m_open "TateCurve P2MW.S_TateCurve_tateTorsionPoint_snd_eq_nsmul.TateCurve"

theorem solution
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] [IsAlgClosed K] [DecidableEq K]
    {q ζ t : K} (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    {j : ℕ} (hj : j < p) :
    TateCurve.tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 0 j
      = j • TateCurve.tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 0 1 := by
  have ht0 : t ≠ 0 := fun h0 => hq0 (by rw [← ht, h0, zero_pow hp.ne_zero])
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · rw [hj0, tateTorsionPoint_zero_zero, zero_nsmul]
  ·
    have ht1off : OffLattice q (t ^ 1) := by
      have h := tateParam_offLattice (q := q) (ζ := ζ) hq0 hq1 hζ ht (i := 0) (j := 1)
        hp.pos (by omega) (by omega)
      rwa [pow_zero, one_mul] at h
    have htjoff : OffLattice q (t ^ j) := by
      have h := tateParam_offLattice (q := q) (ζ := ζ) hq0 hq1 hζ ht (i := 0) (j := j)
        hp.pos hj (by omega)
      rwa [pow_zero, one_mul] at h
    have h₂' : (curve q).toAffine.Nonsingular (pointX q (t ^ 1)) (pointY q (t ^ 1)) :=
      nonsingular_point hq0 hq1 (pow_ne_zero 1 ht0) ht1off
    have h₂ : (curve q).toAffine.Nonsingular (pointX q t) (pointY q t) := by
      rw [← pow_one t]; exact h₂'
    have hnsj : (curve q).toAffine.Nonsingular (pointX q (t ^ j)) (pointY q (t ^ j)) :=
      nonsingular_point hq0 hq1 (pow_ne_zero j ht0) htjoff
    rw [ttp_0j_eq_point hq0 hq1 hp hζ ht hj1 hj hnsj,
        ttp_0j_eq_point hq0 hq1 hp hζ ht le_rfl (by omega) h₂',
        tpow_point_eq_nsmul hq0 hq1 hp hp5 hζ ht h₂ j hj1 hj hnsj]
    congr 1
    exact ps_congr (congrArg (pointX q) (pow_one t).symm)
      (congrArg (pointY q) (pow_one t).symm) h₂ h₂'

end S_TateCurve_tateTorsionPoint_snd_eq_nsmul
end P2MW
export P2MW.S_TateCurve_tateTorsionPoint_snd_eq_nsmul (solution)
