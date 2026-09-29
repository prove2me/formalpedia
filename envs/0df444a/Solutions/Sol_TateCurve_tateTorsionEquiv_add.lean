-- Prove2me | solution 1 for TateCurve.tateTorsionEquiv_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/135bfb1c-9d7a-5e79-aebe-c92a5c41c669

import Mathlib
import Definitions.Def_TateCurve_TorsionParametrization
import Theorems.Thm_TateCurve_tateTorsionPoint_decomp
import Theorems.Thm_TateCurve_tateTorsionPoint_snd_eq_nsmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_tateTorsionEquiv_add

open scoped NNReal WeierstrassCurve.Affine
open WeierstrassCurve

namespace TateCurve
p2m_export "TateCurve" "tateParam_offLattice tateTorsionPoint tateTorsionPoint_spec tateTorsionPoint_zero_zero nsmul_tateTorsionPoint tateTorsionEquiv tateTorsionPoint_fst_eq_nsmul nonsingular_point OffLattice pointX pointY b curve tateTorsionPoint_decomp tateTorsionPoint_snd_eq_nsmul"
p2m_open "TateCurve"

private lemma ps_congr {K : Type*} [Field K] [DecidableEq K]
    {W : WeierstrassCurve K} {x x' y y' : K}
    (hx : x = x') (hy : y = y')
    (h : W.toAffine.Nonsingular x y) (h' : W.toAffine.Nonsingular x' y') :
    (Affine.Point.some x y h : W.toAffine.Point) = Affine.Point.some x' y' h' := by
  subst hx; subst hy; rfl

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [IsAlgClosed K] [DecidableEq K]
variable {q ζ t : K} {p : ℕ}

private lemma ttp_fst_eq_nsmul (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q) {i : ℕ} (hi : i < p) :
    tateTorsionPoint q ζ t hq0 hq1 hp hζ ht i 0
      = i • tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 1 0 := by
  rcases Nat.eq_zero_or_pos i with hi0 | hi1
  · rw [hi0, tateTorsionPoint_zero_zero, zero_nsmul]
  · have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
    have ht0 : t ≠ 0 := fun h0 => hq0 (by rw [← ht, h0, zero_pow hp.ne_zero])
    have h10 : ¬((1 : ℕ) = 0 ∧ (0 : ℕ) = 0) := by omega
    have hi0' : ¬(i = 0 ∧ (0 : ℕ) = 0) := by omega
    have hP1 := tateTorsionPoint_spec (q := q) (ζ := ζ) (t := t) hq0 hq1 hp hζ ht
      (i := 1) (j := 0) (by omega) hp.pos h10
    have hPi := tateTorsionPoint_spec (q := q) (ζ := ζ) (t := t) hq0 hq1 hp hζ ht
      (i := i) (j := 0) hi hp.pos hi0'

    have hparamζ : ζ ^ 1 * t ^ 0 = ζ := by rw [pow_one, pow_zero, mul_one]
    have hparamζi : ζ ^ i * t ^ 0 = ζ ^ i := by rw [pow_zero, mul_one]
    have hζoff : OffLattice q ζ := by
      have h := tateParam_offLattice (q := q) hq0 hq1 hζ ht (i := 1) (j := 0)
        (by omega) hp.pos h10
      rwa [hparamζ] at h
    have hζns : (curve q).toAffine.Nonsingular (pointX q ζ) (pointY q ζ) :=
      nonsingular_point hq0 hq1 hζ0 hζoff
    have hζi_off : OffLattice q (ζ ^ i) := by
      have h := tateParam_offLattice (q := q) hq0 hq1 hζ ht hi hp.pos hi0'
      rwa [hparamζi] at h
    have hζi_ns : (curve q).toAffine.Nonsingular (pointX q (ζ ^ i)) (pointY q (ζ ^ i)) :=
      nonsingular_point hq0 hq1 (pow_ne_zero i hζ0) hζi_off

    have eP1 : tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 1 0
        = Affine.Point.some (pointX q ζ) (pointY q ζ) hζns := by
      rw [hP1]
      exact ps_congr (congrArg (pointX q) hparamζ) (congrArg (pointY q) hparamζ) _ hζns
    have ePi : tateTorsionPoint q ζ t hq0 hq1 hp hζ ht i 0
        = Affine.Point.some (pointX q (ζ ^ i)) (pointY q (ζ ^ i)) hζi_ns := by
      rw [hPi]
      exact ps_congr (congrArg (pointX q) hparamζi) (congrArg (pointY q) hparamζi) _ hζi_ns
    rw [eP1, ePi]
    exact tateTorsionPoint_fst_eq_nsmul hq0 hq1 hp hp5 hζ ht hζns hi1 hi hζi_ns

private lemma ttp_linearize (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q) {i j : ℕ} (hi : i < p) (hj : j < p) :
    tateTorsionPoint q ζ t hq0 hq1 hp hζ ht i j
      = i • tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 1 0
        + j • tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 0 1 := by
  rw [tateTorsionPoint_decomp hq0 hq1 hp hp5 hζ ht hi hj,
      ttp_fst_eq_nsmul hq0 hq1 hp hp5 hζ ht hi,
      tateTorsionPoint_snd_eq_nsmul hq0 hq1 hp hp5 hζ ht hj]

private lemma nsmul_mod_of_nsmul_eq_zero {A : Type*} [AddCommGroup A] {P : A} {p : ℕ}
    (hP : p • P = 0) (n : ℕ) : (n % p) • P = n • P := by
  have h2 : (n / p * p) • P = 0 := by rw [← smul_smul, hP, smul_zero]
  have key : n = n % p + n / p * p := by
    rw [Nat.mul_comm]; exact (Nat.mod_add_div n p).symm
  conv_rhs => rw [key, add_nsmul, h2, add_zero]

end TateCurve

p2m_open "TateCurve P2MW.S_TateCurve_tateTorsionEquiv_add.TateCurve"

theorem solution
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] [IsAlgClosed K] [DecidableEq K]
    {q ζ t : K} (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    (a b : Fin p × Fin p) :
    ((TateCurve.tateTorsionEquiv q ζ t hq0 hq1 Fact.out hp5 hζ ht (a + b) :
        (TateCurve.curve q).n_torsionGen p) : (TateCurve.curve q).toAffine.Point)
      = ((TateCurve.tateTorsionEquiv q ζ t hq0 hq1 Fact.out hp5 hζ ht a :
        (TateCurve.curve q).n_torsionGen p) : (TateCurve.curve q).toAffine.Point)
      + ((TateCurve.tateTorsionEquiv q ζ t hq0 hq1 Fact.out hp5 hζ ht b :
        (TateCurve.curve q).n_torsionGen p) : (TateCurve.curve q).toAffine.Point) := by
  have hp : p.Prime := Fact.out

  have heq : ∀ c : Fin p × Fin p,
      ((tateTorsionEquiv q ζ t hq0 hq1 Fact.out hp5 hζ ht c :
          (curve q).n_torsionGen p) : (curve q).toAffine.Point)
        = tateTorsionPoint q ζ t hq0 hq1 hp hζ ht (c.1 : ℕ) (c.2 : ℕ) := by
    intro c
    simp only [tateTorsionEquiv, Equiv.ofBijective_apply]
  rw [heq (a + b), heq a, heq b]

  set P₁ := tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 1 0 with hP₁_def
  set P₂ := tateTorsionPoint q ζ t hq0 hq1 hp hζ ht 0 1 with hP₂_def
  rw [ttp_linearize hq0 hq1 hp hp5 hζ ht (a + b).1.isLt (a + b).2.isLt,
      ttp_linearize hq0 hq1 hp hp5 hζ ht a.1.isLt a.2.isLt,
      ttp_linearize hq0 hq1 hp hp5 hζ ht b.1.isLt b.2.isLt]

  have hpP₁ : p • P₁ = 0 := by
    rw [hP₁_def]; exact nsmul_tateTorsionPoint hq0 hq1 hp hp5 hζ ht 1 0
  have hpP₂ : p • P₂ = 0 := by
    rw [hP₂_def]; exact nsmul_tateTorsionPoint hq0 hq1 hp hp5 hζ ht 0 1

  have hfst : ((a + b).1 : ℕ) = ((a.1 : ℕ) + (b.1 : ℕ)) % p := by
    simp [Prod.fst_add, Fin.val_add]
  have hsnd : ((a + b).2 : ℕ) = ((a.2 : ℕ) + (b.2 : ℕ)) % p := by
    simp [Prod.snd_add, Fin.val_add]
  rw [hfst, hsnd, nsmul_mod_of_nsmul_eq_zero hpP₁, nsmul_mod_of_nsmul_eq_zero hpP₂,
      add_nsmul, add_nsmul]
  abel

end S_TateCurve_tateTorsionEquiv_add
end P2MW
export P2MW.S_TateCurve_tateTorsionEquiv_add (solution)
