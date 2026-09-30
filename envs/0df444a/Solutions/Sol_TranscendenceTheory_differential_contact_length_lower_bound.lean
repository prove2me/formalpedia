-- Prove2me | solution 1 for TranscendenceTheory.differential_contact_length_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T16:11:07.548333+00:00
-- url     : https://prove2.me/submissions/227bacef-3425-4f59-9535-521218fa3f4a

import Definitions.Def_TranscendenceTheory_DifferentialMultiplicity
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

noncomputable section
namespace TranscendenceTheory

variable {R : Type*} [CommRing R] [Algebra ℚ R]

private lemma iter_add (D : Derivation ℚ R R) (n : ℕ) (f g : R) :
    (D^[n]) (f + g) = (D^[n]) f + (D^[n]) g := by
  simpa only [Module.End.pow_apply] using! (D.toLinearMap ^ n).map_add f g

private lemma jets_mul (D : Derivation ℚ R R) (p : Ideal R) (n : ℕ)
    (f : R) (hf : ∀ j < n, (D^[j]) f ∈ p) (a : R) :
    ∀ j < n, (D^[j]) (a * f) ∈ p := by
  induction n generalizing a f with
  | zero => simp
  | succ n ih =>
    intro j hj
    cases j with
    | zero => simpa using p.mul_mem_left a (hf 0 (by omega))
    | succ j =>
      rw [Function.iterate_succ_apply, D.leibniz, smul_eq_mul, smul_eq_mul, iter_add]
      apply p.add_mem
      · apply ih (D f) _ a j (by omega)
        intro k hk
        simpa only [← Function.iterate_succ_apply] using hf (k + 1) (by omega)
      · rw [mul_comm f (D a)]
        exact ih f (fun k hk => hf k (by omega)) (D a) j (by omega)

private lemma mem_contact (D : Derivation ℚ R R) (p : Ideal R) (n : ℕ) (f : R) :
    f ∈ differentialContactIdeal D p n ↔ ∀ j < n, (D^[j]) f ∈ p := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      intro j hj
      simpa only [Module.End.pow_apply] using!
        (show (D.toLinearMap ^ j) 0 ∈ p by simp)
    | add x y hx hy ihx ihy =>
      intro j hj
      rw [iter_add]
      exact p.add_mem (ihx j hj) (ihy j hj)
    | smul a x hx ih =>
      simpa only [smul_eq_mul] using jets_mul D p n x ih a
  · intro hf; exact Ideal.subset_span hf

private lemma pow_jets (D : Derivation ℚ R R) (p : Ideal R) (q : R) (hq : q ∈ p)
    (n : ℕ) : ∀ j < n, (D^[j]) (q ^ n) ∈ p := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro j hj
    cases j with
    | zero => simpa only [Function.iterate_zero_apply, pow_succ] using p.mul_mem_left (q ^ n) hq
    | succ j =>
      rw [Function.iterate_succ_apply, D.leibniz_pow]
      simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul, Nat.cast_add, Nat.cast_one]
      have h := jets_mul D p n (q ^ n) ih ((n + 1 : R) * D q) j (by omega)
      convert h using 2
      ring

private lemma top_derivative_mod (D : Derivation ℚ R R) (p : Ideal R) (q : R)
    (hq : q ∈ p) (n : ℕ) (a : R) :
    Ideal.Quotient.mk p ((D^[n]) (a * q ^ n)) =
      Ideal.Quotient.mk p a * (n.factorial : R ⧸ p) * Ideal.Quotient.mk p (D q) ^ n := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, D.leibniz, D.leibniz_pow]
    simp only [Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul]
    rw [iter_add, map_add]
    have hz : Ideal.Quotient.mk p ((D^[n]) (q ^ (n + 1) * D a)) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [mul_comm]
      exact jets_mul D p (n + 1) (q ^ (n + 1)) (pow_jets D p q hq (n + 1))
        (D a) n (by omega)
    rw [hz, add_zero]
    have heq : a * (((n + 1 : ℕ) : R) * (q ^ n * D q)) =
        ((n + 1 : R) * a * D q) * q ^ n := by push_cast; ring
    rw [heq, ih]
    simp only [map_mul, map_add, map_one, map_natCast, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    ring


end TranscendenceTheory

open TranscendenceTheory

theorem solution
    (R : Type*) [CommRing R] [Algebra ℚ R]
    (D : Derivation ℚ R R) (p : Ideal R) [p.IsPrime]
    (q : R) (hq : q ∈ p) (hDq : D q ∉ p)
    (I : Ideal R) (T : ℕ) (hI : ∀ f ∈ I, ∀ j ≤ T, (D^[j]) f ∈ p) :
    (T + 1 : ℕ∞) ≤ Module.length R (R ⧸ I) := by
  classical
  let : CharZero (R ⧸ p) := Algebra.charZero_of_charZero ℚ (R ⧸ p)
  have hnz (n : ℕ) : (D^[n]) (q ^ n) ∉ p := by
    intro hz
    have hzero : Ideal.Quotient.mk p ((D^[n]) (q ^ n)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hz
    have hformula := top_derivative_mod D p q hq n 1
    simp only [one_mul, map_one] at hformula
    rw [hformula] at hzero
    have hfac : (n.factorial : R ⧸ p) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hd : Ideal.Quotient.mk p (D q) ≠ 0 := by
      intro he
      exact hDq (Ideal.Quotient.eq_zero_iff_mem.mp he)
    exact (mul_ne_zero hfac (pow_ne_zero n hd)) hzero
  have hstep (n : ℕ) : differentialContactIdeal D p (n + 1) < differentialContactIdeal D p n := by
    refine lt_iff_le_not_ge.mpr ⟨?_, ?_⟩
    · intro f hf
      apply (mem_contact D p n f).mpr
      intro j hj
      exact (mem_contact D p (n + 1) f).mp hf j (by omega)
    · intro hle
      have hpow : q ^ n ∈ differentialContactIdeal D p n :=
        (mem_contact D p n (q ^ n)).mpr (pow_jets D p q hq n)
      exact hnz n ((mem_contact D p (n + 1) (q ^ n)).mp (hle hpow) n (by omega))
  have hlength (n : ℕ) : (n : ℕ∞) ≤ Order.coheight (differentialContactIdeal D p n) := by
    induction n with
    | zero => exact bot_le
    | succ n ih =>
      calc
        (↑(n + 1) : ℕ∞) = ↑n + 1 := by simp
        _ ≤ Order.coheight (differentialContactIdeal D p n) + 1 := add_le_add ih le_rfl
        _ ≤ Order.coheight (differentialContactIdeal D p (n + 1)) :=
          Order.coheight_add_one_le (hstep n)
  have hle : I ≤ differentialContactIdeal D p (T + 1) := by
    intro f hf
    exact (mem_contact D p (T + 1) f).mpr (fun j hj => hI f hf j (by omega))
  rw [Module.length_quotient]
  simpa using (hlength (T + 1)).trans (Order.coheight_anti hle)
