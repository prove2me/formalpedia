-- Prove2me | solution 1 for TranscendenceTheory.derivation_formal_flow_unique
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T18:32:04.848362+00:00
-- url     : https://prove2.me/submissions/ff968108-00d3-4a89-81c8-5ea7926a5e56

import Theorems.Thm_TranscendenceTheory_derivation_formal_jet_substitution
import Mathlib.RingTheory.PowerSeries.Derivative

noncomputable section
open scoped Classical

private lemma aeval_coeff_eq_of_coeff_eq
    {K σ : Type*} [CommRing K]
    (p : MvPolynomial σ K) : ∀ (n : ℕ) (J H : σ → PowerSeries K),
    (∀ i, ∀ k ≤ n, PowerSeries.coeff k (J i) = PowerSeries.coeff k (H i)) →
    PowerSeries.coeff n (MvPolynomial.aeval J p) =
      PowerSeries.coeff n (MvPolynomial.aeval H p) := by
  induction p using MvPolynomial.induction_on with
  | C a => intro n J H h; simp
  | add p q hp hq =>
    intro n J H h
    simp only [map_add, hp n J H h, hq n J H h]
  | mul_X p i hp =>
    intro n J H h
    simp only [map_mul, MvPolynomial.aeval_X, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    rintro ⟨a, b⟩ hab
    have hn := Finset.mem_antidiagonal.mp hab
    have ha : a ≤ n := hn ▸ Nat.le_add_right a b
    have hb : b ≤ n := hn ▸ Nat.le_add_left b a
    rw [hp a J H (fun i k hk => h i k (hk.trans ha)), h i b hb]

theorem solution
    (K σ : Type*) [Field K] [CharZero K]
    (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K)) (v : σ → K) :
    let J : σ → PowerSeries K := fun i => PowerSeries.mk fun k =>
      MvPolynomial.eval v (D^[k] (MvPolynomial.X i)) / (k.factorial : K)
    (∀ i, PowerSeries.coeff 0 (J i) = v i) ∧
    (∀ i, PowerSeries.derivative K (J i) =
      MvPolynomial.aeval J (D (MvPolynomial.X i))) ∧
    ∀ H : σ → PowerSeries K,
      (∀ i, PowerSeries.coeff 0 (H i) = v i) →
      (∀ i, PowerSeries.derivative K (H i) =
        MvPolynomial.aeval H (D (MvPolynomial.X i))) → H = J := by
  classical
  let J : σ → PowerSeries K := fun i => PowerSeries.mk fun k =>
    MvPolynomial.eval v (D^[k] (MvPolynomial.X i)) / (k.factorial : K)
  have hinit (i : σ) : PowerSeries.coeff 0 (J i) = v i := by simp [J]
  have hode (i : σ) : PowerSeries.derivative K (J i) =
      MvPolynomial.aeval J (D (MvPolynomial.X i)) := by
    ext n
    rw [PowerSeries.coeff_derivative]
    have h := TranscendenceTheory.derivation_formal_jet_substitution K σ D v
      (D (MvPolynomial.X i)) n
    change (n.factorial : K) *
      PowerSeries.coeff n (MvPolynomial.aeval J (D (MvPolynomial.X i))) = _ at h
    have hn : (n.factorial : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hs : (n + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simp only [J, PowerSeries.coeff_mk, Function.iterate_succ_apply,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [← h]
    field_simp
    rfl
  refine ⟨hinit, hode, ?_⟩
  intro H hHinit hHode
  have hc : ∀ n : ℕ, ∀ i : σ, PowerSeries.coeff n (H i) =
      PowerSeries.coeff n (J i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => intro i; rw [hHinit, hinit]
      | succ n =>
        intro i
        have he := aeval_coeff_eq_of_coeff_eq (D (MvPolynomial.X i)) n H J
          (fun a k hk => ih k (Nat.lt_succ_of_le hk) a)
        rw [← hHode, ← hode] at he
        simp only [PowerSeries.coeff_derivative] at he
        exact mul_right_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n) he
  funext i
  ext n
  exact hc n i
