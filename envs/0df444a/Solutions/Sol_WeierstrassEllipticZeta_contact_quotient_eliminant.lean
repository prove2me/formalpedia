-- Prove2me | solution 1 for WeierstrassEllipticZeta.contact_quotient_eliminant
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T00:06:31.822336+00:00
-- url     : https://prove2.me/submissions/2a0069e6-6ca8-41c9-aec6-e5cef926e7f5

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.FinCases

noncomputable section
open WeierstrassEllipticZeta

private lemma contact_time_derivative (g₂ g₃ : ℂ) (c : Fin 2)
    (p : Polynomial ℂ) (k : ℕ) :
    (extensionChartDerivation g₂ g₃ c)^[k]
        (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) p) =
      Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (Polynomial.derivative^[k] p) := by
  have ht : extensionChartDerivation g₂ g₃ c (MvPolynomial.X (0 : Fin 4)) = 1 := by
    fin_cases c <;> simp [extensionChartDerivation]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.comp_aeval_eq,
      ht, smul_eq_mul, mul_one, Function.iterate_succ_apply']

private lemma contact_root_power_iff_jets (x : ℂ) (p : Polynomial ℂ) (N : ℕ) :
    (Polynomial.X - Polynomial.C x) ^ N ∣ p ↔
      ∀ k < N, (Polynomial.derivative^[k] p).eval x = 0 := by
  rw [Polynomial.X_sub_C_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  have h (k : ℕ) : (Polynomial.derivative^[k] p).eval x =
      (k.factorial : ℂ) * (Polynomial.taylor x p).coeff k := by
    rw [← Polynomial.factorial_smul_hasseDeriv]
    simp [Polynomial.taylor_coeff, nsmul_eq_mul]
  simp_rw [h, mul_eq_zero, Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _),
    false_or, Polynomial.taylor_apply]

theorem solution
    (G : Frontier.Geometry) (X : Finset ℂ) (N : ℕ)
    (J : Fin 2 → Ideal (MvPolynomial (Fin 4) ℂ))
    (hfinite : ∀ c, FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J c))
    (hcontact : ∀ x ∈ X, ∃ c : Fin 2,
      G.S (extensionChartDenominator c) x ≠ 0 ∧
      J c ≤ extensionChartContactIdeal G.L.g₂ G.L.g₃ c
        (extensionChartCoordinates G.S c x) N) :
    ∃ P : Polynomial ℂ, P.Monic ∧
      P.natDegree = ∑ c : Fin 2, Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J c) ∧
      ∀ x ∈ X, ∀ k < N, (Polynomial.derivative^[k] P).eval x = 0 := by
  classical
  let (c : Fin 2) : FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J c) := hfinite c
  let t (c : Fin 2) : MvPolynomial (Fin 4) ℂ ⧸ J c :=
    Ideal.Quotient.mk (J c) (MvPolynomial.X (0 : Fin 4))
  let p (c : Fin 2) : Polynomial ℂ := (Algebra.lmul ℂ _ (t c)).charpoly
  have hmonic (c : Fin 2) : (p c).Monic := LinearMap.charpoly_monic _
  have hdegree (c : Fin 2) : (p c).natDegree =
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J c) :=
    LinearMap.charpoly_natDegree _
  have hmem (c : Fin 2) :
      Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (p c) ∈ J c := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := Algebra.aeval_self_charpoly_lmul (R := ℂ) (t c)
    change Polynomial.aeval ((Ideal.Quotient.mkₐ ℂ (J c))
      (MvPolynomial.X (0 : Fin 4))) (p c) = 0 at h
    rw [Polynomial.aeval_algHom_apply] at h
    exact h
  refine ⟨∏ c : Fin 2, p c,
    Polynomial.monic_prod_of_monic _ _ (fun c _ => hmonic c), ?_, ?_⟩
  · rw [Polynomial.natDegree_prod_of_monic Finset.univ _ (fun c _ => hmonic c)]
    simp_rw [hdegree]
  · intro x hx
    obtain ⟨c, _, hc⟩ := hcontact x hx
    have hjets : ∀ k < N, (Polynomial.derivative^[k] (p c)).eval x = 0 := by
      intro k hk
      have h := (G.hcontact.1 c (extensionChartCoordinates G.S c x) N _).mp
        (hc (hmem c)) k hk
      rw [contact_time_derivative] at h
      have ht : extensionChartCoordinates G.S c x 0 = x := by
        fin_cases c <;> simp [extensionChartCoordinates]
      change MvPolynomial.aeval (extensionChartCoordinates G.S c x)
        (Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
          (Polynomial.derivative^[k] (p c))) = 0 at h
      rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X, ht] at h
      exact h
    apply (contact_root_power_iff_jets x _ N).mp
    exact dvd_trans ((contact_root_power_iff_jets x (p c) N).mpr hjets)
      (Finset.dvd_prod_of_mem p (Finset.mem_univ c))
