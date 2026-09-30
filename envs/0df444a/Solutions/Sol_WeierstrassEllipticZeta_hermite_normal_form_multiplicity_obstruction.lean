-- Prove2me | solution 1 for WeierstrassEllipticZeta.hermite_normal_form_multiplicity_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T22:41:24.882788+00:00
-- url     : https://prove2.me/submissions/3cef0ece-6f36-490e-9496-fcd6e70e9135
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_time_normal_form_triangular_generators
import Theorems.Thm_WeierstrassEllipticZeta_triangular_contact_multiplicity_obstruction
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveContactIdeal
import Mathlib.RingTheory.Ideal.IsPrimary
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartNormalization
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartCalculus
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionChartLocus
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionLocus
import Mathlib.LinearAlgebra.Projectivization.Basic
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Mathlib.Analysis.Analytic.Order
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Set.Card

open WeierstrassEllipticZeta
open scoped Pointwise
open TranscendenceTheory

open scoped Classical

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω)
    (P : GraphQuotientExtension L.lattice η ≃ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (hP : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (P ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)
    (F : ProjectiveExtensionFiberModel L.g₂ L.g₃)
    (hP_action : ∀ (u : ℂ) (e : GraphQuotientExtension L.lattice η),
      P (e + extensionInclusion L.lattice η u) = F.action u (P e))
    (hflow :
    (∀ z : ℂ, S 0 z ≠ 0 →
      HasDerivAt (fun w => S 1 w / S 0 w) (S 2 z / S 0 z) z ∧
      HasDerivAt (fun w => S 2 w / S 0 w) (6 * (S 1 z / S 0 z) ^ 2 - L.g₂ / 2) z ∧
      HasDerivAt (fun w => S 3 w / S 0 w) (-S 1 z / S 0 z) z) ∧
    (∀ z : ℂ, S 2 z ≠ 0 →
      HasDerivAt (fun w => S 0 w / S 2 w)
        (-6 * (S 1 z / S 2 z) ^ 2 + L.g₂ / 2 * (S 0 z / S 2 z) ^ 2) z ∧
      HasDerivAt (fun w => S 1 w / S 2 w)
        (-(1 / 2 : ℂ) - L.g₂ * (S 0 z / S 2 z) * (S 1 z / S 2 z) -
          3 * L.g₃ / 2 * (S 0 z / S 2 z) ^ 2) z ∧
      HasDerivAt (fun w => S 4 w / S 2 w)
        (-2 * L.g₂ * (S 1 z / S 2 z) ^ 2 -
          3 * L.g₃ * (S 0 z / S 2 z) * (S 1 z / S 2 z)) z))
    (hjets :
    (∀ c : Fin 2, extensionChartDerivation L.g₂ L.g₃ c (extensionChartCubic L.g₂ L.g₃ c) = 0) ∧
    ∀ (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ) (n : ℕ),
      ((extensionChartDerivation L.g₂ L.g₃ c)^[n] p).totalDegree ≤ p.totalDegree + n ∧
      ∀ z : ℂ, S (extensionChartDenominator c) z ≠ 0 →
        iteratedDeriv n (fun w => MvPolynomial.eval (extensionChartCoordinates S c w) p) z =
          MvPolynomial.eval (extensionChartCoordinates S c z)
            ((extensionChartDerivation L.g₂ L.g₃ c)^[n] p) ∧
        ((n : ℕ∞) ≤ analyticOrderAt
            (fun w => MvPolynomial.eval (extensionChartCoordinates S c w) p) z ↔
          ∀ k < n, MvPolynomial.eval (extensionChartCoordinates S c z)
            ((extensionChartDerivation L.g₂ L.g₃ c)^[k] p) = 0))
    (B : ℕ → ℕ)
    (hB : Monotone B ∧ (∀ d : ℕ, 0 < B d) ∧
      ∀ (d : ℕ) (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ), p.totalDegree ≤ d →
        ∀ v : Fin 4 → ℂ,
          ((∀ k < B d, MvPolynomial.eval v ((extensionChartDerivation L.g₂ L.g₃ c)^[k] p) = 0) ↔
            ∀ k : ℕ, MvPolynomial.eval v ((extensionChartDerivation L.g₂ L.g₃ c)^[k] p) = 0))
    (hcontact :
    (∀ (c : Fin 2) (v : Fin 4 → ℂ) (n : ℕ) (p : MvPolynomial (Fin 4) ℂ),
      p ∈ extensionChartContactIdeal L.g₂ L.g₃ c v n ↔
        ∀ k < n, MvPolynomial.eval v ((extensionChartDerivation L.g₂ L.g₃ c)^[k] p) = 0) ∧
    (∀ (c : Fin 2) (v : Fin 4 → ℂ) (m n : ℕ),
      extensionChartContactIdeal L.g₂ L.g₃ c v m * extensionChartContactIdeal L.g₂ L.g₃ c v n ≤
        extensionChartContactIdeal L.g₂ L.g₃ c v (m + n)) ∧
    (∀ (c : Fin 2) (v : Fin 4 → ℂ) (n : ℕ),
      RingHom.ker (MvPolynomial.eval v) ^ n ≤ extensionChartContactIdeal L.g₂ L.g₃ c v n) ∧
    (∀ (c : Fin 2) (v : Fin 4 → ℂ) (n : ℕ), 0 < n →
      (extensionChartContactIdeal L.g₂ L.g₃ c v n).radical = RingHom.ker (MvPolynomial.eval v) ∧
        (extensionChartContactIdeal L.g₂ L.g₃ c v n).IsPrimary) ∧
    (∀ (c : Fin 2) (v w : Fin 4 → ℂ), v ≠ w → ∀ m n : ℕ,
      extensionChartContactIdeal L.g₂ L.g₃ c v m ⊔ extensionChartContactIdeal L.g₂ L.g₃ c w n = ⊤) ∧
    (∀ (c : Fin 2) (v : Fin 4 → ℂ) (n : ℕ) (p : MvPolynomial (Fin 4) ℂ),
      p ∈ extensionChartContactIdeal L.g₂ L.g₃ c v (n + 1) →
        extensionChartDerivation L.g₂ L.g₃ c p ∈ extensionChartContactIdeal L.g₂ L.g₃ c v n) ∧
    (∀ (c : Fin 2) (V : Finset (Fin 4 → ℂ)) (n : V → ℕ)
        (p : V → MvPolynomial (Fin 4) ℂ),
      ∃ q : MvPolynomial (Fin 4) ℂ, ∀ v : V,
        q - p v ∈ extensionChartContactIdeal L.g₂ L.g₃ c v.val (n v))) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n U : ℕ,
      1 ≤ m → 1 ≤ n → 1 ≤ U → ∀ X : Finset ℂ,
      0 ∈ X → ∀ Q : MvPolynomial (Fin 7) ℂ,
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧
          d 2 + d 3 + d 4 + d 5 + d 6 = n) →
        (∀ (c : Fin 2) (z : ℂ), S (extensionChartDenominator c) z ≠ 0 →
          extensionChartNormalize c Q ∉ extensionChartContactIdeal L.g₂ L.g₃ c
            (extensionChartCoordinates S c z) (B (m + 2 * n))) →
        (∀ (c : Fin 2) (k : ℕ),
          ((extensionChartDerivation L.g₂ L.g₃ c)^[k] (extensionChartNormalize c Q)).totalDegree ≤
            m + 2 * n + k) →
        (∀ c : Fin 2,
          let Z := (X + X + X).filter (fun z => S (extensionChartDenominator c) z ≠ 0)
          let V := Z.image (extensionChartCoordinates S c)
          let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
            ⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (3 * U + 1)
          extensionChartNormalize c Q ∈ I ∧
            FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) ∧
            Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) = (3 * U + 1) * Z.card ∧
            ∀ p : MvPolynomial (Fin 4) ℂ, ∃! q : Polynomial ℂ,
              q.degree < ((3 * U + 1) * Z.card : ℕ) ∧
              p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) q ∈ I) →
        ∃ H : Submodule ℤ (GraphExtensionGroup L.lattice η), ∃ a b : ℕ,
          ((a = 1 ∧ H ≤ LinearMap.ker (extensionAdditiveProjection L.lattice η)) ∨
            (a = 0 ∧ H ≤ LinearMap.ker (extensionEllipticProjection L.lattice η))) ∧
          b ≤ 2 ∧
          ((U + 1 : ℕ) : ℝ) *
            (H.mkQ '' (extensionCurve L.lattice η '' (X : Set ℂ))).ncard ≤
            C * (m : ℝ) ^ a * (n : ℝ) ^ b := by
  classical
  obtain ⟨C, hC, hbound⟩ := triangular_contact_multiplicity_obstruction
    L D S hS hS_value hS_ne η hη P hP F hP_action hflow hjets B hB hcontact
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hnonzero hdegree hvanish
  apply hbound m n U hm hn hU X hX Q hQ hnonzero hdegree _
  intro c
  let Z := (X + X + X).filter (fun z => S (extensionChartDenominator c) z ≠ 0)
  let V := Z.image (extensionChartCoordinates S c)
  let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (3 * U + 1)
  let M : Polynomial ℂ :=
    ∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ (3 * U + 1)
  have hinj : Function.Injective (extensionChartCoordinates S c) := by
    intro z w h
    have h0 := congrFun h (0 : Fin 4)
    by_cases hc : c = 0 <;> simpa [extensionChartCoordinates, hc] using h0
  have hcard : V.card = Z.card := Finset.card_image_of_injective _ hinj
  have hmonic : M.Monic := Polynomial.monic_prod_of_monic _ _ fun v _ =>
    (Polynomial.monic_X_sub_C (v.val 0)).pow (3 * U + 1)
  have hdeg : M.degree = ((3 * U + 1) * Z.card : ℕ) := by
    simp [M, Polynomial.degree_prod, Polynomial.degree_pow, hcard, Nat.mul_comm]
    simp only [add_mul, one_mul, mul_comm]
  have hMI : Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) M ∈ I := by
    rw [Ideal.mem_iInf]
    intro v
    have hker : MvPolynomial.X (0 : Fin 4) - MvPolynomial.C (v.val 0) ∈
        RingHom.ker (MvPolynomial.eval v.val) := by
      simp
    have hpow := hcontact.2.2.1 c v.val (3 * U + 1) (Ideal.pow_mem_pow hker (3 * U + 1))
    have hfactor : (MvPolynomial.X (0 : Fin 4) - MvPolynomial.C (v.val 0)) ^ (3 * U + 1) ∣
        Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) M := by
      dsimp [M]
      simp only [map_prod, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ v)
    exact Ideal.mem_of_dvd _ hfactor hpow
  have hold := hvanish c
  refine ⟨hold.1, hold.2.1, hold.2.2.1, hmonic, hdeg, ?_⟩
  exact time_normal_form_triangular_generators I ((3 * U + 1) * Z.card) M
    hmonic hdeg hMI hold.2.2.2
