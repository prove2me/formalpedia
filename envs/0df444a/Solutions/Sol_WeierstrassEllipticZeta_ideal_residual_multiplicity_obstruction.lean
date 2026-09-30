-- Prove2me | solution 1 for WeierstrassEllipticZeta.ideal_residual_multiplicity_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T13:29:02.244508+00:00
-- url     : https://prove2.me/submissions/e34149a3-4f2b-4d99-a5ca-813fd7f13f93
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_finite_contact_ideal_colon
import Theorems.Thm_WeierstrassEllipticZeta_complementary_intersection_multiplicity_obstruction
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.AdjoinRoot
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
            (∃ a : Fin (B (m + 2 * n)) → MvPolynomial (Fin 4) ℂ,
              1 - ∑ k : Fin (B (m + 2 * n)), a k *
                ((extensionChartDerivation L.g₂ L.g₃ c)^[k.val] (extensionChartNormalize c Q)) ∈ I ∧
              I ⊔ Ideal.span (Set.range (fun k : Fin (B (m + 2 * n)) =>
                (extensionChartDerivation L.g₂ L.g₃ c)^[k.val] (extensionChartNormalize c Q))) = ⊤) ∧
            FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) ∧
            Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) = (3 * U + 1) * Z.card ∧
            let M : Polynomial ℂ :=
              ∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ (3 * U + 1)
            M.Monic ∧ M.degree = ((3 * U + 1) * Z.card : ℕ) ∧
            ∃ r : Fin 3 → Polynomial ℂ,
              (∀ i, (r i).degree < ((3 * U + 1) * Z.card : ℕ)) ∧
              I = Ideal.span (insert (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) M)
                (Set.range (fun i : Fin 3 => MvPolynomial.X i.succ -
                  Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (r i)))) ∧
              (∀ p : MvPolynomial (Fin 4) ℂ,
                p ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) p) ∧
              (∃ t : V → ℕ,
                (∀ v : V, 3 * U + 1 ≤ t v ∧ t v < B (m + 2 * n) ∧
                  MvPolynomial.eval v.val
                    ((extensionChartDerivation L.g₂ L.g₃ c)^[t v] (extensionChartNormalize c Q)) ≠ 0 ∧
                  ∀ j < t v, MvPolynomial.eval v.val
                    ((extensionChartDerivation L.g₂ L.g₃ c)^[j] (extensionChartNormalize c Q)) = 0) ∧
                ∀ s : ℕ, 0 < s →
                  let J := I ⊔ Ideal.span (Set.range (fun i : Fin s =>
                    (extensionChartDerivation L.g₂ L.g₃ c)^[i.val] (extensionChartNormalize c Q)))
                  FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
                  Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) =
                    ∑ v : V, min (3 * U + 1) (t v + 1 - s) ∧
                  (J = ⊤ ↔ ∀ v : V, t v < s) ∧
                  (B (m + 2 * n) ≤ s → J = ⊤)) ∧
              (∀ s : ℕ,
                let J := I ⊔ Ideal.span (Set.range (fun i : Fin s =>
                  (extensionChartDerivation L.g₂ L.g₃ c)^[i.val] (extensionChartNormalize c Q)))
                (let R := I.colon (J : Set (MvPolynomial (Fin 4) ℂ))
                 I ≤ R ∧
                 I.colon (R : Set (MvPolynomial (Fin 4) ℂ)) = J ∧
                 FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) ∧
                 Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) +
                   Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = M.natDegree ∧
                 (∀ K : Ideal (MvPolynomial (Fin 4) ℂ), I ≤ K →
                   (J ≤ K ↔ I.colon (K : Set (MvPolynomial (Fin 4) ℂ)) ≤ R))) ∧
                (∃ g : Polynomial ℂ,
                  g.Monic ∧ g ∣ M ∧ g.natDegree ≤ M.natDegree ∧
                  J = I ⊔ Ideal.span {Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g} ∧
                  (∀ f : MvPolynomial (Fin 4) ℂ,
                    f ∈ J ↔ g ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
                  Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = g.natDegree ∧
                  (∀ h : Polynomial ℂ, h.Monic →
                    (∀ f : MvPolynomial (Fin 4) ℂ,
                      f ∈ J ↔ h ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) → h = g)) ∧
                FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
                ∃ e : V → ℕ,
                  (∀ v : V, e v ≤ 3 * U + 1 ∧ ∀ k ≤ 3 * U + 1,
                    k ≤ e v ↔ ∀ i : Fin s, ∀ j < k,
                      MvPolynomial.eval v.val
                        ((extensionChartDerivation L.g₂ L.g₃ c)^[j + i.val]
                          (extensionChartNormalize c Q)) = 0) ∧
                  J = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e v)) ∧
                  Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ J) ≃ₐ[ℂ]
                    ((v : V) → Polynomial ℂ ⧸
                      Ideal.span {(Polynomial.X - Polynomial.C (v.val 0)) ^ e v})) ∧
                  J.radical = (⨅ v : V, if e v = 0 then ⊤ else RingHom.ker (MvPolynomial.eval v.val)) ∧
                  (∀ P' : Ideal (MvPolynomial (Fin 4) ℂ), P'.IsPrime →
                    (J ≤ P' ↔ ∃! v : V, 0 < e v ∧ P' = RingHom.ker (MvPolynomial.eval v.val))) ∧
                  Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = ∑ v : V, e v ∧
                  (∀ p : MvPolynomial (Fin 4) ℂ,
                    let K := J.colon {p ^ (3 * U + 1)}
                    let e' : V → ℕ := fun v => if MvPolynomial.eval v.val p = 0 then 0 else e v
                    K = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e' v)) ∧
                    (∀ q : MvPolynomial (Fin 4) ℂ, (∃ r : ℕ, q * p ^ r ∈ J) ↔ q ∈ K) ∧
                    FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
                    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = ∑ v : V, e' v)) ∧
              (∃ b : Fin (B (m + 2 * n)) → Polynomial ℂ,
                (∀ k : Fin (B (m + 2 * n)),
                  (b k).degree < ((3 * U + 1) * Z.card : ℕ) ∧
                  (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) (b k)).totalDegree ≤
                    (3 * U + 1) * Z.card - 1) ∧
                (1 - ∑ k : Fin (B (m + 2 * n)),
                  Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b k) *
                    ((extensionChartDerivation L.g₂ L.g₃ c)^[k.val] (extensionChartNormalize c Q))) ∈ I ∧
                (1 - ∑ k : Fin (B (m + 2 * n)),
                  Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b k) *
                    ((extensionChartDerivation L.g₂ L.g₃ c)^[k.val] (extensionChartNormalize c Q))).totalDegree ≤
                  ((3 * U + 1) * Z.card - 1) + (m + 2 * n + (B (m + 2 * n) - 1))) ∧
              ∀ p : MvPolynomial (Fin 4) ℂ,
                let q := MvPolynomial.aeval (Fin.cons Polynomial.X r) p
                let J := I ⊔ Ideal.span {p}
                Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ J) ≃ₐ[ℂ]
                  (Polynomial ℂ ⧸ Ideal.span {gcd M q})) ∧
                FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
                Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = (gcd M q).natDegree ∧
                Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ≤ M.natDegree ∧
                (q ≠ 0 → Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ≤ q.natDegree) ∧
                (let R := I.colon {p}
                 let G := M / gcd M q
                 (∀ f : MvPolynomial (Fin 4) ℂ,
                   f ∈ R ↔ G ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
                 Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ R) ≃ₐ[ℂ]
                   (Polynomial ℂ ⧸ Ideal.span {G})) ∧
                 FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) ∧
                 Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) = G.natDegree ∧
                 Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) +
                   Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = M.natDegree ∧
                 I.colon (R : Set (MvPolynomial (Fin 4) ℂ)) = J ∧
                 I.colon (J : Set (MvPolynomial (Fin 4) ℂ)) = R) ∧
                ∃ e : V → ℕ,
                  (∀ v : V, e v ≤ 3 * U + 1 ∧ ∀ k ≤ 3 * U + 1,
                    k ≤ e v ↔ ∀ j < k,
                      MvPolynomial.eval v.val
                        ((extensionChartDerivation L.g₂ L.g₃ c)^[j] p) = 0) ∧
                  Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = ∑ v : V, e v ∧
                  I.colon {p} =
                    (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (3 * U + 1 - e v)) ∧
                  Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I.colon {p}) =
                    ∑ v : V, (3 * U + 1 - e v)) →
        ∃ H : Submodule ℤ (GraphExtensionGroup L.lattice η), ∃ a b : ℕ,
          ((a = 1 ∧ H ≤ LinearMap.ker (extensionAdditiveProjection L.lattice η)) ∨
            (a = 0 ∧ H ≤ LinearMap.ker (extensionEllipticProjection L.lattice η))) ∧
          b ≤ 2 ∧
          ((U + 1 : ℕ) : ℝ) *
            (H.mkQ '' (extensionCurve L.lattice η '' (X : Set ℂ))).ncard ≤
            C * (m : ℝ) ^ a * (n : ℝ) ^ b := by
  classical
  obtain ⟨C, hC, hbound⟩ := complementary_intersection_multiplicity_obstruction
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
  obtain ⟨hQmem, hbezout, hfinite, hlength, hmonic, hdeg, r, hr,
    hgenerators, hmem, hprofile, hprefix, hbounded, hinter⟩ := hvanish c
  refine ⟨hQmem, hbezout, hfinite, hlength, hmonic, hdeg,
    r, hr, hgenerators, hmem, hprofile, ?_, hbounded, hinter⟩
  intro s
  let J := I ⊔ Ideal.span (Set.range (fun i : Fin s =>
    (extensionChartDerivation L.g₂ L.g₃ c)^[i.val] (extensionChartNormalize c Q)))
  obtain ⟨hres, hcanonical, hfiniteJ, e, he, hJeq, halg, hrad, hprime, hlenJ, hsat⟩ := hprefix s
  change J = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e v)) at hJeq
  obtain ⟨hcolon, _, hcolonlen⟩ := finite_contact_ideal_colon L.g₂ L.g₃ c V
    (fun _ => 3 * U + 1) e (fun v => (he v).1)
  refine ⟨hres, hcanonical, hfiniteJ, e, he, hJeq, halg, hrad, hprime, hlenJ, ?_, ?_, hsat⟩
  · change I.colon (J : Set (MvPolynomial (Fin 4) ℂ)) = _
    rw [hJeq]
    exact hcolon
  · change Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸
      I.colon (J : Set (MvPolynomial (Fin 4) ℂ))) = _
    rw [hJeq]
    exact hcolonlen
