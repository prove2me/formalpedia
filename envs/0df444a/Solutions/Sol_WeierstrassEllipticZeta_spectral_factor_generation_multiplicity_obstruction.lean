-- Prove2me | solution 1 for WeierstrassEllipticZeta.spectral_factor_generation_multiplicity_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-11T19:56:45.299993+00:00
-- url     : https://prove2.me/submissions/024a5db5-8935-4546-ac22-3523b104920d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_commutative_weighted_surjectivity_iff
import Theorems.Thm_WeierstrassEllipticZeta_spectral_factor_cyclic_vector_multiplicity_obstruction
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
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

set_option maxHeartbeats 800000

set_option maxHeartbeats 6400000 in
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
                (0 < s → J = ⊤ → ∃ a : ℕ, a ≤ V.card * (s - 1) ∧
                  let q := ∑ j : Fin s, MvPolynomial.C ((a : ℂ) ^ j.val) *
                    ((extensionChartDerivation L.g₂ L.g₃ c)^[j.val] (extensionChartNormalize c Q))
                  (∀ v : V, MvPolynomial.eval v.val q ≠ 0) ∧
                  q.totalDegree ≤ m + 2 * n + (s - 1) ∧
                  ∃ b : Polynomial ℂ,
                    b.degree < (M.natDegree : ℕ) ∧
                    (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) b).totalDegree ≤
                      M.natDegree - 1 ∧
                    1 - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b * q ∈ I ∧
                    (1 - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b * q).totalDegree ≤
                      M.natDegree - 1 + q.totalDegree ∧
                    (∀ b' : Polynomial ℂ, b'.degree < (M.natDegree : ℕ) →
                      1 - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b' * q ∈ I → b' = b) ∧
                    (∀ f : MvPolynomial (Fin 4) ℂ, f * q ∈ I ↔ f ∈ I) ∧
                    I ⊔ Ideal.span {q} = ⊤ ∧
                    ∃ T : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ,
                      (∀ p : MvPolynomial (Fin 4) ℂ,
                        T p = (MvPolynomial.aeval (Fin.cons Polynomial.X r)
                          (p * Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b)) %ₘ M ∧
                        (T p).degree < (M.natDegree : ℕ) ∧
                        (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) (T p)).totalDegree ≤
                          M.natDegree - 1 ∧
                        p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (T p) * q ∈ I ∧
                        (p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (T p) * q).totalDegree ≤
                          max p.totalDegree (M.natDegree - 1 + q.totalDegree) ∧
                        (∀ b' : Polynomial ℂ, b'.degree < (M.natDegree : ℕ) →
                          (p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b' * q ∈ I ↔ b' = T p))) ∧
                      (∀ p : MvPolynomial (Fin 4) ℂ, T p = 0 ↔ p ∈ I) ∧
                      (∀ T' : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ,
                        (∀ p : MvPolynomial (Fin 4) ℂ, (T' p).degree < (M.natDegree : ℕ) ∧
                          p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (T' p) * q ∈ I) → T' = T) ∧
                      ∃ β : Module.Basis (Fin M.natDegree) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I),
                        (∀ i : Fin M.natDegree,
                          β i = Ideal.Quotient.mk I ((MvPolynomial.X (0 : Fin 4)) ^ i.val * q) ∧
                          ((MvPolynomial.X (0 : Fin 4)) ^ i.val * q).totalDegree ≤
                            M.natDegree - 1 + q.totalDegree) ∧
                        (∀ (p : MvPolynomial (Fin 4) ℂ) (i : Fin M.natDegree),
                          β.repr (Ideal.Quotient.mk I p) i = (T p).coeff i.val) ∧
                        (∀ p : MvPolynomial (Fin 4) ℂ,
                          Ideal.Quotient.mk I p = ∑ i : Fin M.natDegree,
                            (T p).coeff i.val • Ideal.Quotient.mk I
                              ((MvPolynomial.X (0 : Fin 4)) ^ i.val * q)) ∧
                        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) = M.natDegree ∧
                        ∃ ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ]
                            Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ,
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            ρ p = Algebra.leftMulMatrix β (Ideal.Quotient.mk I p)) ∧
                          (∀ (p : MvPolynomial (Fin 4) ℂ) (i j : Fin M.natDegree),
                            ρ p i j = ((MvPolynomial.aeval (Fin.cons Polynomial.X r) p *
                              Polynomial.X ^ j.val) %ₘ M).coeff i.val) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ, ρ p = 0 ↔ p ∈ I) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            ρ p = Polynomial.aeval (ρ (MvPolynomial.X (0 : Fin 4)))
                              (MvPolynomial.aeval (Fin.cons Polynomial.X r) p)) ∧
                          (ρ (MvPolynomial.X (0 : Fin 4))).charpoly = M ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            (ρ p).det = ∏ v : V,
                              (MvPolynomial.eval v.val p) ^ (3 * U + 1)) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            IsUnit (ρ p) ↔ ∀ v : V, 0 < 3 * U + 1 →
                              MvPolynomial.eval v.val p ≠ 0) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            (ρ p).charpoly = ∏ v : V,
                              (Polynomial.X - Polynomial.C (MvPolynomial.eval v.val p)) ^
                                (3 * U + 1)) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            (ρ p).trace = ∑ v : V,
                              ((3 * U + 1 : ℕ) : ℂ) * MvPolynomial.eval v.val p) ∧
                          (∀ (p : MvPolynomial (Fin 4) ℂ) (z : ℂ),
                            z ∈ spectrum ℂ (ρ p) ↔ ∃ v : V,
                              0 < 3 * U + 1 ∧ z = MvPolynomial.eval v.val p) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            IsNilpotent (ρ p) ↔ ∀ v : V, 0 < 3 * U + 1 →
                              MvPolynomial.eval v.val p = 0) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            (∀ v : V, 0 < 3 * U + 1 → MvPolynomial.eval v.val p = 0) →
                              (ρ p) ^ M.natDegree = 0) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ I.colon {p}) ≃ₗ[ℂ]
                              LinearMap.range (ρ p).mulVecLin) ∧
                            (ρ p).rank = Module.finrank ℂ
                              (MvPolynomial (Fin 4) ℂ ⧸ I.colon {p}) ∧
                            Module.finrank ℂ (LinearMap.ker (ρ p).mulVecLin) =
                              Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸
                                (I ⊔ Ideal.span {p})) ∧
                            (ρ p).rank + Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸
                              (I ⊔ Ideal.span {p})) = M.natDegree) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            IsCompl (LinearMap.ker ((ρ p) ^ M.natDegree).mulVecLin)
                              (LinearMap.range ((ρ p) ^ M.natDegree).mulVecLin) ∧
                            Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₗ[ℂ]
                              (LinearMap.ker ((ρ p) ^ M.natDegree).mulVecLin) ×
                                (LinearMap.range ((ρ p) ^ M.natDegree).mulVecLin)) ∧
                            ∀ N : ℕ, M.natDegree ≤ N →
                              LinearMap.ker ((ρ p) ^ N).mulVecLin =
                                LinearMap.ker ((ρ p) ^ M.natDegree).mulVecLin ∧
                              LinearMap.range ((ρ p) ^ N).mulVecLin =
                                LinearMap.range ((ρ p) ^ M.natDegree).mulVecLin ∧
                              I.colon {p ^ N} = I.colon {p ^ M.natDegree}) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            let K := I ⊔ Ideal.span {p ^ M.natDegree}
                            let R := I.colon {p ^ M.natDegree}
                            K ⊔ R = ⊤ ∧ K ⊓ R = I ∧ K * R = I ∧
                            Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₐ[ℂ]
                              (MvPolynomial (Fin 4) ℂ ⧸ K) ×
                                (MvPolynomial (Fin 4) ℂ ⧸ R)) ∧
                            (Ideal.Quotient.mk K p) ^ M.natDegree = 0 ∧
                            IsUnit (Ideal.Quotient.mk R p) ∧
                            ∃ e : MvPolynomial (Fin 4) ℂ,
                              e ∈ K ∧ 1 - e ∈ R ∧ e * e - e ∈ I ∧
                              K = I ⊔ Ideal.span {e} ∧ R = I ⊔ Ideal.span {1 - e}) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            ∃! b : MvPolynomial (Fin 4) ℂ ⧸ I,
                              Ideal.Quotient.mk I p * b * b = b ∧
                              (Ideal.Quotient.mk I p) ^ (M.natDegree + 1) * b =
                                (Ideal.Quotient.mk I p) ^ M.natDegree ∧
                              (let a := Ideal.Quotient.mk I p
                               let f := Algebra.lmul ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) a
                               let E := Algebra.lmul ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) (a * b)
                               IsIdempotentElem (a * b) ∧ IsIdempotentElem E ∧
                                 LinearMap.ker E = LinearMap.ker (f ^ M.natDegree) ∧
                                 LinearMap.range E = LinearMap.range (f ^ M.natDegree) ∧
                                 ∃ h : IsCompl (LinearMap.range (f ^ M.natDegree))
                                     (LinearMap.ker (f ^ M.natDegree)),
                                   E = (LinearMap.range (f ^ M.natDegree)).projection
                                     (LinearMap.ker (f ^ M.natDegree)) h)) ∧
                          (∃! G : MvPolynomial (Fin 4) ℂ →*₀
                              (MvPolynomial (Fin 4) ℂ ⧸ I),
                            ∀ p : MvPolynomial (Fin 4) ℂ,
                              Ideal.Quotient.mk I p * G p * G p = G p ∧
                              (Ideal.Quotient.mk I p) ^ (M.natDegree + 1) * G p =
                                (Ideal.Quotient.mk I p) ^ M.natDegree ∧
                              (G p = 0 ↔ p ∈ I.radical) ∧
                              (IsUnit (Ideal.Quotient.mk I p) ↔
                                Ideal.Quotient.mk I p * G p = 1) ∧
                              ∀ r : MvPolynomial (Fin 4) ℂ,
                                Ideal.Quotient.mk I r = G p →
                                  (∀ v : V,
                                    MvPolynomial.eval v.val r = (MvPolynomial.eval v.val p)⁻¹ ∧
                                    MvPolynomial.eval v.val (p * r) =
                                      if MvPolynomial.eval v.val p = 0 then 0 else 1) ∧
                                  (ρ (p * r)).rank = (3 * U + 1) *
                                    (Finset.univ.filter (fun v : V =>
                                      MvPolynomial.eval v.val p ≠ 0)).card ∧
                                  Module.finrank ℂ (LinearMap.ker (ρ (p * r)).mulVecLin) =
                                    M.natDegree - (3 * U + 1) *
                                      (Finset.univ.filter (fun v : V =>
                                        MvPolynomial.eval v.val p ≠ 0)).card) ∧
                          (∀ (p : MvPolynomial (Fin 4) ℂ) (N : ℕ), M.natDegree ≤ N →
                            ((ρ p) ^ N).rank = (3 * U + 1) *
                              (Finset.univ.filter (fun v : V =>
                                MvPolynomial.eval v.val p ≠ 0)).card ∧
                            Module.finrank ℂ (LinearMap.ker ((ρ p) ^ N).mulVecLin) =
                              M.natDegree - (3 * U + 1) *
                                (Finset.univ.filter (fun v : V =>
                                  MvPolynomial.eval v.val p ≠ 0)).card) ∧
                          (∀ (p : MvPolynomial (Fin 4) ℂ) (z : ℂ),
                            Module.finrank ℂ
                              (Module.End.maxGenEigenspace (ρ p).mulVecLin z) =
                                (3 * U + 1) * (Finset.univ.filter (fun v : V =>
                                  MvPolynomial.eval v.val p = z)).card ∧
                            ∀ N : ℕ, M.natDegree ≤ N →
                              Module.finrank ℂ
                                (Module.End.genEigenspace (ρ p).mulVecLin z N) =
                                  (3 * U + 1) * (Finset.univ.filter (fun v : V =>
                                    MvPolynomial.eval v.val p = z)).card) ∧
                          (∀ p : MvPolynomial (Fin 4) ℂ,
                            let W := Finset.univ.image (fun v : V => MvPolynomial.eval v.val p)
                            DirectSum.IsInternal (fun z : W =>
                              Module.End.maxGenEigenspace (ρ p).mulVecLin z.val) ∧
                            ∃ e : (∀ z : W,
                                Module.End.maxGenEigenspace (ρ p).mulVecLin z.val) ≃ₗ[ℂ]
                                  (Fin M.natDegree → ℂ),
                              (∀ x, e x = ∑ z : W, (x z : Fin M.natDegree → ℂ)) ∧
                              ∃ Pr : W → Module.End ℂ (Fin M.natDegree → ℂ),
                                (∀ z x, Pr z x = (e.symm x z : Fin M.natDegree → ℂ)) ∧
                                (∀ z, IsIdempotentElem (Pr z)) ∧
                                (∀ z w, z ≠ w → Pr z * Pr w = 0) ∧
                                (∑ z, Pr z) = 1 ∧
                                (∀ z, LinearMap.range (Pr z) =
                                  Module.End.maxGenEigenspace (ρ p).mulVecLin z.val) ∧
                                (∀ (q : MvPolynomial (Fin 4) ℂ) (z : W),
                                  Commute (Pr z) (ρ q).mulVecLin) ∧
                                ∃ ε : W → MvPolynomial (Fin 4) ℂ ⧸ I,
                                  (∀ z, (Algebra.leftMulMatrix β (ε z)).mulVecLin = Pr z) ∧
                                  (∀ z, ε z = β.equivFun.symm (Pr z (β.equivFun 1))) ∧
                                  (∀ z, IsIdempotentElem (ε z)) ∧
                                  (∀ z w, z ≠ w → ε z * ε w = 0) ∧
                                  (∑ z, ε z) = 1 ∧
                                  (∀ z (a : MvPolynomial (Fin 4) ℂ ⧸ I),
                                    a ∈ Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)) ↔ ε z * a = 0) ∧
                                  ∃ Φ : (MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₐ[ℂ]
                                      (∀ z : W, (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
                                        Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))),
                                    (∀ a z, Φ a z =
                                      Ideal.Quotient.mk (Ideal.span {1 - ε z}) a) ∧
                                    (∀ z w, Φ (ε w) z = if z = w then 1 else 0) ∧
                                    ∀ z : W, ∃ ψ : ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
                                          Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))) ≃ₗ[ℂ]
                                        Module.End.maxGenEigenspace (ρ p).mulVecLin z.val,
                                      (∀ a : MvPolynomial (Fin 4) ℂ ⧸ I,
                                        (ψ (Ideal.Quotient.mk (Ideal.span {1 - ε z}) a) : Fin M.natDegree → ℂ) =
                                          β.equivFun (ε z * a)) ∧
                                      Module.finrank ℂ
                                        ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
                                          Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))) =
                                        (3 * U + 1) * (Finset.univ.filter (fun v : V =>
                                          MvPolynomial.eval v.val p = z.val)).card ∧
                                      (Ideal.Quotient.mk
                                        (Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))
                                        (Ideal.Quotient.mk I (p - MvPolynomial.C z.val))) ^
                                          M.natDegree = 0 ∧
                                      (∀ N : ℕ, (3 * U + 1) *
                                        (Finset.univ.filter (fun v : V =>
                                          MvPolynomial.eval v.val p = z.val)).card ≤ N →
                                        (Ideal.Quotient.mk
                                          (Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))
                                          (Ideal.Quotient.mk I (p - MvPolynomial.C z.val))) ^ N = 0) ∧
                                      (∀ w : ℂ, w ≠ z.val →
                                        let π := (Ideal.Quotient.mk
                                          (Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))).comp
                                            (Ideal.Quotient.mk I)
                                        let d := (3 * U + 1) *
                                          (Finset.univ.filter (fun v : V =>
                                            MvPolynomial.eval v.val p = z.val)).card
                                        let b := π (MvPolynomial.C ((z.val - w)⁻¹)) *
                                          ∑ k ∈ Finset.range d,
                                            (-(π (MvPolynomial.C ((z.val - w)⁻¹)) *
                                              π (p - MvPolynomial.C z.val))) ^ k
                                        π (p - MvPolynomial.C w) * b = 1 ∧
                                          b * π (p - MvPolynomial.C w) = 1 ∧
                                          IsUnit (π (p - MvPolynomial.C w))) ∧
                                      (∀ q : Polynomial ℂ,
                                        let π := (Ideal.Quotient.mk
                                          (Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))).comp
                                            (Ideal.Quotient.mk I)
                                        let d := (3 * U + 1) *
                                          (Finset.univ.filter (fun v : V =>
                                            MvPolynomial.eval v.val p = z.val)).card
                                        (q.eval₂ (π.comp MvPolynomial.C) (π p) -
                                          π (MvPolynomial.C (q.eval z.val))) ^ d = 0 ∧
                                        (IsUnit (q.eval₂ (π.comp MvPolynomial.C) (π p)) ↔
                                          q.eval z.val ≠ 0) ∧
                                        (IsNilpotent (q.eval₂ (π.comp MvPolynomial.C) (π p)) ↔
                                          q.eval z.val = 0) ∧
                                        (q ≠ 0 →
                                          ∃ u : ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
                                            Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))ˣ,
                                            q.eval₂ (π.comp MvPolynomial.C) (π p) =
                                              (π p - π (MvPolynomial.C z.val)) ^ q.rootMultiplicity z.val * ↑u ∧
                                            (∀ k : ℕ,
                                              (q.eval₂ (π.comp MvPolynomial.C) (π p)) ^ k = 0 ↔
                                                (π p - π (MvPolynomial.C z.val)) ^
                                                  (q.rootMultiplicity z.val * k) = 0) ∧
                                            ∀ k : ℕ, d ≤ q.rootMultiplicity z.val * k →
                                              (q.eval₂ (π.comp MvPolynomial.C) (π p)) ^ k = 0)) ∧
                                      let π := (Ideal.Quotient.mk
                                        (Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))).comp
                                          (Ideal.Quotient.mk I)
                                      let d := (3 * U + 1) *
                                        (Finset.univ.filter (fun v : V =>
                                          MvPolynomial.eval v.val p = z.val)).card
                                      let n := nilpotencyClass (π p - π (MvPolynomial.C z.val))
                                      n ≤ d ∧
                                        (∀ q : Polynomial ℂ,
                                          q.eval₂ (π.comp MvPolynomial.C) (π p) = 0 ↔
                                            (Polynomial.X - Polynomial.C z.val) ^ n ∣ q) ∧
                                        RingHom.ker (Polynomial.eval₂RingHom (π.comp MvPolynomial.C) (π p)) =
                                          Ideal.span ({(Polynomial.X - Polynomial.C z.val) ^ n} : Set (Polynomial ℂ)) ∧
                                        (∀ q : Polynomial ℂ,
                                          let r := q %ₘ ((Polynomial.X - Polynomial.C z.val) ^ n)
                                          r.degree < (n : WithBot ℕ) ∧
                                            r.eval₂ (π.comp MvPolynomial.C) (π p) =
                                              q.eval₂ (π.comp MvPolynomial.C) (π p) ∧
                                            ∀ s : Polynomial ℂ, s.degree < (n : WithBot ℕ) →
                                              s.eval₂ (π.comp MvPolynomial.C) (π p) =
                                                q.eval₂ (π.comp MvPolynomial.C) (π p) → s = r) ∧
                                        (∀ q r : Polynomial ℂ,
                                          q.eval₂ (π.comp MvPolynomial.C) (π p) =
                                            r.eval₂ (π.comp MvPolynomial.C) (π p) ↔
                                              q %ₘ ((Polynomial.X - Polynomial.C z.val) ^ n) =
                                                r %ₘ ((Polynomial.X - Polynomial.C z.val) ^ n)) ∧
                                        (∀ q : Polynomial ℂ,
                                          q.eval₂ (π.comp MvPolynomial.C) (π p) =
                                            ∑ i ∈ Finset.range n,
                                              π (MvPolynomial.C ((Polynomial.hasseDeriv i q).eval z.val)) *
                                                (π p - π (MvPolynomial.C z.val)) ^ i) ∧
                                        (∀ q : Polynomial ℂ,
                                          q.eval₂ (π.comp MvPolynomial.C) (π p) = 0 ↔
                                            ∀ i < n, (Polynomial.hasseDeriv i q).eval z.val = 0) ∧
                                        (∀ q r : Polynomial ℂ,
                                          q.eval₂ (π.comp MvPolynomial.C) (π p) =
                                            r.eval₂ (π.comp MvPolynomial.C) (π p) ↔
                                              ∀ i < n, (Polynomial.hasseDeriv i q).eval z.val =
                                                (Polynomial.hasseDeriv i r).eval z.val) ∧
                                        (∀ q : Polynomial ℂ,
                                          q.eval₂ (π.comp MvPolynomial.C) (π p) =
                                            ∑ i ∈ Finset.range n,
                                              π (MvPolynomial.C (((Polynomial.derivative^[i]) q).eval z.val /
                                                (i.factorial : ℂ))) *
                                                  (π p - π (MvPolynomial.C z.val)) ^ i) ∧
                                        (∀ q : Polynomial ℂ,
                                          q.eval₂ (π.comp MvPolynomial.C) (π p) = 0 ↔
                                            ∀ i < n, ((Polynomial.derivative^[i]) q).eval z.val = 0) ∧
                                        (∀ q r : Polynomial ℂ,
                                          q.eval₂ (π.comp MvPolynomial.C) (π p) =
                                            r.eval₂ (π.comp MvPolynomial.C) (π p) ↔
                                              ∀ i < n, ((Polynomial.derivative^[i]) q).eval z.val =
                                                ((Polynomial.derivative^[i]) r).eval z.val) ∧
                                        (∀ q : Polynomial ℂ, q ≠ 0 →
                                          (∀ k : ℕ,
                                            (q.eval₂ (π.comp MvPolynomial.C) (π p)) ^ k = 0 ↔
                                              n ≤ q.rootMultiplicity z.val * k) ∧
                                          (0 < q.rootMultiplicity z.val →
                                            IsNilpotent (q.eval₂ (π.comp MvPolynomial.C) (π p)) ∧
                                              nilpotencyClass (q.eval₂ (π.comp MvPolynomial.C) (π p)) =
                                                (n + q.rootMultiplicity z.val - 1) /
                                                  q.rootMultiplicity z.val)) ∧
                                        (minpoly ℂ (π p) = (Polynomial.X - Polynomial.C z.val) ^ n ∧
                                          (∃ b : PowerBasis ℂ (Algebra.adjoin ℂ ({π p} : Set _)),
                                            (b.gen : ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
                                              Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))) = π p ∧
                                              b.dim = n) ∧
                                          FiniteDimensional ℂ (Algebra.adjoin ℂ ({π p} : Set _)) ∧
                                          Module.finrank ℂ (Algebra.adjoin ℂ ({π p} : Set _)) = n ∧
                                          LinearIndependent ℂ (fun i : Fin n => (π p) ^ (i : ℕ))) ∧
                                        (∃! e : (Polynomial ℂ ⧸
                                            Ideal.span {(Polynomial.X - Polynomial.C z.val) ^ n}) ≃ₐ[ℂ]
                                              Algebra.adjoin ℂ ({π p} : Set _),
                                          ∀ q : Polynomial ℂ,
                                            (e (Ideal.Quotient.mk
                                                (Ideal.span {(Polynomial.X - Polynomial.C z.val) ^ n}) q) :
                                              ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
                                                Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I)))) =
                                                  q.eval₂ (π.comp MvPolynomial.C) (π p)) ∧
                                        ((n = d ↔ Algebra.adjoin ℂ ({π p} : Set _) = ⊤) ∧
                                          (n = d ↔ Function.Surjective
                                            (fun q : Polynomial ℂ => q.eval₂ (π.comp MvPolynomial.C) (π p))) ∧
                                          (n < d ↔ ∃ y : ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
                                              Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))),
                                            ∀ q : Polynomial ℂ,
                                              q.eval₂ (π.comp MvPolynomial.C) (π p) ≠ y)) ∧
                                        ∃ f : (Polynomial ℂ ⧸
                                            Ideal.span {(Polynomial.X - Polynomial.C z.val) ^ n}) →+*
                                          ((MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
                                            Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))),
                                          Function.Injective f ∧ ∀ q : Polynomial ℂ,
                                            f (Ideal.Quotient.mk
                                              (Ideal.span {(Polynomial.X - Polynomial.C z.val) ^ n}) q) =
                                                q.eval₂ (π.comp MvPolynomial.C) (π p))) ∧
                (let R := I.colon (J : Set (MvPolynomial (Fin 4) ℂ))
                 I ≤ R ∧
                 I.colon (R : Set (MvPolynomial (Fin 4) ℂ)) = J ∧
                 FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) ∧
                 Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) +
                   Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = M.natDegree ∧
                 (∀ K : Ideal (MvPolynomial (Fin 4) ℂ), I ≤ K →
                   (J ≤ K ↔ I.colon (K : Set (MvPolynomial (Fin 4) ℂ)) ≤ R))) ∧
                (let p : ℕ → MvPolynomial (Fin 4) ℂ := fun j =>
                   (extensionChartDerivation L.g₂ L.g₃ c)^[j] (extensionChartNormalize c Q)
                 let T := (Finset.range s).filter (fun j =>
                   p j ∉ (I ⊔ Ideal.span (Set.range (fun i : Fin j => p i.val))))
                 J = I ⊔ Ideal.span (p '' (T : Set ℕ)) ∧
                 T.card + Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ≤ M.natDegree ∧
                 (J = ⊤ → ∃ b : T → Polynomial ℂ,
                   (∀ j : T, (b j).degree < (M.natDegree : ℕ) ∧
                     (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) (b j)).totalDegree ≤
                       M.natDegree - 1) ∧
                   1 - ∑ j : T,
                     Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b j) * p j.val ∈ I ∧
                   ∀ D : ℕ, (∀ j : T, (p j.val).totalDegree ≤ D) →
                     (1 - ∑ j : T,
                       Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b j) * p j.val).totalDegree ≤
                         M.natDegree - 1 + D)) ∧
                (∃ g : Polynomial ℂ,
                  g.Monic ∧ g ∣ M ∧ g.natDegree ≤ M.natDegree ∧
                  g = Nat.rec M (fun j h => gcd h
                    (MvPolynomial.aeval (Fin.cons Polynomial.X r)
                      ((extensionChartDerivation L.g₂ L.g₃ c)^[j]
                        (extensionChartNormalize c Q)))) s ∧
                  J = I ⊔ Ideal.span {Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g} ∧
                  (let f : Fin 4 → MvPolynomial (Fin 4) ℂ :=
                     Fin.cons (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g)
                       (fun i : Fin 3 => MvPolynomial.X i.succ -
                         Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (r i))
                   J = Ideal.span (Set.range f) ∧
                   (∀ i : Fin 4, (f i).totalDegree ≤ max 1 M.natDegree) ∧
                   (∀ (k : ℕ) (i : Fin (k + 1) × Fin 4),
                     ((extensionChartDerivation L.g₂ L.g₃ c)^[i.1.val] (f i.2)).totalDegree ≤
                       max 1 M.natDegree + k)) ∧
                  (∀ f : MvPolynomial (Fin 4) ℂ,
                    f ∈ J ↔ g ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
                  Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = g.natDegree ∧
                  (∀ p : MvPolynomial (Fin 4) ℂ,
                    let h := gcd g (MvPolynomial.aeval (Fin.cons Polynomial.X r) p)
                    let K := J ⊔ Ideal.span {p}
                    h.Monic ∧ h ∣ g ∧
                    (∀ f : MvPolynomial (Fin 4) ℂ,
                      f ∈ K ↔ h ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
                    FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
                    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = h.natDegree ∧
                    h.natDegree ≤ g.natDegree ∧
                    (h = g ↔ p ∈ J) ∧
                    (h.natDegree < g.natDegree ↔ p ∉ J) ∧
                    (Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) <
                      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ↔ p ∉ J) ∧
                    (∀ q : Polynomial ℂ, q.Monic →
                      (∀ f : MvPolynomial (Fin 4) ℂ,
                        f ∈ K ↔ q ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) → q = h)) ∧
                  (let δ := extensionChartDerivation L.g₂ L.g₃ c
                   let p := Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g
                   (∀ k : ℕ, δ^[k] p = Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
                     (Polynomial.derivative^[k] g)) ∧
                   δ^[g.natDegree] p = algebraMap ℂ (MvPolynomial (Fin 4) ℂ)
                     (g.natDegree.factorial : ℂ) ∧
                   (g.natDegree.factorial : ℂ)⁻¹ • δ^[g.natDegree] p = 1 ∧
                   (∀ k : ℕ, g.natDegree < k → δ^[k] p = 0) ∧
                   (∀ k : ℕ, Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ≤ k →
                     Ideal.span (Set.range (fun i : Fin (k + 1) => δ^[i.val] p)) = ⊤)) ∧
                  (∀ e : V → ℕ,
                    J = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e v)) →
                    g = (∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ e v) ∧
                      ∀ z : ℂ, g.eval z = 0 ↔ ∃ v : V, 0 < e v ∧ z = v.val 0) ∧
                  (∀ h : Polynomial ℂ, h.Monic →
                    (∀ f : MvPolynomial (Fin 4) ℂ,
                      f ∈ J ↔ h ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) → h = g)) ∧
                FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
                (J ≠ ⊤ → ∃ p : MvPolynomial (Fin 4) ℂ,
                  p ∈ J ∧ extensionChartDerivation L.g₂ L.g₃ c p ∉ J) ∧
                (J ≠ ⊤ → ∃ g : Polynomial ℂ,
                  g.Monic ∧ 0 < g.natDegree ∧
                  g.natDegree ≤ Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
                  (∀ q : Polynomial ℂ, Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) q ∈ J ↔ g ∣ q) ∧
                  Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g ∈ J ∧
                  extensionChartDerivation L.g₂ L.g₃ c (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g) =
                    Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g.derivative ∧
                  g.derivative.natDegree < g.natDegree ∧
                  extensionChartDerivation L.g₂ L.g₃ c (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g) ∉ J) ∧
                ∃ e : V → ℕ,
                  (∀ v : V, e v ≤ 3 * U + 1 ∧ ∀ k ≤ 3 * U + 1,
                    k ≤ e v ↔ ∀ i : Fin s, ∀ j < k,
                      MvPolynomial.eval v.val
                        ((extensionChartDerivation L.g₂ L.g₃ c)^[j + i.val]
                          (extensionChartNormalize c Q)) = 0) ∧
                  J = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e v)) ∧
                  (∀ (r₀ : ℕ) (f : Fin r₀ → MvPolynomial (Fin 4) ℂ),
                    J = Ideal.span (Set.range f) → ∀ k : ℕ,
                    let K := Ideal.span (Set.range (fun i : Fin (k + 1) × Fin r₀ =>
                      (extensionChartDerivation L.g₂ L.g₃ c)^[i.1.val] (f i.2)))
                    K = J ⊔ Ideal.span ((extensionChartDerivation L.g₂ L.g₃ c)^[k] ''
                      (J : Set (MvPolynomial (Fin 4) ℂ))) ∧
                      K = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e v - k)) ∧
                      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
                      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = ∑ v : V, (e v - k) ∧
                      (∀ p : MvPolynomial (Fin 4) ℂ,
                        p ∈ K ↔ ∃ q : MvPolynomial (Fin 4) ℂ, q ∈ J ∧
                          p - (extensionChartDerivation L.g₂ L.g₃ c)^[k] q ∈ J) ∧
                      (K = ⊤ ↔ ∀ v : V, e v ≤ k) ∧
                      (let K' := Ideal.span (Set.range
                         (fun i : Fin (k + 1 + 1) × Fin r₀ =>
                           (extensionChartDerivation L.g₂ L.g₃ c)^[i.1.val] (f i.2)))
                       K ≤ K' ∧
                       (K = K' ↔ K = ⊤) ∧
                       (K < K' ↔ ∃ v : V, k < e v) ∧
                       Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) =
                         Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K') +
                           (Finset.univ.filter (fun v : V => k < e v)).card)) ∧
                  (∀ k : ℕ,
                    let K := J ⊔ Ideal.span ((extensionChartDerivation L.g₂ L.g₃ c)^[k] ''
                      (J : Set (MvPolynomial (Fin 4) ℂ)))
                    K = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (e v - k)) ∧
                      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
                      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = ∑ v : V, (e v - k) ∧
                      (∀ p : MvPolynomial (Fin 4) ℂ,
                        p ∈ K ↔ ∃ q : MvPolynomial (Fin 4) ℂ, q ∈ J ∧
                          p - (extensionChartDerivation L.g₂ L.g₃ c)^[k] q ∈ J) ∧
                      (K = ⊤ ↔ ∀ v : V, e v ≤ k)) ∧
                  (∀ f : V → ℕ,
                    let K : Ideal (MvPolynomial (Fin 4) ℂ) :=
                      ⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (f v)
                    (J ≤ K ↔ ∀ v : V, f v ≤ e v) ∧
                    (J = K ↔ e = f) ∧
                    (J < K ↔ (∀ v : V, f v ≤ e v) ∧ ∃ v : V, f v < e v)) ∧
                  Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ J) ≃ₐ[ℂ]
                    ((v : V) → Polynomial ℂ ⧸
                      Ideal.span {(Polynomial.X - Polynomial.C (v.val 0)) ^ e v})) ∧
                  J.radical = (⨅ v : V, if e v = 0 then ⊤ else RingHom.ker (MvPolynomial.eval v.val)) ∧
                  (∀ P' : Ideal (MvPolynomial (Fin 4) ℂ), P'.IsPrime →
                    (J ≤ P' ↔ ∃! v : V, 0 < e v ∧ P' = RingHom.ker (MvPolynomial.eval v.val))) ∧
                  Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = ∑ v : V, e v ∧
                  I.colon (J : Set (MvPolynomial (Fin 4) ℂ)) =
                    (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val (3 * U + 1 - e v)) ∧
                  Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸
                    I.colon (J : Set (MvPolynomial (Fin 4) ℂ))) =
                    ∑ v : V, (3 * U + 1 - e v) ∧
                  (let R := I.colon (J : Set (MvPolynomial (Fin 4) ℂ))
                   J ⊔ R = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val
                     (min (e v) (3 * U + 1 - e v))) ∧
                   FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J ⊔ R) ∧
                   Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J ⊔ R) =
                     ∑ v : V, min (e v) (3 * U + 1 - e v) ∧
                   (J ⊔ R = ⊤ ↔ ∀ v : V, e v = 0 ∨ e v = 3 * U + 1) ∧
                   ((∀ v : V, e v = 0 ∨ e v = 3 * U + 1) →
                     J ⊓ R = I ∧ J * R = I ∧
                     Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₐ[ℂ]
                       (MvPolynomial (Fin 4) ℂ ⧸ J) × (MvPolynomial (Fin 4) ℂ ⧸ R)) ∧
                     ∃ p : MvPolynomial (Fin 4) ℂ,
                       p ∈ J ∧ 1 - p ∈ R ∧ p * p - p ∈ I ∧
                       J = I ⊔ Ideal.span {p} ∧ R = I ⊔ Ideal.span {1 - p}) ∧
                   (let K := J ⊓ R
                    I ≤ K ∧ K ^ 2 ≤ I ∧
                    K = (⨅ v : V, extensionChartContactIdeal L.g₂ L.g₃ c v.val
                      (max (e v) (3 * U + 1 - e v))) ∧
                    FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
                    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) =
                      ∑ v : V, max (e v) (3 * U + 1 - e v) ∧
                    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) +
                      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J ⊔ R) =
                      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) ∧
                    (K = I ↔ J ⊔ R = ⊤))) ∧
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
  obtain ⟨C, hC, hbound⟩ := spectral_factor_cyclic_vector_multiplicity_obstruction
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
  obtain ⟨hgeneric, hrest⟩ := hprefix s
  refine ⟨?_, hrest⟩
  intro hs htop
  obtain ⟨a, ha, hq, hqdegree, b, hb, hbdegree, hcert, hcertdegree,
    hinverse, hcancel, hunit, T, hT, hker, hTunique,
    β, hβ, hcoord, hreconstruct, hfinrank,
    ρ, hρaction, hρentries, hρzero, hρeval, hchar, hdet, hρunit,
    hchars, htrace, hspectrum, hnil, hpower, hrank, hfitting, halgebra, hprojector, hmonoid, hstable, heigenspace, hsplit⟩ := hgeneric hs htop
  refine ⟨a, ha, hq, hqdegree, b, hb, hbdegree, hcert, hcertdegree,
    hinverse, hcancel, hunit, T, hT, hker, hTunique,
    β, hβ, hcoord, hreconstruct, hfinrank,
    ρ, hρaction, hρentries, hρzero, hρeval, hchar, hdet, hρunit,
    hchars, htrace, hspectrum, hnil, hpower, hrank, hfitting, halgebra, hprojector, hmonoid, hstable, heigenspace, ?_⟩
  intro p
  let W := Finset.univ.image (fun v : V => MvPolynomial.eval v.val p)
  obtain ⟨hinternal, e, he, Pr, hPr, hidem, horth, hsum, hrange, hcomm,
    ε, hεaction, hεformula, hεidem, hεorth, hεsum, hεker, Φ, hΦ, hεΦ, hfactors⟩ := hsplit p
  refine ⟨hinternal, e, he, Pr, hPr, hidem, horth, hsum, hrange, hcomm,
    ε, hεaction, hεformula, hεidem, hεorth, hεsum, hεker, Φ, hΦ, hεΦ, ?_⟩
  intro z
  obtain ⟨ψ, hψ, hdim, hpow, hbound, hresolvent, hpolynomial,
    hν, hann, hevalker, hreps, heq, htaylor, hjet, hjet_eq,
    hordinary, hordinary_zero, hordinary_eq, hindex, hpowerbasis, hmodel,
    hgeneration, f, hfinj, hf⟩ := hfactors z
  refine ⟨ψ, hψ, hdim, hpow, hbound, hresolvent, hpolynomial,
    hν, hann, hevalker, hreps, heq, htaylor, hjet, hjet_eq,
    hordinary, hordinary_zero, hordinary_eq, hindex, hpowerbasis, hmodel,
    hgeneration, ?_, f, hfinj, hf⟩
  let A := (MvPolynomial (Fin 4) ℂ ⧸ I) ⧸
    Ideal.span ({1 - ε z} : Set (MvPolynomial (Fin 4) ℂ ⧸ I))
  let π : MvPolynomial (Fin 4) ℂ →+* A :=
    (Ideal.Quotient.mk (Ideal.span {1 - ε z})).comp (Ideal.Quotient.mk I)
  intro y
  have hcriterion := @commutative_weighted_surjectivity_iff (Polynomial ℂ) A
    inferInstance (fun q => q.eval₂ (π.comp MvPolynomial.C) (π p)) y
  exact hcriterion.trans (and_congr hgeneration.2.1.symm Iff.rfl)
