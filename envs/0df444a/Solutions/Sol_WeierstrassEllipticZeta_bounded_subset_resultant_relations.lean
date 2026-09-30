-- Prove2me | solution 1 for WeierstrassEllipticZeta.bounded_subset_resultant_relations
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T15:50:54.649828+00:00
-- url     : https://prove2.me/submissions/12f72a4a-2c36-4c4f-af1d-ad55d675bf5f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TranscendenceTheory_bounded_resultant_family_selection
import Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_resultant_families
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finsupp.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

theorem solution (G : Frontier.Geometry) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, ∀ U : Fin ((G.B (m + 2 * n) - 2) / 3 + 1),
          1 ≤ m → 1 ≤ n → 1 ≤ (U : ℕ) → ∀ X : Finset ℂ,
          0 ∈ X → ∀ Q : MvPolynomial (Fin 7) ℂ,
            (∀ d ∈ Q.support, d 0 + d 1 = m ∧
              d 2 + d 3 + d 4 + d 5 + d 6 = n) →
            (∀ (c : Fin 2) (z : ℂ), G.S (extensionChartDenominator c) z ≠ 0 →
              let f := fun w => MvPolynomial.eval (extensionChartCoordinates G.S c w)
                (extensionChartNormalize c Q)
              ∃! k : ℕ, k < G.B (m + 2 * n) ∧
                (z ∈ X + X + X → 3 * (U : ℕ) + 1 ≤ k) ∧
                (∀ j < k, iteratedDeriv j f z = 0) ∧ iteratedDeriv k f z ≠ 0 ∧
                ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
                  f =ᶠ[𝓝 z] (fun w => (w - z) ^ k * g w)) →
            (∀ (c : Fin 2) (k : ℕ),
              ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k] (extensionChartNormalize c Q)).totalDegree ≤
                m + 2 * n + k) →
            Frontier.HasChartCertificates G m n (U : ℕ) X Q →
            ∀ Y : Finset ℂ, Y ⊆ X → 0 ∈ Y →
              Y.card = ⌊(C * (m : ℝ) * (n : ℝ) ^ 2) /
                (((U : ℕ) + 1 : ℕ) : ℝ)⌋₊ + 1 →
              let Z := Y.filter (fun z => z ∉ G.L.lattice)
              let N := 3 * (U : ℕ) + 1
              let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
                ⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ 0
                  (extensionChartCoordinates G.S 0 z.val) N
              let x := Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 4))
              ∃ (y : MvPolynomial (Fin 4) ℂ ⧸ I)
                (F H : Polynomial (Polynomial ℂ)) (a b : ℕ),
                (∀ i, (F.coeff i).natDegree ≤ a) ∧
                (∀ i, (H.coeff i).natDegree ≤ b) ∧
                (F.natDegree ≠ 0 ∨ H.natDegree ≠ 0) ∧
                F.resultant H ≠ 0 ∧
                F.eval₂ (Polynomial.aeval x).toRingHom y = 0 ∧
                H.eval₂ (Polynomial.aeval x).toRingHom y = 0 ∧
                ((2 * (F.natDegree * b + H.natDegree * a) + ((U : ℕ) + 1) : ℕ) : ℝ) ≤
                  C * (n : ℝ) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := WeierstrassEllipticZeta.bounded_subset_resultant_families G
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hlocal hdegree hcharts Y hYX hY hcard
  let Z := Y.filter (fun z => z ∉ G.L.lattice)
  let N := 3 * (U : ℕ) + 1
  let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ 0
      (extensionChartCoordinates G.S 0 z.val) N
  let x := Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 4))
  let L := AlgebraicClosure (FractionRing (Polynomial ℂ))
  let φ : Polynomial ℂ →+* L :=
    (algebraMap (FractionRing (Polynomial ℂ)) L).comp
      (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
  have hφ : Function.Injective φ :=
    (RingHom.injective (algebraMap (FractionRing (Polynomial ℂ)) L)).comp
      (IsFractionRing.injective (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
  obtain ⟨y, F, k, H, a, b, s, hFpos, hF, hH, hHs, hroots, hFx, hHx, hcost⟩ :=
    hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts Y hYX hY hcard
  have hFnz : F ≠ 0 := fun hz => hFpos (by simp [hz])
  obtain ⟨t, _, hres, hd, hc⟩ := TranscendenceTheory.bounded_resultant_family_selection
    L φ hφ F k b s H hFnz (IsAlgClosed.splits _) hroots hHs hH
  refine ⟨y, F, ∑ j : Fin k, (t ^ j.val) • H j, a, b,
    hF, hc, Or.inl hFpos, hres, hFx, ?_, ?_⟩
  · simp only [Polynomial.eval₂_finsetSum, nsmul_eq_mul, Polynomial.eval₂_mul,
      hHx, mul_zero, Finset.sum_const_zero]
  · have hb : ((2 * (F.natDegree * b +
        (∑ j : Fin k, (t ^ j.val) • H j).natDegree * a) + ((U : ℕ) + 1) : ℕ) : ℝ) ≤
        ((2 * (F.natDegree * b + s * a) + ((U : ℕ) + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right
        (Nat.mul_le_mul_left 2 (Nat.add_le_add_left (Nat.mul_le_mul_right a hd) _)) _
    exact hb.trans hcost
