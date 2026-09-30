-- Prove2me | solution 1 for WeierstrassEllipticZeta.bounded_subset_resultant_families
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T16:19:08.12626+00:00
-- url     : https://prove2.me/submissions/ec02b26b-24c9-4acf-bb70-692f4a7e7b17
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TranscendenceTheory_bounded_bivariate_relation_basis
import Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_rootwise_relations
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

private lemma eval_zero_of_mem_relation_span
    (L : Type*) [CommRing L] (φ : Polynomial ℂ →+* L) (z : L)
    (k : ℕ) (H : Fin k → Polynomial (Polynomial ℂ))
    (hH : ∀ j, (H j).eval₂ φ z = 0)
    (P : Polynomial (Polynomial ℂ))
    (hP : P ∈ Submodule.span ℂ (Set.range H)) : P.eval₂ φ z = 0 := by
  let e : Polynomial (Polynomial ℂ) →+* L := Polynomial.eval₂RingHom φ z
  change e P = 0
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hP
  · rintro Q ⟨j, rfl⟩
    exact hH j
  · exact map_zero e
  · intro Q R _ _ hQ hR
    rw [map_add, hQ, hR, zero_add]
  · intro c Q _ hQ
    rw [Algebra.smul_def, map_mul, hQ, mul_zero]

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
              let L := AlgebraicClosure (FractionRing (Polynomial ℂ))
              let φ : Polynomial ℂ →+* L :=
                (algebraMap (FractionRing (Polynomial ℂ)) L).comp
                  (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
              ∃ (y : MvPolynomial (Fin 4) ℂ ⧸ I)
                (F : Polynomial (Polynomial ℂ)) (k : ℕ)
                (H : Fin k → Polynomial (Polynomial ℂ)) (a b s : ℕ),
                F.natDegree ≠ 0 ∧
                (∀ i, (F.coeff i).natDegree ≤ a) ∧
                (∀ j i, ((H j).coeff i).natDegree ≤ b) ∧
                (∀ j, (H j).natDegree ≤ s) ∧
                (∀ z ∈ (F.map φ).roots, ∃ j, (H j).eval₂ φ z ≠ 0) ∧
                F.eval₂ (Polynomial.aeval x).toRingHom y = 0 ∧
                (∀ j, (H j).eval₂ (Polynomial.aeval x).toRingHom y = 0) ∧
                ((2 * (F.natDegree * b + s * a) + ((U : ℕ) + 1) : ℕ) : ℝ) ≤
                  C * (n : ℝ) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := WeierstrassEllipticZeta.bounded_subset_rootwise_relations G
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
  obtain ⟨y, F, a, b, s, hFpos, hF, hFx, hroots, hcost⟩ :=
    hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts Y hYX hY hcard
  obtain ⟨k, _, H, _, hspan⟩ := TranscendenceTheory.bounded_bivariate_relation_basis
    ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) x y b s
  have hH (j : Fin k) := (hspan (H j)).mp
    (Submodule.subset_span (Set.mem_range_self j))
  refine ⟨y, F, k, H, a, b, s, hFpos, hF,
    (fun j => (hH j).2.1), (fun j => (hH j).1), ?_, hFx,
    (fun j => (hH j).2.2), hcost⟩
  intro z hz
  obtain ⟨P, hPs, hPb, hPx, hPz⟩ := hroots z hz
  by_contra! hall
  exact hPz (eval_zero_of_mem_relation_span L φ z k H hall P
    ((hspan P).mpr ⟨hPs, hPb, hPx⟩))
