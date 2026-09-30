-- Prove2me | solution 1 for WeierstrassEllipticZeta.bounded_subset_jet_interpolation_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T17:32:11.409167+00:00
-- url     : https://prove2.me/submissions/be65862d-e33c-4a59-894c-a1ac5814dbae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TranscendenceTheory_derivation_formal_jet_substitution
import Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_formal_series_obstruction
import Mathlib.RingTheory.PowerSeries.Basic
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

private lemma formal_monomial_jet_formula
    (G : Frontier.Geometry) (z : ℂ) (p : MvPolynomial (Fin 4) ℂ) (j i k : ℕ) :
    let J : Fin 4 → PowerSeries ℂ := fun a => PowerSeries.mk fun n =>
      MvPolynomial.eval (extensionChartCoordinates G.S 0 z)
        ((extensionChartDerivation G.L.g₂ G.L.g₃ 0)^[n] (MvPolynomial.X a)) /
          (n.factorial : ℂ)
    (k.factorial : ℂ) * PowerSeries.coeff k
      ((J (1 : Fin 4)) ^ j * (MvPolynomial.aeval J p) ^ i) =
        MvPolynomial.eval (extensionChartCoordinates G.S 0 z)
          ((extensionChartDerivation G.L.g₂ G.L.g₃ 0)^[k]
            ((MvPolynomial.X (1 : Fin 4)) ^ j * p ^ i)) := by
  have h := TranscendenceTheory.derivation_formal_jet_substitution ℂ (Fin 4)
    (extensionChartDerivation G.L.g₂ G.L.g₃ 0) (extensionChartCoordinates G.S 0 z)
    ((MvPolynomial.X (1 : Fin 4)) ^ j * p ^ i) k
  simpa only [map_mul, map_pow, MvPolynomial.aeval_X] using! h

private lemma factorial_weight_pairing
    {L : Type*} [AddCommGroup L] [Module ℂ L]
    (k : ℕ) (u v : ℂ) (h : (k.factorial : ℂ) * u = v) (w : L) :
    u • ((k.factorial : ℂ) • w) = v • w ∧
      v • (((k.factorial : ℂ)⁻¹) • w) = u • w := by
  constructor
  · rw [smul_smul, mul_comm, h]
  · rw [← h, smul_smul, mul_right_comm,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)), one_mul]

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
              ∃ (p : MvPolynomial (Fin 4) ℂ)
                (F : Polynomial (Polynomial ℂ)) (a b s : ℕ),
                F.natDegree ≠ 0 ∧
                (∀ i, (F.coeff i).natDegree ≤ a) ∧
                F.eval₂ (Polynomial.aeval x).toRingHom (Ideal.Quotient.mk I p) = 0 ∧
                (∀ z ∈ (F.map φ).roots,
                  ¬ ∃ w : Z × Fin N → L, ∀ i ≤ s, ∀ j ≤ b,
                    (∑ r : Z × Fin N,
                      MvPolynomial.eval (extensionChartCoordinates G.S 0 r.1.val)
                        ((extensionChartDerivation G.L.g₂ G.L.g₃ 0)^[r.2.val]
                          ((MvPolynomial.X (1 : Fin 4)) ^ j * p ^ i)) • w r) =
                      (φ Polynomial.X) ^ j * z ^ i) ∧
                ((2 * (F.natDegree * b + s * a) + ((U : ℕ) + 1) : ℕ) : ℝ) ≤
                  C * (n : ℝ) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := WeierstrassEllipticZeta.bounded_subset_formal_series_obstruction G
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
  let J : Z → Fin 4 → PowerSeries ℂ := fun r a => PowerSeries.mk fun k =>
    MvPolynomial.eval (extensionChartCoordinates G.S 0 r.val)
      ((extensionChartDerivation G.L.g₂ G.L.g₃ 0)^[k] (MvPolynomial.X a)) /
        (k.factorial : ℂ)
  obtain ⟨p, F, a, b, s, hFpos, hF, hFx, hroots, hcost⟩ :=
    hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts Y hYX hY hcard
  refine ⟨p, F, a, b, s, hFpos, hF, hFx, ?_, hcost⟩
  intro z hz hw
  obtain ⟨w, hw⟩ := hw
  apply hroots z hz
  refine ⟨(fun r => (r.2.val.factorial : ℂ) • w r), ?_⟩
  intro i hi j hj
  calc
    _ = ∑ r : Z × Fin N,
        MvPolynomial.eval (extensionChartCoordinates G.S 0 r.1.val)
          ((extensionChartDerivation G.L.g₂ G.L.g₃ 0)^[r.2.val]
            ((MvPolynomial.X (1 : Fin 4)) ^ j * p ^ i)) • w r := by
      apply Finset.sum_congr rfl
      intro r _
      exact (factorial_weight_pairing r.2.val _ _
        (formal_monomial_jet_formula G r.1.val p j i r.2.val) (w r)).1
    _ = _ := hw i hi j hj
