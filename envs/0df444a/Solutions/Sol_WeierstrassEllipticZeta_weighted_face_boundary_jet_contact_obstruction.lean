-- Prove2me | solution 1 for WeierstrassEllipticZeta.weighted_face_boundary_jet_contact_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T22:38:36.79699+00:00
-- url     : https://prove2.me/submissions/a1f9aa67-b746-4f59-9250-f69c5615f37c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_time_axis_jet_box_certificate
import Theorems.Thm_WeierstrassEllipticZeta_time_coordinate_cardinality_contact_obstruction
import Theorems.Thm_WeierstrassEllipticZeta_finite_jet_span_interpolation
import Theorems.Thm_WeierstrassEllipticZeta_finite_span_rank_stability_iff
import Mathlib.Data.Fintype.Card
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
            ((∃ a : X → Fin 2,
              (∀ x : X, G.S (extensionChartDenominator (a x)) x.val ≠ 0) ∧
              ∃ b : Fin 2 → (Fin 4 →₀ ℕ),
              let S := fun c : Fin 2 => Finset.Iic (b c)
              let B := fun c : Fin 2 => (Finset.univ.biUnion fun i : Fin 4 =>
                (S c).image (fun d => d + Finsupp.single i 1)) \ S c
              let jets := fun (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ)
                (x : {z : X // a z = c}) (k : Fin ((U : ℕ) + 1)) =>
                  MvPolynomial.eval (extensionChartCoordinates G.S c x.val.val)
                    ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k.val] p)
              ∃ p : Fin 2 → MvPolynomial (Fin 4) ℂ,
              ((∑ c : Fin 2, ∑ i : Fin 4,
                (p c).degreeOf i * ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
                  (b c j + 1) : ℕ) : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2 ∧
              (∀ c : Fin 2, p c ≠ 0) ∧
              (∀ (c : Fin 2) (i : Fin 4), (p c).degreeOf i ≤ b c i) ∧
              (∀ c : Fin 2, ∀ x : {z : X // a z = c},
                p c ∈ extensionChartContactIdeal G.L.g₂ G.L.g₃ c
                  (extensionChartCoordinates G.S c x.val.val) ((U : ℕ) + 1)) ∧
              ∀ c : Fin 2,
                Module.finrank ℂ (Submodule.span ℂ
                  ((fun d : Fin 4 →₀ ℕ => jets c (MvPolynomial.monomial d 1)) ''
                    ((S c ∪ B c : Finset (Fin 4 →₀ ℕ)) : Set (Fin 4 →₀ ℕ)))) =
                Module.finrank ℂ (Submodule.span ℂ
                  ((fun d : Fin 4 →₀ ℕ => jets c (MvPolynomial.monomial d 1)) ''
                    (S c : Set (Fin 4 →₀ ℕ))))) ∨
              (((U : ℕ) + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2) := by
  classical
  have hnext := WeierstrassEllipticZeta.time_coordinate_cardinality_contact_obstruction G
  rcases hnext with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hlocal hdegree hcharts
  rcases hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts with hcardbound | hperiod
  · have hcover (z : ℂ) : ∃ c : Fin 2, G.S (extensionChartDenominator c) z ≠ 0 := by
      obtain ⟨hv, hp⟩ := G.hP z 0
      have hc := (G.P ((TranscendenceTheory.extensionPeriodGraph G.L.lattice G.η).mkQ
        (z, 0))).property
      rw [hp] at hc
      obtain ⟨s, hs⟩ := Projectivization.exists_smul_eq_mk_rep ℂ _ hv
      rw [← hs] at hc
      rcases hc with h0 | h2
      · refine ⟨0, ?_⟩
        intro hs
        have hz : G.S 0 z = 0 := by simpa [extensionChartDenominator] using hs
        simp [hz] at h0
      · refine ⟨1, ?_⟩
        intro hs
        have hz : G.S 2 z = 0 := by simpa [extensionChartDenominator] using hs
        simp [hz] at h2
    choose a ha using fun x : X => hcover x.val
    let V (c : Fin 2) : Finset (Fin 4 → ℂ) := Finset.univ.image
      (fun x : {z : X // a z = c} => extensionChartCoordinates G.S c x.val.val)
    have hcoords0 (c : Fin 2) (z : ℂ) : extensionChartCoordinates G.S c z 0 = z := by
      fin_cases c <;> simp [extensionChartCoordinates]
    have hinjfun (c : Fin 2) : Function.Injective
        (fun x : {z : X // a z = c} => extensionChartCoordinates G.S c x.val.val) := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      simpa only [hcoords0] using congrFun hxy 0
    have hVinj (c : Fin 2) : Function.Injective (fun v : V c => v.val 0) := by
      intro v w hvw
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp v.property
      obtain ⟨y, _, hy⟩ := Finset.mem_image.mp w.property
      apply Subtype.ext
      rw [← hx, ← hy]
      apply congrArg (extensionChartCoordinates G.S c)
      simpa only [← hx, ← hy, hcoords0] using hvw
    have hcard (c : Fin 2) : (V c).card = Fintype.card {z : X // a z = c} := by
      dsimp only [V]
      rw [Finset.card_image_of_injective _ (hinjfun c), Finset.card_univ]
    have hsumcard : (∑ c : Fin 2, (V c).card) = X.card := by
      simp_rw [hcard]
      rw [← Fintype.card_sigma]
      simpa using Fintype.card_congr (Equiv.sigmaFiberEquiv a)
    let b (c : Fin 2) : Fin 4 →₀ ℕ := Finsupp.single 0 (((U : ℕ) + 1) * (V c).card)
    have hcert := fun c : Fin 2 => WeierstrassEllipticZeta.time_axis_jet_box_certificate
      G c (V c) ((U : ℕ) + 1) (hVinj c)
    choose p hne hfit hfaces hcontact hrep using hcert
    refine Or.inl ⟨a, ha, b, p, ?_, hne, hfit, ?_, ?_⟩
    · apply le_trans (Nat.cast_le.mpr (Finset.sum_le_sum fun c _ => hfaces c))
      simpa only [← Finset.mul_sum, hsumcard] using hcardbound
    · intro c x
      exact hcontact c ⟨extensionChartCoordinates G.S c x.val.val,
        Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
    · intro c
      let S : Finset (Fin 4 →₀ ℕ) := Finset.Iic (b c)
      let B := (Finset.univ.biUnion fun i : Fin 4 =>
        S.image (fun d => d + Finsupp.single i 1)) \ S
      let D := extensionChartDerivation G.L.g₂ G.L.g₃ c
      let v (x : {z : X // a z = c}) : Fin 4 → ℂ :=
        extensionChartCoordinates G.S c x.val.val
      apply (WeierstrassEllipticZeta.finite_span_rank_stability_iff ℂ _ (Fin 4 →₀ ℕ)
        (fun d => fun (x : {z : X // a z = c}) (k : Fin ((U : ℕ) + 1)) =>
          MvPolynomial.eval (v x) (D^[k.val] (MvPolynomial.monomial d 1))) S B).mp
      intro d _
      obtain ⟨r, hr, hmod⟩ := hrep c (MvPolynomial.monomial d 1)
      apply (WeierstrassEllipticZeta.finite_jet_span_interpolation
        ℂ (Fin 4) {z : X // a z = c} D v ((U : ℕ) + 1) S
          (MvPolynomial.monomial d 1)).mp
      refine ⟨r, hr, ?_⟩
      intro x k
      exact hmod ⟨v x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩ k
  · exact Or.inr hperiod
