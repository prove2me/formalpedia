-- Prove2me | solution 1 for WeierstrassEllipticZeta.box_degree_boundary_jet_contact_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T04:46:48.230233+00:00
-- url     : https://prove2.me/submissions/e87477cc-7349-4007-a286-e86bfa10d7cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_box_volume_face_bound
import Theorems.Thm_WeierstrassEllipticZeta_weighted_face_boundary_jet_contact_obstruction
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
              ((∑ c : Fin 2, ∏ i : Fin 4, (b c i + 1) : ℕ) : ℝ) ≤
                C * (m : ℝ) * (n : ℝ) ^ 2 +
                ((∑ c : Fin 2, ∏ i : Fin 4, (b c i - (p c).degreeOf i + 1) : ℕ) : ℝ) ∧
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
  have hnext := WeierstrassEllipticZeta.weighted_face_boundary_jet_contact_obstruction G
  rcases hnext with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hlocal hdegree hcharts
  rcases hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts with hjet | hperiod
  · obtain ⟨a, hvalid, b, p, hcount, hne, hfit, hcontact, hrank⟩ := hjet
    let V (c : Fin 2) : ℕ := ∏ i : Fin 4, (b c i + 1)
    let I (c : Fin 2) : ℕ := ∏ i : Fin 4, (b c i - (p c).degreeOf i + 1)
    let F (c : Fin 2) : ℕ := ∑ i : Fin 4,
      (p c).degreeOf i * ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, (b c j + 1)
    have hface (c : Fin 2) : V c ≤ I c + F c :=
      WeierstrassEllipticZeta.box_volume_face_bound (Fin 4) (b c)
        (fun i => (p c).degreeOf i) (hfit c)
    have hsum : (∑ c : Fin 2, V c) ≤ (∑ c : Fin 2, I c) + ∑ c : Fin 2, F c := by
      calc
        (∑ c : Fin 2, V c) ≤ ∑ c : Fin 2, (I c + F c) :=
          Finset.sum_le_sum fun c _ => hface c
        _ = (∑ c : Fin 2, I c) + ∑ c : Fin 2, F c := Finset.sum_add_distrib
    have hreal : ((∑ c : Fin 2, V c : ℕ) : ℝ) ≤
        ((∑ c : Fin 2, I c : ℕ) : ℝ) + ((∑ c : Fin 2, F c : ℕ) : ℝ) := by
      exact_mod_cast hsum
    have hfaces : ((∑ c : Fin 2, F c : ℕ) : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2 := hcount
    refine Or.inl ⟨a, hvalid, b, p, ?_, hne, hfit, hcontact, hrank⟩
    change ((∑ c : Fin 2, V c : ℕ) : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2 +
      ((∑ c : Fin 2, I c : ℕ) : ℝ)
    linarith
  · exact Or.inr hperiod
