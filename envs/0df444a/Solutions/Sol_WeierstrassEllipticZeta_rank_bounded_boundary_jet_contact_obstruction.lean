-- Prove2me | solution 1 for WeierstrassEllipticZeta.rank_bounded_boundary_jet_contact_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T03:23:34.815111+00:00
-- url     : https://prove2.me/submissions/5fb0fa2e-47ae-45af-8ca7-f66c3a28e4e1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_supported_relations_rank_bound
import Theorems.Thm_WeierstrassEllipticZeta_relation_space_boundary_jet_contact_obstruction
import Mathlib.LinearAlgebra.Pi
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
              ∃ S : Fin 2 → Finset (Fin 4 →₀ ℕ),
              let B := fun c : Fin 2 => (Finset.univ.biUnion fun i : Fin 4 =>
                (S c).image (fun d => d + Finsupp.single i 1)) \ S c
              let jets := fun (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ)
                (x : {z : X // a z = c}) (k : Fin ((U : ℕ) + 1)) =>
                  MvPolynomial.eval (extensionChartCoordinates G.S c x.val.val)
                    ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k.val] p)
              ((∑ c : Fin 2, Module.finrank ℂ (Submodule.span ℂ
                ((fun d : Fin 4 →₀ ℕ => jets c (MvPolynomial.monomial d 1)) ''
                  (S c : Set (Fin 4 →₀ ℕ)))) : ℕ) : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2 ∧
              (∀ c : Fin 2, 0 ∈ S c) ∧
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
  have hnext := WeierstrassEllipticZeta.relation_space_boundary_jet_contact_obstruction G
  rcases hnext with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hlocal hdegree hcharts
  rcases hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts with hjet | hperiod
  · obtain ⟨a, hvalid, S, R, hcount, hvanish, hzero, hrank⟩ := hjet
    let J (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ)
        (x : {z : X // a z = c}) (k : Fin ((U : ℕ) + 1)) :=
      MvPolynomial.eval (extensionChartCoordinates G.S c x.val.val)
        ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k.val] p)
    let E (c : Fin 2) : MvPolynomial (Fin 4) ℂ →ₗ[ℂ]
        ({z : X // a z = c} → Fin ((U : ℕ) + 1) → ℂ) :=
      LinearMap.pi fun x => LinearMap.pi fun k =>
        (MvPolynomial.aeval (extensionChartCoordinates G.S c x.val.val)).toLinearMap.comp
          ((extensionChartDerivation G.L.g₂ G.L.g₃ c).toLinearMap ^ k.val)
    have hE (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ) : E c p = J c p := by
      funext x k
      change MvPolynomial.aeval (extensionChartCoordinates G.S c x.val.val)
        (((extensionChartDerivation G.L.g₂ G.L.g₃ c).toLinearMap ^ k.val) p) = _
      rw [MvPolynomial.aeval_eq_eval, Module.End.pow_apply]
      rfl
    let r (c : Fin 2) := Module.finrank ℂ (Submodule.span ℂ
      ((fun d : Fin 4 →₀ ℕ => J c (MvPolynomial.monomial d 1)) '' (S c : Set (Fin 4 →₀ ℕ))))
    have hdim (c : Fin 2) : r c + Module.finrank ℂ (R c) ≤ (S c).card := by
      have hrel : ∀ p : R c, E c p.val.val = 0 := by
        intro p
        rw [hE]
        funext x k
        exact hvanish c p x k
      have h := WeierstrassEllipticZeta.supported_relations_rank_bound
        ℂ (Fin 4) ({z : X // a z = c} → Fin ((U : ℕ) + 1) → ℂ)
        (E c) (S c) (R c) hrel
      have hmonomials :
          (fun d : Fin 4 →₀ ℕ => E c (MvPolynomial.monomial d 1)) =
            (fun d : Fin 4 →₀ ℕ => J c (MvPolynomial.monomial d 1)) :=
        funext fun d => hE c (MvPolynomial.monomial d 1)
      rw [hmonomials] at h
      exact h
    refine Or.inl ⟨a, hvalid, S, ?_, hzero, hrank⟩
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hdim c)
    rw [Finset.sum_add_distrib] at hsum
    have hsum' : ((∑ c : Fin 2, r c : ℕ) : ℝ) +
        ((∑ c : Fin 2, Module.finrank ℂ (R c) : ℕ) : ℝ) ≤
        ((∑ c : Fin 2, (S c).card : ℕ) : ℝ) := by exact_mod_cast hsum
    change ((∑ c : Fin 2, r c : ℕ) : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2
    linarith
  · exact Or.inr hperiod
