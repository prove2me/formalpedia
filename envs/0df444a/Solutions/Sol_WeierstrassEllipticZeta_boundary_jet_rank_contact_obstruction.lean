-- Prove2me | solution 1 for WeierstrassEllipticZeta.boundary_jet_rank_contact_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T03:13:34.590685+00:00
-- url     : https://prove2.me/submissions/45332461-3722-485d-8191-6dd948d4b30c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_finite_span_compression_with_point
import Theorems.Thm_WeierstrassEllipticZeta_finite_span_rank_stability_iff
import Theorems.Thm_WeierstrassEllipticZeta_rank_bounded_boundary_jet_contact_obstruction
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
              ((∑ c : Fin 2, (S c).card : ℕ) : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2 ∧
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
  have hnext := WeierstrassEllipticZeta.rank_bounded_boundary_jet_contact_obstruction G
  rcases hnext with ⟨C, hC, hbound⟩
  refine ⟨C + 2, by linarith, ?_⟩
  intro m n U hm hn hU X hX Q hQ hlocal hdegree hcharts
  rcases hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts with hjet | hperiod
  · obtain ⟨a, hvalid, S, hcount, hzero, hrank⟩ := hjet
    let j (c : Fin 2) (d : Fin 4 →₀ ℕ)
        (x : {z : X // a z = c}) (k : Fin ((U : ℕ) + 1)) :=
      MvPolynomial.eval (extensionChartCoordinates G.S c x.val.val)
        ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k.val]
          (MvPolynomial.monomial d 1))
    have hcomp (c : Fin 2) := WeierstrassEllipticZeta.finite_span_compression_with_point
      ℂ ({z : X // a z = c} → Fin ((U : ℕ) + 1) → ℂ) (Fin 4 →₀ ℕ)
      (j c) (S c) 0 (hzero c)
    choose T hsub hTzero hspan hcard using hcomp
    have hold (c : Fin 2) :=
      (WeierstrassEllipticZeta.finite_span_rank_stability_iff
        ℂ _ _ (j c) (S c) _).mpr (hrank c)
    refine Or.inl ⟨a, hvalid, T, ?_, hTzero, ?_⟩
    · let r (c : Fin 2) := Module.finrank ℂ
        (Submodule.span ℂ (j c '' (S c : Set (Fin 4 →₀ ℕ))))
      have hsum : (∑ c : Fin 2, (T c).card) ≤ (∑ c : Fin 2, r c) + 2 := by
        calc
          _ ≤ ∑ c : Fin 2, (r c + 1) := Finset.sum_le_sum (fun c _ => hcard c)
          _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      have hsum' : ((∑ c : Fin 2, (T c).card : ℕ) : ℝ) ≤
          ((∑ c : Fin 2, r c : ℕ) : ℝ) + 2 := by exact_mod_cast hsum
      change ((∑ c : Fin 2, r c : ℕ) : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2 at hcount
      have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hmn : (1 : ℝ) ≤ (m : ℝ) * (n : ℝ) ^ 2 := by
        calc
          1 = (1 : ℝ) * 1 := by norm_num
          _ ≤ (m : ℝ) * (n : ℝ) ^ 2 :=
            mul_le_mul hm' (one_le_pow₀ hn') (by norm_num) (by positivity)
      nlinarith
    · intro c
      apply (WeierstrassEllipticZeta.finite_span_rank_stability_iff
        ℂ _ _ (j c) (T c) _).mp
      intro e he
      rw [hspan c]
      by_cases heS : e ∈ S c
      · exact Submodule.subset_span ⟨e, heS, rfl⟩
      · apply hold c e
        refine Finset.mem_sdiff.mpr ⟨?_, heS⟩
        obtain ⟨i, hi, heI⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp he).1
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp heI
        exact Finset.mem_biUnion.mpr
          ⟨i, hi, Finset.mem_image.mpr ⟨d, hsub c hd, rfl⟩⟩
  · exact Or.inr (hperiod.trans
      (mul_le_mul_of_nonneg_right (show C ≤ C + 2 by linarith) (sq_nonneg (n : ℝ))))
