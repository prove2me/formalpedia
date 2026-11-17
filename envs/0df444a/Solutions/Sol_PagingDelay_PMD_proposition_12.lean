-- Prove2me | solution 1 for PagingDelay.PMD.proposition_12
-- status  : ACCEPTED   (prove)
-- author  : @licsth
-- created : 2026-11-16T12:33:30.770904+00:00
-- url     : https://prove2.me/submissions/f9dc2c35-a0db-4350-bb0f-6d5c9186467e

import Mathlib
import Definitions.Def_PagingDelay_PMD_Algorithm
import Theorems.Thm_PagingDelay_PMD_lemma_3
import Theorems.Thm_PagingDelay_PMD_proposition_7
import Theorems.Thm_PagingDelay_PMD_proposition_11
/-!
# Proposition 12 from Lemma 3, Proposition 7 and Proposition 11

Pure arithmetic: with `F ≤ cF + len`, `D ≤ F + 5 len` and `len ≤ 3 cF + 3 W`,
`F + D ≤ 23 cF + 21 W`. The three facts are hypotheses, so that the platform solution can take
them from the (imported) platform statements.
-/

namespace PagingDelay.PMD.Sim

open PagingDelay.PMD

theorem proposition_12_of (n k : ℕ) (w : Fin n → ℝ) (hw : PMDWeights w)
    (O₀ : Finset (Fin n)) (e : Instance n → Execution n)
    (ρ c : ℝ) (hc : 0 ≤ c)
    (h3 : ∀ σ : Instance n, ValidInstance σ →
      criticalLength k w (e σ) ≤ 3 * criticalFetch w (e σ) + 3 * ∑ i, w i)
    (h7 : ∀ σ : Instance n, ValidInstance σ →
      fractionalFetch w (e σ) ≤ criticalFetch w (e σ) + criticalLength k w (e σ))
    (h11 : ∀ σ : Instance n, ValidInstance σ →
      fractionalDelay k (e σ) σ ≤
        ENNReal.ofReal (fractionalFetch w (e σ) + 5 * criticalLength k w (e σ)))
    (hbound : ∀ σ : Instance n, ValidInstance σ →
      ENNReal.ofReal (criticalFetch w (e σ)) ≤
        ENNReal.ofReal ρ * optimum k w O₀ σ + ENNReal.ofReal c) :
    ∀ σ : Instance n, ValidInstance σ →
      ENNReal.ofReal (fractionalFetch w (e σ)) + fractionalDelay k (e σ) σ ≤
      ENNReal.ofReal (23 * ρ) * optimum k w O₀ σ + ENNReal.ofReal (23 * c + 21 * ∑ i, w i) := by
  intro σ hσ
  have hw0 : ∀ i, 0 ≤ w i := fun i => by obtain ⟨m, hm⟩ := hw.1 i; rw [hm]; positivity
  have hsum : ∀ l : List (Move n), 0 ≤ (l.map (stepFetch w)).sum := fun l =>
    List.sum_nonneg fun x hx => by
      obtain ⟨m, -, rfl⟩ := List.mem_map.1 hx
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (le_max_left _ _)
  set F := fractionalFetch w (e σ)
  set cF := criticalFetch w (e σ)
  set len := criticalLength k w (e σ)
  set W := ∑ i, w i
  have hF : 0 ≤ F := hsum _
  have hcF : 0 ≤ cF := hsum _
  have hW : 0 ≤ W := Finset.sum_nonneg fun i _ => hw0 i
  have hlen := le_max_left len 0
  have hL : max len 0 ≤ 3 * cF + 3 * W := max_le (h3 σ hσ) (by positivity)
  calc ENNReal.ofReal F + fractionalDelay k (e σ) σ
      ≤ ENNReal.ofReal F + ENNReal.ofReal (F + 5 * max len 0) := by
        gcongr; exact (h11 σ hσ).trans (ENNReal.ofReal_le_ofReal (by linarith))
    _ ≤ ENNReal.ofReal (23 * cF + 21 * W) := by
        rw [← ENNReal.ofReal_add hF (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith [h7 σ hσ])
    _ = 23 * ENNReal.ofReal cF + ENNReal.ofReal (21 * W) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num)]
        norm_num
    _ ≤ 23 * (ENNReal.ofReal ρ * optimum k w O₀ σ + ENNReal.ofReal c) + ENNReal.ofReal (21 * W) := by
        gcongr; exact hbound σ hσ
    _ = ENNReal.ofReal (23 * ρ) * optimum k w O₀ σ + ENNReal.ofReal (23 * c + 21 * W) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num)]
        norm_num; ring

end PagingDelay.PMD.Sim

open PagingDelay.PMD in
theorem solution (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (w : Fin n → ℝ) (hw : PMDWeights w)
    (O₀ : Finset (Fin n)) (hO₀ : O₀.card = k)
    (i₀ : Fin n) (hi₀ : i₀ ∉ O₀) (π : Fin n ≃ Fin n)
    (ρ c : ℝ) (hρ : 0 ≤ ρ) (hc : 0 ≤ c)
    (hbound : ∀ σ : Instance n, ValidInstance σ →
      ENNReal.ofReal (criticalFetch w (run k w O₀ i₀ π σ)) ≤
        ENNReal.ofReal ρ * optimum k w O₀ σ + ENNReal.ofReal c) :
    ∀ σ : Instance n, ValidInstance σ →
      ENNReal.ofReal (fractionalFetch w (run k w O₀ i₀ π σ)) +
        fractionalDelay k (run k w O₀ i₀ π σ) σ ≤
      ENNReal.ofReal (23 * ρ) * optimum k w O₀ σ +
        ENNReal.ofReal (23 * c + 21 * ∑ i, w i) :=
  PagingDelay.PMD.Sim.proposition_12_of n k w hw O₀ (run k w O₀ i₀ π) ρ c hc
    (fun σ hσ => lemma_3 n k hk hkn w hw O₀ hO₀ i₀ hi₀ π σ hσ)
    (fun σ hσ => proposition_7 n k hk hkn w hw O₀ hO₀ i₀ hi₀ π σ hσ)
    (fun σ hσ => proposition_11 n k hk hkn w hw O₀ hO₀ i₀ hi₀ π σ hσ) hbound
