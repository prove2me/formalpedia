-- Prove2me | solution 1 for SpilloverDuopoly.Switchers.Supplement.theorem_D3_refuted
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:21:12.170517+00:00
-- url     : https://prove2.me/submissions/578e1d82-cacd-41d1-85f1-0a4d10c3d662

import Mathlib
import Definitions.Def_ImbalPricing_IsPureNash
import Definitions.Def_SpilloverDuopoly_Switchers_Supplement_PricingGames

open SpilloverDuopoly
open SpilloverDuopoly.Switchers
open SpilloverDuopoly.Switchers.Supplement

/-- Refutation of Theorem D.3 as printed (p. 55, PDF 57). Take `T = N = 2`,
`c = δ = 0`, and independent normal valuations with common mean `mu` and standard
deviation one (`ρ = 0`). Since only first-period profit has positive weight, the
symmetric price game is exactly `zeroDiscountProfit`. No finite mean threshold can
guarantee a symmetric equilibrium with strictly positive overall profit for both firms.
Every admissible tie rule is allowed, including unequal shares.
The normal law does not appear in this reduced game: before trial its mean is the only
consumer valuation, and learning and all second-period profits receive weight zero. -/
theorem solution :
    ¬ ∃ threshold : ℝ, ∀ mu : ℝ, threshold ≤ mu →
      ∃ G : FirstPeriod (Fin 2), G.Standing ∧ G.c = 0 ∧ G.delta = 0 ∧
        G.V = mu ∧ G.u0 = 0 ∧ ∃ p : ℝ,
          ImbalPricing.IsPureNash (fun _ : Fin 2 => Set.univ)
            (fun i q => zeroDiscountProfit G q i) (fun _ => p) ∧
          ∀ i : Fin 2, 0 < zeroDiscountProfit G (fun _ => p) i := by
            classical
            rintro ⟨threshold, hthreshold⟩
            obtain ⟨G, hG, hc, hd, hV, hu, p, hnash, hpos⟩ :=
              hthreshold threshold le_rfl
            have hnonneg : ∀ S j, 0 ≤ G.tie S j := hG.2.2.2.1
            have hsum : ∀ S : Finset (Fin 2), S.Nonempty → ∑ j ∈ S, G.tie S j = 1 :=
              hG.2.2.2.2
            have hmem : (0 : Fin 2) ∈ G.best (fun _ => p) := by
              by_contra h
              have hz : zeroDiscountProfit G (fun _ => p) 0 = 0 := by
                simp [zeroDiscountProfit, FirstPeriod.share, h]
              have := hpos 0
              rw [hz] at this
              exact lt_irrefl _ this
            have hacc : G.u0 ≤ G.V - p := by
              simp only [FirstPeriod.best, Finset.mem_filter] at hmem
              exact hmem.2.1
            have hbest : G.best (fun _ : Fin 2 => p) = Finset.univ := by
              ext j
              simp [FirstPeriod.best, hacc]
            have hprofit : ∀ i : Fin 2,
                zeroDiscountProfit G (fun _ => p) i = G.tie Finset.univ i * p := by
              intro i
              simp [zeroDiscountProfit, FirstPeriod.share, hbest]
            have hp : 0 < p := by
              have h0 := hpos 0
              rw [hprofit] at h0
              have hn := hnonneg Finset.univ 0
              nlinarith
            have ht1 : 0 < G.tie Finset.univ (1 : Fin 2) := by
              have h1 := hpos 1
              rw [hprofit] at h1
              exact (mul_pos_iff_of_pos_right hp).mp h1
            have ht : G.tie Finset.univ (0 : Fin 2) + G.tie Finset.univ (1 : Fin 2) = 1 := by
              have hs := hsum Finset.univ (by simp)
              simpa [Fin.sum_univ_two] using hs
            have ht0 : G.tie Finset.univ (0 : Fin 2) < 1 := by linarith
            have hmargin : G.tie Finset.univ (0 : Fin 2) * p < p := by nlinarith
            let q : ℝ := (G.tie Finset.univ (0 : Fin 2) * p + p) / 2
            have hqp : q < p := by dsimp [q]; linarith
            have hqprofit : G.tie Finset.univ (0 : Fin 2) * p < q := by
              dsimp [q]
              linarith
            have hqacc : G.u0 ≤ G.V - q := by linarith
            have hbestq : G.best (Function.update (fun _ : Fin 2 => p) 0 q) = {0} := by
              ext j
              fin_cases j <;>
                simp [FirstPeriod.best, Fin.forall_fin_two, hqacc, le_of_lt hqp,
                  not_le_of_gt hqp]
            have hsingle : G.tie {0} (0 : Fin 2) = 1 := by
              simpa using hsum {0} (by simp)
            have hdev : zeroDiscountProfit G
                (Function.update (fun _ : Fin 2 => p) 0 q) 0 = q := by
              simp [zeroDiscountProfit, FirstPeriod.share, hbestq, hsingle]
            have hn := hnash.2 (0 : Fin 2) q (Set.mem_univ q)
            change zeroDiscountProfit G (Function.update (fun _ : Fin 2 => p) 0 q) 0 ≤
              zeroDiscountProfit G (fun _ => p) 0 at hn
            rw [hdev, hprofit] at hn
            exact (not_le_of_gt hqprofit) hn
