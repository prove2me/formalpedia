-- Prove2me | solution 1 for RevenueOrdered.UDPmin.udpmin_reduction
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T04:17:41.992285+00:00
-- url     : https://prove2.me/submissions/c4089f30-f631-459a-ba1b-04d93b79d9eb

import Mathlib
import Definitions.Def_RevenueOrdered_UDPmin_Reduction
import Theorems.Thm_RevenueOrdered_UDPmin_exists_optimal_valuation_prices
import Theorems.Thm_RevenueOrdered_UDPmin_reduction_isRegular
import Theorems.Thm_RevenueOrdered_UDPmin_rev_eq_revenue_priceOf
import Theorems.Thm_RevenueOrdered_UDPmin_rev_assortOf_eq_revenue

open RevenueOrdered.UDPmin
local notation "IsRegular" => RevenueOrdered.UDPmin.IsRegular

private theorem priceOf_pos {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M]
    (I : Instance X M) (S : Finset (RedProd I)) (x : X) : 0 < priceOf I S x := by
  classical
  unfold priceOf
  split_ifs with h
  · obtain ⟨y,hy,he⟩ := Finset.mem_image.mp (Finset.min'_mem _ h)
    obtain ⟨i,hi,hiv⟩ := Finset.mem_image.mp y.2.property
    rw [← he,← hiv]
    exact I.v_pos i
  · unfold priceTop
    have hsum : 0 ≤ ∑ i,I.v i := Finset.sum_nonneg (fun i hi => (I.v_pos i).le)
    linarith

private theorem threshold_assort {X M : Type*} [Fintype X] [DecidableEq X]
    [Fintype M] [Nonempty M] (I : Instance X M) (i : M) :
    thresholdSet (redRev I) ((Fintype.card M : ℝ)*I.v i) = assortOf I (fun _ => I.v i) := by
  classical
  have hc : 0 < (Fintype.card M : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold thresholdSet assortOf
  apply Finset.filter_congr
  intro y hy
  exact mul_le_mul_iff_right₀ hc

theorem solution {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M] [Nonempty M]
    (I : Instance X M) :
    IsRegular (redP I) ∧
    (∀ y : RedProd I, 0 < redRev I y) ∧
    RevenueOrdered.Ratio.opt (redP I) (redRev I) = optUDP I ∧
    (∀ i : M, RevenueOrdered.Tightness.rev (redP I) (redRev I)
        (thresholdSet (redRev I) ((Fintype.card M : ℝ) * I.v i)) = revenue I (fun _ => I.v i)) ∧
    (∀ y : RedProd I, ∃ i : M, RevenueOrdered.Tightness.rev (redP I) (redRev I)
        (thresholdSet (redRev I) (redRev I y)) = revenue I (fun _ => I.v i)) := by
  classical
  have hc : 0 < (Fintype.card M : ℝ) := by exact_mod_cast Fintype.card_pos
  have hr (y : RedProd I) : 0 < redRev I y := by
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp y.2.property
    exact mul_pos hc (he ▸ I.v_pos i)
  have ht (i : M) : RevenueOrdered.Tightness.rev (redP I) (redRev I)
      (thresholdSet (redRev I) ((Fintype.card M : ℝ)*I.v i)) = revenue I (fun _ => I.v i) := by
    rw [threshold_assort]
    exact rev_assortOf_eq_revenue I _ (fun x => ⟨i,rfl⟩)
  refine ⟨reduction_isRegular I,hr,?_,ht,?_⟩
  · obtain ⟨p,hp,hdom,hopt⟩ := exists_optimal_valuation_prices I
    apply le_antisymm
    · unfold RevenueOrdered.Ratio.opt
      apply Finset.sup'_le
      intro S hS
      change RevenueOrdered.Tightness.rev (redP I) (redRev I) S ≤ optUDP I
      rw [rev_eq_revenue_priceOf,← hopt]
      exact hdom _ (priceOf_pos I S)
    · rw [← hopt,← rev_assortOf_eq_revenue I p hp]
      exact Finset.le_sup' (RevenueOrdered.Ratio.revenue (redP I) (redRev I))
        (Finset.mem_univ (assortOf I p))
  · intro y
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp y.2.property
    refine ⟨i,?_⟩
    simpa only [redRev,← he] using ht i
