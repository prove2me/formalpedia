-- Prove2me | solution 1 for SharedVehicleApprox.Pricing.Supplement.theorem_34
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:08:46.91518+00:00
-- url     : https://prove2.me/submissions/9af6ae68-f8e9-44f1-ab6e-1fcb51fd3ddf

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_StationaryLaw
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_SupplyRedirection
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_Algorithm3
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_NoPricing
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_TravelTimes
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_RedirectionTravelTimes

open Finset QueueingFundamentals.Networks

open SharedVehicleApprox
open SharedVehicleApprox.Pricing
open SharedVehicleApprox.Pricing.Supplement

/-- Theorem 34, p. 40 (corrected: the routing of `r̃` is strongly connected unless `q̃ = 0`; the
rate-limit misprint of Algorithm 9 is repaired): without prices, with travel times and `m ≥ 100`,
let `r̃` be the output of Algorithm 9. Then (1) the printed ratio bound holds for the least upper
bound `Opt_m` of the objectives of state-dependent policies whenever `Opt_m ≠ 0`; (2) if `q̃ ≠ 0`
or the total reward rate at each origin is nonnegative, the approximation guarantee holds in product form. -/
theorem solution {n m : ℕ} (hm : 100 ≤ m) (φ τ : Fin n → Fin n → ℝ)
    (hφ : ∀ i j, 0 ≤ φ i j) (hτ : ∀ i j, 0 < τ i j)
    (I c : Fin n → Fin n → ℝ) (qt : Fin n → ℝ) (zt rt : Fin n → Fin n → ℝ)
    (hopt : IsAlg9Optimal φ τ I c m qt zt) (hrt : rt = noPriceRedirectProb φ qt zt)
    (hconn : SupportConnected (inducedDemand φ (fun _ _ => 1) rt) (fun _ _ => 1) ∨ qt = 0)
    (πt : RTState n → ℝ) (hπt : IsRTStationary n m φ τ (toRTPolicy rt) πt) :
    (∀ Opt : ℝ,
      IsLUB {v : ℝ | ∃ r π, IsRTPolicy n m r ∧ IsRTStationary n m φ τ r π ∧
        v = rtObj n m φ τ I c r π} Opt →
      Opt ≠ 0 → delayFactor n m ≤ rtObj n m φ τ I c (toRTPolicy rt) πt / Opt) ∧
      ((qt ≠ 0 ∨ ∀ i, 0 ≤ ∑ j, φ i j * I i j) →
        ∀ (r : RTState n → Fin n → Fin n → Fin n → ℝ) (π : RTState n → ℝ),
          IsRTPolicy n m r → IsRTStationary n m φ τ r π →
            delayFactor n m * max (rtObj n m φ τ I c r π) 0 ≤
              rtObj n m φ τ I c (toRTPolicy rt) πt) := by
                classical
                have pU : ∀ (φ τ I c : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j) (hτ : ∀ i j, 0 < τ i j)
                    (r : RTState n → Fin n → Fin n → Fin n → ℝ) (π : RTState n → ℝ)
                    (hr : IsRTPolicy n m r) (hπ : IsRTStationary n m φ τ r π),
                    ∃ q z, IsAlg9Feasible φ τ m q z ∧ alg8Obj φ I c q z = rtObj n m φ τ I c r π := by
                  intro φ τ I c hφ hτ r π hr hπ
                  clear * - φ τ I c hφ hτ r π hr hπ
                  have hmem : ∀ t : RTState n, t ∈ rtStates n m ↔
                      (∑ i, t.1 i) + (∑ i, ∑ j, t.2.1 i j) + (∑ i, ∑ j, t.2.2 i j) = m := by
                    intro t
                    unfold rtStates
                    rw [mem_filter, mem_product, mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset,
                      Fintype.mem_piFinset]
                    constructor
                    · exact fun h => h.2
                    · intro h
                      refine ⟨⟨fun i => ?_, fun i => Fintype.mem_piFinset.2 fun j => ?_,
                        fun i => Fintype.mem_piFinset.2 fun j => ?_⟩, h⟩
                      · rw [mem_range]; have := single_le_sum (fun i _ => Nat.zero_le (t.1 i)) (mem_univ i); omega
                      · rw [mem_range]; have h1 := single_le_sum (fun j _ => Nat.zero_le (t.2.1 i j)) (mem_univ j)
                        have h2 := single_le_sum (fun i _ => Nat.zero_le (∑ j, t.2.1 i j)) (mem_univ i); omega
                      · rw [mem_range]; have h1 := single_le_sum (fun j _ => Nat.zero_le (t.2.2 i j)) (mem_univ j)
                        have h2 := single_le_sum (fun i _ => Nat.zero_le (∑ j, t.2.2 i j)) (mem_univ i); omega
                  have hLU : ∀ i j : Fin n, (∑ a, ∑ b, linkUnit i j a b) = 1 := by
                    intro i j
                    simp only [linkUnit, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
                      Finset.mem_univ, if_true]
                  have sxm : ∀ (x : Fin n → ℕ) k, 0 < x k → (∑ a, (x - Pi.single k 1 : Fin n → ℕ) a) + 1 = ∑ a, x a := by
                    intro x k hk
                    have : ∀ a, x a = (x - Pi.single k 1 : Fin n → ℕ) a + (Pi.single k 1 : Fin n → ℕ) a := by
                      intro a; rw [Pi.sub_apply]; by_cases ha : a = k
                      · subst ha; rw [Pi.single_eq_same]; omega
                      · rw [Pi.single_eq_of_ne ha]; omega
                    rw [Finset.sum_congr rfl (fun a _ => this a), Finset.sum_add_distrib, Finset.sum_pi_single',
                      if_pos (Finset.mem_univ k)]
                  have sxp : ∀ (x : Fin n → ℕ) k, (∑ a, (x + Pi.single k 1 : Fin n → ℕ) a) = (∑ a, x a) + 1 := by
                    intro x k; simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ, if_true]
                  have syp : ∀ (y : Fin n → Fin n → ℕ) k i, (∑ a, ∑ b, (y + linkUnit k i : Fin n → Fin n → ℕ) a b) = (∑ a, ∑ b, y a b) + 1 := by
                    intro y k i; simp only [Pi.add_apply, Finset.sum_add_distrib, hLU]
                  have sym : ∀ (y : Fin n → Fin n → ℕ) k i, 0 < y k i → (∑ a, ∑ b, (y - linkUnit k i : Fin n → Fin n → ℕ) a b) + 1 = ∑ a, ∑ b, y a b := by
                    intro y k i hy
                    have : ∀ a b, y a b = (y - linkUnit k i : Fin n → Fin n → ℕ) a b + linkUnit k i a b := by
                      intro a b; simp only [Pi.sub_apply, linkUnit]
                      split_ifs with h
                      · obtain ⟨rfl, rfl⟩ := h; omega
                      · omega
                    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => this a b))]
                    simp only [Finset.sum_add_distrib, hLU]
                  have T1 : ∀ s ∈ rtStates n m, ∀ k i, 0 < s.1 k →
                      ((s.1 - Pi.single k 1, s.2.1 + linkUnit k i, s.2.2) : RTState n) ∈ rtStates n m := by
                    intro s hs k i h; rw [hmem] at hs ⊢; dsimp only
                    have := sxm s.1 k h; rw [syp]; omega
                  have T2 : ∀ s ∈ rtStates n m, ∀ k i, 0 < s.2.1 k i →
                      ((s.1 + Pi.single i 1, s.2.1 - linkUnit k i, s.2.2) : RTState n) ∈ rtStates n m := by
                    intro s hs k i h; rw [hmem] at hs ⊢; dsimp only
                    have := sym s.2.1 k i h; rw [sxp]; omega
                  have T3 : ∀ s ∈ rtStates n m, ∀ k i j, 0 < s.2.1 k i →
                      ((s.1, s.2.1 - linkUnit k i, s.2.2 + linkUnit i j) : RTState n) ∈ rtStates n m := by
                    intro s hs k i j h; rw [hmem] at hs ⊢; dsimp only
                    have := sym s.2.1 k i h; rw [syp]; omega
                  have T4 : ∀ s ∈ rtStates n m, ∀ k i, 0 < s.2.2 k i →
                      ((s.1 + Pi.single i 1, s.2.1, s.2.2 - linkUnit k i) : RTState n) ∈ rtStates n m := by
                    intro s hs k i h; rw [hmem] at hs ⊢; dsimp only
                    have := sym s.2.2 k i h; rw [sxp]; omega
                  have hgen : ∀ (g : RTState n → ℝ), ∀ s ∈ rtStates n m,
                      (∑ t ∈ rtStates n m, rtRate φ τ r s t * (g t - g s)) =
                        ∑ k, ∑ i, ((if 0 < s.1 k then φ k i *
                            (g (s.1 - Pi.single k 1, s.2.1 + linkUnit k i, s.2.2) - g s) else 0) +
                          (s.2.1 k i : ℝ) / τ k i *
                            ((1 - ∑ j, r s k i j) * (g (s.1 + Pi.single i 1, s.2.1 - linkUnit k i, s.2.2) - g s) +
                              ∑ j, r s k i j * (g (s.1, s.2.1 - linkUnit k i, s.2.2 + linkUnit i j) - g s)) +
                          (s.2.2 k i : ℝ) / τ k i * (g (s.1 + Pi.single i 1, s.2.1, s.2.2 - linkUnit k i) - g s)) := by
                    intro g s hs
                    unfold rtRate; rw [Finset.sum_congr rfl fun t _ => (Finset.sum_mul _ _ _).trans (Finset.sum_congr rfl fun k _ => Finset.sum_mul _ _ _)]
                    rw [Finset.sum_comm]
                    refine Finset.sum_congr rfl fun k _ => Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ => ?_)
                    rw [Finset.sum_congr rfl fun t _ => add_mul _ _ _, Finset.sum_add_distrib,
                      Finset.sum_congr rfl fun t _ => add_mul _ _ _, Finset.sum_add_distrib]
                    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
                    · by_cases hx : 0 < s.1 k
                      · simp only [hx, true_and, if_true, ite_mul, zero_mul]
                        rw [Finset.sum_ite_eq' (rtStates n m), if_pos (T1 s hs k i hx)]
                      · simp only [hx, false_and, if_false, zero_mul, Finset.sum_const_zero]
                    · by_cases hy : 0 < s.2.1 k i
                      · simp only [hy, if_true, mul_add, add_mul, ite_mul, zero_mul, mul_ite, mul_zero]
                        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (rtStates n m), if_pos (T2 s hs k i hy)]
                        congr 1
                        · exact mul_assoc _ _ _
                        · simp only [Finset.mul_sum, Finset.sum_mul]
                          rw [Finset.sum_comm]
                          refine Finset.sum_congr rfl fun j _ => ?_
                          simp only [mul_ite, ite_mul, mul_zero, zero_mul]
                          rw [Finset.sum_ite_eq' (rtStates n m), if_pos (T3 s hs k i j hy)]; exact mul_assoc _ _ _
                      · have : s.2.1 k i = 0 := by omega
                        simp only [this, lt_irrefl, if_false, zero_mul, Finset.sum_const_zero, Nat.cast_zero, zero_div]
                    · by_cases he : 0 < s.2.2 k i
                      · simp only [he, true_and, ite_mul, zero_mul]
                        rw [Finset.sum_ite_eq' (rtStates n m), if_pos (T4 s hs k i he)]
                      · have : s.2.2 k i = 0 := by omega
                        simp only [this, lt_irrefl, false_and, if_false, zero_mul, Finset.sum_const_zero, Nat.cast_zero, zero_div]
                  have htest : ∀ (g : RTState n → ℝ),
                      (∑ s ∈ rtStates n m, π s * ∑ t ∈ rtStates n m, rtRate φ τ r s t * (g t - g s)) = 0 := by
                    intro g
                    have hbalance := hπ.2.2.2
                    have hb : ∀ s ∈ rtStates n m, π s * (∑ t ∈ rtStates n m, rtRate φ τ r s t) =
                        ∑ t ∈ rtStates n m, π t * rtRate φ τ r t s := by
                      intro s hs
                      have := hbalance ⟨s, hs⟩
                      simp only [tsum_fintype] at this
                      rw [← Finset.sum_coe_sort (rtStates n m) (fun t => rtRate φ τ r s t),
                        ← Finset.sum_coe_sort (rtStates n m) (fun t => π t * rtRate φ τ r t s)]
                      exact this
                    have e1 : (∑ s ∈ rtStates n m, π s * ∑ t ∈ rtStates n m, rtRate φ τ r s t * (g t - g s)) =
                        (∑ s ∈ rtStates n m, ∑ t ∈ rtStates n m, π s * rtRate φ τ r s t * g t) -
                          ∑ s ∈ rtStates n m, g s * (π s * ∑ t ∈ rtStates n m, rtRate φ τ r s t) := by
                      rw [← Finset.sum_sub_distrib]
                      refine Finset.sum_congr rfl fun s _ => ?_
                      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
                      refine Finset.sum_congr rfl fun t _ => ?_
                      rw [mul_sub, mul_sub, ← mul_assoc, ← mul_assoc, mul_comm (g s)]
                    have e2 : (∑ s ∈ rtStates n m, g s * (π s * ∑ t ∈ rtStates n m, rtRate φ τ r s t)) =
                        ∑ s ∈ rtStates n m, ∑ t ∈ rtStates n m, π s * rtRate φ τ r s t * g t := by
                      rw [Finset.sum_congr rfl (fun s hs => by rw [hb s hs])]
                      simp only [Finset.mul_sum]
                      rw [Finset.sum_comm]
                      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => mul_comm _ _
                    rw [e1, e2, sub_self]
                  have cxm : ∀ (x : Fin n → ℕ) k a, 0 < x k →
                      (((x - Pi.single k 1 : Fin n → ℕ) a : ℕ) : ℝ) = (x a : ℝ) - if a = k then 1 else 0 := by
                    intro x k a hk
                    by_cases ha : a = k
                    · subst ha; rw [Pi.sub_apply, Pi.single_eq_same, if_pos rfl, Nat.cast_sub (by omega), Nat.cast_one]
                    · rw [Pi.sub_apply, Pi.single_eq_of_ne ha, Nat.sub_zero, if_neg ha, sub_zero]
                  have cxp : ∀ (x : Fin n → ℕ) k a,
                      (((x + Pi.single k 1 : Fin n → ℕ) a : ℕ) : ℝ) = (x a : ℝ) + if a = k then 1 else 0 := by
                    intro x k a
                    by_cases ha : a = k
                    · subst ha; rw [Pi.add_apply, Pi.single_eq_same, if_pos rfl, Nat.cast_add, Nat.cast_one]
                    · rw [Pi.add_apply, Pi.single_eq_of_ne ha, if_neg ha, Nat.add_zero, add_zero]
                  have cyp : ∀ (y : Fin n → Fin n → ℕ) k i a b,
                      (((y + linkUnit k i : Fin n → Fin n → ℕ) a b : ℕ) : ℝ) =
                        (y a b : ℝ) + if a = k ∧ b = i then 1 else 0 := by
                    intro y k i a b
                    simp only [Pi.add_apply, linkUnit]
                    split_ifs <;> simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
                  have cym : ∀ (y : Fin n → Fin n → ℕ) k i a b, 0 < y k i →
                      (((y - linkUnit k i : Fin n → Fin n → ℕ) a b : ℕ) : ℝ) =
                        (y a b : ℝ) - if a = k ∧ b = i then 1 else 0 := by
                    intro y k i a b h
                    simp only [Pi.sub_apply, linkUnit]
                    split_ifs with hab
                    · obtain ⟨rfl, rfl⟩ := hab; rw [Nat.cast_sub (by omega), Nat.cast_one]
                    · simp only [Nat.sub_zero, sub_zero]
                  have IY : ∀ a b, ∑ s ∈ rtStates n m, π s * ((if 0 < s.1 a then φ a b else 0) - (s.2.1 a b : ℝ) / τ a b) = 0 := by
                    intro a b
                    refine Eq.trans ?_ (htest (fun t => (t.2.1 a b : ℝ)))
                    refine Finset.sum_congr rfl fun s hs => ?_
                    rw [hgen _ s hs]
                    refine congrArg (π s * ·) ?_
                    have hC : ((if 0 < s.1 a then φ a b else 0) - (s.2.1 a b : ℝ) / τ a b) = ∑ k, ∑ i,
                        if k = a ∧ i = b then ((if 0 < s.1 a then φ a b else 0) - (s.2.1 a b : ℝ) / τ a b) else 0 := by
                      simp only [Finset.sum_sub_distrib, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
                    rw [hC]
                    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
                    dsimp only
                    rw [cyp]
                    by_cases hki : k = a ∧ i = b
                    · obtain ⟨rfl, rfl⟩ := hki
                      by_cases hy : 0 < s.2.1 k i
                      · rw [cym _ _ _ _ _ hy]
                        simp only [and_self, if_true, add_sub_cancel_left, sub_sub_cancel_left, mul_one, sub_self,
                          mul_zero, add_zero, mul_neg, Finset.sum_neg_distrib]
                        ring
                      · have h0 : s.2.1 k i = 0 := by omega
                        simp only [h0, and_self, if_true, Nat.cast_zero, zero_div,
                          zero_mul, sub_self, mul_zero, sub_zero, add_zero, zero_add, mul_one]
                    · have hab : ¬ (a = k ∧ b = i) := fun h => hki ⟨h.1.symm, h.2.symm⟩
                      have hD : (((s.2.1 - linkUnit k i : Fin n → Fin n → ℕ) a b : ℕ) : ℝ) = s.2.1 a b := by
                        simp only [Pi.sub_apply, linkUnit, if_neg hab, Nat.sub_zero]
                      rw [hD, if_neg hab, if_neg hki]
                      simp only [add_zero, sub_self, mul_zero, Finset.sum_const_zero, ite_self]
                  have IE : ∀ a b, ∑ s ∈ rtStates n m, π s *
                      ((∑ k, (s.2.1 k a : ℝ) / τ k a * r s k a b) - (s.2.2 a b : ℝ) / τ a b) = 0 := by
                    intro a b
                    refine Eq.trans ?_ (htest (fun t => (t.2.2 a b : ℝ)))
                    refine Finset.sum_congr rfl fun s hs => ?_
                    rw [hgen _ s hs]
                    refine congrArg (π s * ·) ?_
                    have hC : ((∑ k, (s.2.1 k a : ℝ) / τ k a * r s k a b) - (s.2.2 a b : ℝ) / τ a b) = ∑ k, ∑ i,
                        ((if i = a then (s.2.1 k a : ℝ) / τ k a * r s k a b else 0) -
                          if k = a ∧ i = b then (s.2.2 a b : ℝ) / τ a b else 0) := by
                      simp only [Finset.sum_sub_distrib, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
                    rw [hC]
                    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
                    dsimp only
                    simp only [sub_self, mul_zero, ite_self, zero_add]
                    have h2 : ∑ j, r s k i j * ((((s.2.2 + linkUnit i j : Fin n → Fin n → ℕ) a b : ℕ) : ℝ) - (s.2.2 a b : ℝ))
                        = if i = a then r s k a b else 0 := by
                      simp only [cyp, add_sub_cancel_left, mul_ite, mul_one, mul_zero, ite_and]
                      simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
                      by_cases hia : a = i
                      · subst hia; rfl
                      · rw [if_neg hia, if_neg (Ne.symm hia)]
                    rw [h2]
                    have h3 : (s.2.2 k i : ℝ) / τ k i * ((((s.2.2 - linkUnit k i : Fin n → Fin n → ℕ) a b : ℕ) : ℝ) - (s.2.2 a b : ℝ))
                        = -(if k = a ∧ i = b then (s.2.2 a b : ℝ) / τ a b else 0) := by
                      by_cases hki : k = a ∧ i = b
                      · obtain ⟨rfl, rfl⟩ := hki
                        by_cases he : 0 < s.2.2 k i
                        · rw [cym _ _ _ _ _ he, sub_sub_cancel_left, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, mul_neg, mul_one]
                        · have h0 : s.2.2 k i = 0 := by omega
                          simp only [h0, Nat.cast_zero, zero_div, zero_mul, and_self, if_true, neg_zero]
                      · have hab : ¬ (a = k ∧ b = i) := fun h => hki ⟨h.1.symm, h.2.symm⟩
                        simp only [Pi.sub_apply, linkUnit, if_neg hab, Nat.sub_zero, sub_self, mul_zero, if_neg hki, neg_zero]
                    rw [h3]
                    by_cases hia : i = a
                    · subst hia; rw [if_pos rfl, if_pos rfl, sub_eq_add_neg]
                    · rw [if_neg hia, if_neg hia, mul_zero, zero_sub, zero_add]
                  have IX : ∀ a, ∑ s ∈ rtStates n m, π s *
                      ((∑ k, ((s.2.1 k a : ℝ) / τ k a * (1 - ∑ j, r s k a j) + (s.2.2 k a : ℝ) / τ k a)) -
                        ∑ i, (if 0 < s.1 a then φ a i else 0)) = 0 := by
                    intro a
                    refine Eq.trans ?_ (htest (fun t => (t.1 a : ℝ)))
                    refine Finset.sum_congr rfl fun s hs => ?_
                    rw [hgen _ s hs]
                    refine congrArg (π s * ·) ?_
                    have hC : ((∑ k, ((s.2.1 k a : ℝ) / τ k a * (1 - ∑ j, r s k a j) + (s.2.2 k a : ℝ) / τ k a)) -
                        ∑ i, (if 0 < s.1 a then φ a i else 0)) = ∑ k, ∑ i,
                        ((if i = a then (s.2.1 k a : ℝ) / τ k a * (1 - ∑ j, r s k a j) + (s.2.2 k a : ℝ) / τ k a else 0) -
                          if k = a then (if 0 < s.1 a then φ a i else 0) else 0) := by
                      simp only [Finset.sum_sub_distrib, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
                    rw [hC]
                    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
                    dsimp only
                    simp only [sub_self, mul_zero, Finset.sum_const_zero, add_zero, cxp, add_sub_cancel_left]
                    have h1 : (if 0 < s.1 k then φ k i * ((((s.1 - Pi.single k 1 : Fin n → ℕ) a : ℕ) : ℝ) - (s.1 a : ℝ)) else 0)
                        = -(if k = a then (if 0 < s.1 a then φ a i else 0) else 0) := by
                      by_cases hx : 0 < s.1 k
                      · rw [if_pos hx, cxm _ _ _ hx, sub_sub_cancel_left]
                        by_cases hka : k = a
                        · subst hka; simp only [if_true, if_pos hx, mul_neg, mul_one]
                        · simp only [if_neg (Ne.symm hka), if_neg hka, neg_zero, mul_zero]
                      · rw [if_neg hx]
                        by_cases hka : k = a
                        · subst hka; simp only [if_true, if_neg hx, neg_zero]
                        · simp only [if_neg hka, neg_zero]
                    rw [h1]
                    by_cases hia : i = a
                    · subst hia; simp only [if_true]; ring
                    · simp only [if_neg hia, if_neg (Ne.symm hia)]; ring
                  clear hgen htest cxm cxp cyp cym T1 T2 T3 T4 sxm sxp syp sym hLU
                  obtain ⟨hπ0, -, hπ1, -⟩ := hπ
                  refine ⟨fun a => ∑ s ∈ rtStates n m, π s * (if 0 < s.1 a then 1 else 0),
                    fun i j => ∑ s ∈ rtStates n m, π s * ∑ k, (s.2.1 k i : ℝ) / τ k i * r s k i j, ?_, ?_⟩
                  · have key : ∀ (A B : RTState n → ℝ), ∑ s ∈ rtStates n m, π s * (A s - B s) = 0 →
                        ∑ s ∈ rtStates n m, π s * A s = ∑ s ∈ rtStates n m, π s * B s := by
                      intro A B h
                      rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← h]
                      exact Finset.sum_congr rfl fun s _ => (mul_sub _ _ _).symm
                    have hY : ∀ a b, φ a b * (∑ s ∈ rtStates n m, π s * (if 0 < s.1 a then 1 else 0)) =
                        ∑ s ∈ rtStates n m, π s * ((s.2.1 a b : ℝ) / τ a b) := by
                      intro a b
                      rw [← key _ _ (IY a b), Finset.mul_sum]
                      refine Finset.sum_congr rfl fun s _ => ?_
                      by_cases hp : 0 < s.1 a
                      · rw [if_pos hp, if_pos hp, mul_one, mul_comm]
                      · simp only [if_neg hp, mul_zero]
                    have hE : ∀ a b, (∑ s ∈ rtStates n m, π s * ∑ k, (s.2.1 k a : ℝ) / τ k a * r s k a b) =
                        ∑ s ∈ rtStates n m, π s * ((s.2.2 a b : ℝ) / τ a b) := fun a b => key _ _ (IE a b)
                    have hX : ∀ a, ∑ j, φ a j * (∑ s ∈ rtStates n m, π s * (if 0 < s.1 a then 1 else 0)) =
                        ∑ s ∈ rtStates n m, π s *
                          ∑ k, ((s.2.1 k a : ℝ) / τ k a * (1 - ∑ j, r s k a j) + (s.2.2 k a : ℝ) / τ k a) := by
                      intro a
                      rw [key _ _ (IX a)]
                      simp only [Finset.mul_sum]
                      rw [Finset.sum_comm]
                      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => ?_
                      by_cases hp : 0 < s.1 a
                      · rw [if_pos hp, if_pos hp, mul_one, mul_comm]
                      · simp only [if_neg hp, mul_zero]
                    have hyτ : ∀ s ∈ rtStates n m, ∀ k i, 0 ≤ (s.2.1 k i : ℝ) / τ k i := fun s _ k i =>
                      div_nonneg (Nat.cast_nonneg _) (hτ k i).le
                    refine ⟨⟨fun i _ => ⟨Finset.sum_nonneg fun s _ => mul_nonneg (hπ0 s) (ite_nonneg zero_le_one le_rfl), ?_⟩,
                      fun i j => Finset.sum_nonneg fun s hs => mul_nonneg (hπ0 s) (Finset.sum_nonneg fun k _ =>
                        mul_nonneg (hyτ s hs k i) ((hr s hs k i).1 j)), fun i => ?_, fun i => ?_⟩, ?_⟩
                    · exact (Finset.sum_le_sum fun s _ => mul_le_of_le_one_right (hπ0 s) (by split_ifs <;> [exact le_rfl; exact zero_le_one])).trans hπ1.le
                    · -- circulation
                      have L : ∑ k, (φ k i * (∑ s ∈ rtStates n m, π s * (if 0 < s.1 k then 1 else 0)) +
                          ∑ s ∈ rtStates n m, π s * ∑ k', (s.2.1 k' k : ℝ) / τ k' k * r s k' k i) =
                          ∑ s ∈ rtStates n m, π s * ∑ k, ((s.2.1 k i : ℝ) / τ k i + (s.2.2 k i : ℝ) / τ k i) := by
                        rw [Finset.sum_congr rfl fun k _ => (congrArg₂ (· + ·) (hY k i) (hE k i)).trans
                          Finset.sum_add_distrib.symm, Finset.sum_comm]
                        exact Finset.sum_congr rfl fun s _ => by
                          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => (mul_add _ _ _).symm
                      rw [L, Finset.sum_add_distrib, hX]
                      have R : ∑ j, ∑ s ∈ rtStates n m, π s * ∑ k, (s.2.1 k i : ℝ) / τ k i * r s k i j =
                          ∑ s ∈ rtStates n m, π s * ∑ k, (s.2.1 k i : ℝ) / τ k i * ∑ j, r s k i j := by
                        rw [Finset.sum_comm]
                        refine Finset.sum_congr rfl fun s _ => ?_
                        rw [← Finset.mul_sum, Finset.sum_comm]
                        simp only [Finset.mul_sum]
                      rw [R, ← Finset.sum_add_distrib]
                      refine Finset.sum_congr rfl fun s _ => ?_
                      rw [← mul_add, ← Finset.sum_add_distrib]
                      congr 1
                      refine Finset.sum_congr rfl fun k _ => ?_
                      ring
                    · -- redirect capacity
                      have h1 : ∑ k, ∑ s ∈ rtStates n m, π s * ∑ j, (s.2.1 j i : ℝ) / τ j i * r s j i k =
                          ∑ s ∈ rtStates n m, π s * ∑ j, (s.2.1 j i : ℝ) / τ j i * ∑ k, r s j i k := by
                        rw [Finset.sum_comm]
                        refine Finset.sum_congr rfl fun s _ => ?_
                        rw [← Finset.mul_sum, Finset.sum_comm]
                        simp only [Finset.mul_sum]
                      have h2 : ∑ j, φ j i * (∑ s ∈ rtStates n m, π s * (if 0 < s.1 j then 1 else 0)) =
                          ∑ s ∈ rtStates n m, π s * ∑ j, (s.2.1 j i : ℝ) / τ j i := by
                        rw [Finset.sum_congr rfl fun j _ => hY j i, Finset.sum_comm]
                        exact Finset.sum_congr rfl fun s _ => (Finset.mul_sum _ _ _).symm
                      rw [h1, h2]
                      refine Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_left
                        (Finset.sum_le_sum fun j _ => mul_le_of_le_one_right (hyτ s hs j i) (hr s hs j i).2) (hπ0 s)
                    · -- rate limit
                      have e : ∀ i j, τ i j * (φ i j * (∑ s ∈ rtStates n m, π s * (if 0 < s.1 i then 1 else 0)) +
                          ∑ s ∈ rtStates n m, π s * ∑ k, (s.2.1 k i : ℝ) / τ k i * r s k i j) =
                          ∑ s ∈ rtStates n m, π s * ((s.2.1 i j : ℝ) + (s.2.2 i j : ℝ)) := by
                        intro i j
                        rw [hY, hE, ← Finset.sum_add_distrib, Finset.mul_sum]
                        refine Finset.sum_congr rfl fun s _ => ?_
                        have h1 : τ i j * (τ i j)⁻¹ = 1 := mul_inv_cancel₀ (hτ i j).ne'
                        rw [div_eq_mul_inv, div_eq_mul_inv]
                        linear_combination (π s * ((s.2.1 i j : ℝ) + (s.2.2 i j : ℝ))) * h1
                      simp only [e]
                      have hpt : ∀ s ∈ rtStates n m, ∑ i, ∑ j, ((s.2.1 i j : ℝ) + (s.2.2 i j : ℝ)) ≤ m := by
                        intro s hs
                        have h2 : (∑ i, ∑ j, (s.2.1 i j + s.2.2 i j) : ℕ) ≤ m := by
                          have := (hmem s).1 hs
                          simp only [Finset.sum_add_distrib]; omega
                        have h3 := (Nat.cast_le (α := ℝ)).2 h2
                        simp only [Nat.cast_sum, Nat.cast_add] at h3
                        exact h3
                      calc ∑ i, ∑ j, ∑ s ∈ rtStates n m, π s * ((s.2.1 i j : ℝ) + (s.2.2 i j : ℝ))
                          = ∑ s ∈ rtStates n m, π s * ∑ i, ∑ j, ((s.2.1 i j : ℝ) + (s.2.2 i j : ℝ)) :=
                            ((Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm).trans
                              (Finset.sum_congr rfl fun s _ => by
                                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm)
                        _ ≤ ∑ s ∈ rtStates n m, π s * (m : ℝ) :=
                            Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (hpt s hs) (hπ0 s)
                        _ = m := by rw [← Finset.sum_mul, hπ1, one_mul]
                  · -- objective
                    unfold alg8Obj rtObj
                    rw [Finset.sum_congr rfl fun i _ => Finset.sum_sub_distrib _ _, Finset.sum_sub_distrib,
                      Finset.sum_congr rfl fun s _ => mul_sub _ _ _, Finset.sum_sub_distrib]
                    congr 1
                    · have h1 : ∀ i j, φ i j * (∑ s ∈ rtStates n m, π s * (if 0 < s.1 i then 1 else 0)) * I i j =
                          ∑ s ∈ rtStates n m, π s * (if 0 < s.1 i then φ i j * I i j else 0) := by
                        intro i j
                        rw [Finset.mul_sum, Finset.sum_mul]
                        refine Finset.sum_congr rfl fun s _ => ?_
                        by_cases hp : 0 < s.1 i
                        · rw [if_pos hp, if_pos hp, mul_one, mul_comm (φ i j), mul_assoc]
                        · simp only [if_neg hp, mul_zero, zero_mul]
                      simp only [h1]
                      refine ((Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm).trans
                        (Finset.sum_congr rfl fun s _ => ?_)
                      rw [Finset.mul_sum]
                      exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
                    · have h1 : ∀ i j, c i j * (∑ s ∈ rtStates n m, π s * ∑ k, (s.2.1 k i : ℝ) / τ k i * r s k i j) =
                          ∑ s ∈ rtStates n m, ∑ k, π s * ((s.2.1 k i : ℝ) / τ k i * (r s k i j * c i j)) := by
                        intro i j
                        rw [Finset.mul_sum]
                        refine Finset.sum_congr rfl fun s _ => ?_
                        rw [Finset.mul_sum, Finset.mul_sum]
                        exact Finset.sum_congr rfl fun k _ => by ring
                      simp only [h1]
                      refine ((Finset.sum_congr rfl fun i _ => Finset.sum_comm.trans
                        (Finset.sum_congr rfl fun s _ => Finset.sum_comm)).trans Finset.sum_comm).trans
                        (Finset.sum_congr rfl fun s _ => ?_)
                      rw [Finset.sum_comm, Finset.mul_sum]
                      refine Finset.sum_congr rfl fun k _ => ?_
                      rw [Finset.mul_sum]
                      refine Finset.sum_congr rfl fun i _ => ?_
                      rw [Finset.mul_sum, Finset.mul_sum]
                have pPF1 : ∀ (φ τ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j) (hτ : ∀ i j, 0 < τ i j)
                    (ρ : Fin n → ℝ) (z R : Fin n → Fin n → ℝ)
                    (hρ : ∀ k, 0 ≤ ρ k) (hR : ∀ i j, 0 ≤ R i j) (hR1 : ∀ i, ∑ j, R i j ≤ 1)
                    (hz : ∀ i j, z i j = R i j * ∑ k, φ k i * ρ k)
                    (hcirc : ∀ i, ∑ k, (φ k i * ρ k + z k i) = ∑ j, (φ i j * ρ i + z i j))
                    (ν : RTState n → ℝ)
                    (hν : ∀ s : RTState n, ν s = (∏ k, ρ k ^ s.1 k) *
                      ((∏ a, ∏ b, (τ a b * φ a b * ρ a) ^ s.2.1 a b / ((s.2.1 a b).factorial : ℝ)) *
                       (∏ a, ∏ b, (τ a b * z a b) ^ s.2.2 a b / ((s.2.2 a b).factorial : ℝ)))),
                    ∀ s ∈ rtStates n m, ν s * ∑ t ∈ rtStates n m, rtRate φ τ (toRTPolicy R) s t =
                      ∑ t ∈ rtStates n m, ν t * rtRate φ τ (toRTPolicy R) t s := by
                  intro φ τ hφ hτ ρ z R hρ hR hR1 hz hcirc ν hν
                  clear * - hτ hz hcirc hν
                  have hLUii : ∀ i j : Fin n, linkUnit i j i j = 1 := fun i j => if_pos ⟨rfl, rfl⟩
                  have hLU : ∀ i j : Fin n, (∑ a, ∑ b, linkUnit i j a b) = 1 := by
                    intro i j
                    have hz0 : ∀ a b, ¬(a = i ∧ b = j) → linkUnit i j a b = 0 := fun a b h => if_neg h
                    rw [Fintype.sum_eq_single i (fun a ha => Finset.sum_eq_zero fun b _ => hz0 a b fun h => ha h.1),
                      Fintype.sum_eq_single j (fun b hb => hz0 i b fun h => hb h.2)]
                    exact hLUii i j
                  have hpx : ∀ (x : Fin n → ℕ) k, 0 < (x + Pi.single k 1 : Fin n → ℕ) k := fun x k => by
                    rw [Pi.add_apply, Pi.single_eq_same]; exact Nat.succ_pos _
                  have hpy : ∀ (y : Fin n → Fin n → ℕ) k i, 0 < (y + linkUnit k i : Fin n → Fin n → ℕ) k i :=
                    fun y k i => by rw [Pi.add_apply, Pi.add_apply, hLUii]; exact Nat.succ_pos _
                  have hSle : ∀ (x : Fin n → ℕ) (k : Fin n), 0 < x k → Pi.single k 1 ≤ x := by
                    intro x k hk a
                    by_cases ha : a = k
                    · subst ha; rw [Pi.single_eq_same]; exact hk
                    · rw [Pi.single_eq_of_ne ha]; exact Nat.zero_le _
                  have hLUle : ∀ (y : Fin n → Fin n → ℕ) (i j : Fin n), 0 < y i j → linkUnit i j ≤ y := by
                    intro y i j h a b
                    by_cases hab : a = i ∧ b = j
                    · obtain ⟨rfl, rfl⟩ := hab; rw [hLUii]; exact h
                    · rw [show linkUnit i j a b = 0 from if_neg hab]; exact Nat.zero_le _
                  have hx1 : ∀ (x : Fin n → ℕ) k, 0 < x k → x - Pi.single k 1 + Pi.single k 1 = x :=
                    fun x k h => tsub_add_cancel_of_le (hSle x k h)
                  have hx2 : ∀ (x : Fin n → ℕ) k, x + Pi.single k 1 - Pi.single k 1 = x :=
                    fun x k => add_tsub_cancel_right _ _
                  have hy1 : ∀ (y : Fin n → Fin n → ℕ) k i, 0 < y k i → y - linkUnit k i + linkUnit k i = y :=
                    fun y k i h => tsub_add_cancel_of_le (hLUle y k i h)
                  have hy2 : ∀ (y : Fin n → Fin n → ℕ) k i, y + linkUnit k i - linkUnit k i = y :=
                    fun y k i => add_tsub_cancel_right _ _
                  have hsx : ∀ (x : Fin n → ℕ) k, ∑ a, (x + Pi.single k 1 : Fin n → ℕ) a = ∑ a, x a + 1 := by
                    intro x k; simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single',
                      Finset.mem_univ, if_true]
                  have hsy : ∀ (y : Fin n → Fin n → ℕ) k i, ∑ a, ∑ b, (y + linkUnit k i : Fin n → Fin n → ℕ) a b = ∑ a, ∑ b, y a b + 1 := by
                    intro y k i; simp only [Pi.add_apply, Finset.sum_add_distrib, hLU]
                  have hmemIff : ∀ t : RTState n, t ∈ rtStates n m ↔
                      (∑ i, t.1 i) + (∑ i, ∑ j, t.2.1 i j) + (∑ i, ∑ j, t.2.2 i j) = m := by
                    intro t
                    unfold rtStates
                    rw [mem_filter, mem_product, mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset,
                      Fintype.mem_piFinset]
                    constructor
                    · exact fun h => h.2
                    · intro h
                      refine ⟨⟨fun i => ?_, fun i => Fintype.mem_piFinset.2 fun j => ?_,
                        fun i => Fintype.mem_piFinset.2 fun j => ?_⟩, h⟩
                      · rw [mem_range]; have := single_le_sum (fun i _ => Nat.zero_le (t.1 i)) (mem_univ i); omega
                      · rw [mem_range]; have h1 := single_le_sum (fun j _ => Nat.zero_le (t.2.1 i j)) (mem_univ j)
                        have h2 := single_le_sum (fun i _ => Nat.zero_le (∑ j, t.2.1 i j)) (mem_univ i); omega
                      · rw [mem_range]; have h1 := single_le_sum (fun j _ => Nat.zero_le (t.2.2 i j)) (mem_univ j)
                        have h2 := single_le_sum (fun i _ => Nat.zero_le (∑ j, t.2.2 i j)) (mem_univ i); omega

                  have hfadd : ∀ (W : Fin n → Fin n → ℝ) (y : Fin n → Fin n → ℕ) (i j : Fin n),
                      (∏ a, ∏ b, W a b ^ ((y + linkUnit i j) a b) / (((y + linkUnit i j) a b).factorial : ℝ)) *
                        ((y i j : ℝ) + 1) = (∏ a, ∏ b, W a b ^ (y a b) / ((y a b).factorial : ℝ)) * W i j := by
                    intro W y i j
                    have pt : ∀ a b, W a b ^ ((y + linkUnit i j) a b) /
                        (((y + linkUnit i j) a b).factorial : ℝ) =
                        (W a b ^ (y a b) / ((y a b).factorial : ℝ)) *
                          (if a = i then (if b = j then W i j / ((y i j : ℝ) + 1) else 1) else 1) := by
                      intro a b
                      by_cases h : a = i ∧ b = j
                      · obtain ⟨rfl, rfl⟩ := h
                        simp only [Pi.add_apply, linkUnit, and_self, if_true, pow_succ, Nat.factorial_succ,
                          Nat.cast_mul, Nat.cast_add, Nat.cast_one]
                        rw [div_mul_div_comm, mul_comm ((y a b : ℝ) + 1)]
                      · have h1 : linkUnit i j a b = 0 := if_neg h
                        simp only [Pi.add_apply, h1, add_zero]
                        by_cases ha : a = i
                        · subst ha; have hb : b ≠ j := fun hb => h ⟨rfl, hb⟩; rw [if_pos rfl, if_neg hb, mul_one]
                        · rw [if_neg ha, mul_one]
                    rw [Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun b _ => pt a b))]
                    simp only [Finset.prod_mul_distrib]
                    have hp : (∏ a, ∏ b, (if a = i then (if b = j then W i j /
                        ((y i j : ℝ) + 1) else 1) else 1)) = W i j / ((y i j : ℝ) + 1) := by
                      rw [Fintype.prod_eq_single i (fun a ha => Finset.prod_eq_one fun b _ => if_neg ha)]
                      trans ∏ b, (if b = j then W i j / ((y i j : ℝ) + 1) else 1)
                      · exact Finset.prod_congr rfl fun b _ => if_pos rfl
                      · rw [Fintype.prod_eq_single j (fun b hb => if_neg hb), if_pos rfl]
                    rw [hp]
                    have : (0 : ℝ) < (y i j : ℝ) + 1 := Nat.cast_add_one_pos _
                    rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt this)]
                  have Ax : ∀ (x : Fin n → ℕ) (y e : Fin n → Fin n → ℕ) k,
                      ν (x + Pi.single k 1, y, e) = ν (x, y, e) * ρ k := by
                    intro x y e k; rw [hν, hν]
                    have : ∏ a, ρ a ^ (x + Pi.single k 1 : Fin n → ℕ) a = (∏ a, ρ a ^ x a) * ρ k := by
                      have h1 : ∏ a, ρ a ^ (Pi.single k 1 : Fin n → ℕ) a = ρ k := by
                        rw [Fintype.prod_eq_single k (fun a ha => by rw [Pi.single_eq_of_ne ha, pow_zero]),
                          Pi.single_eq_same, pow_one]
                      simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
                      rw [h1]
                    dsimp only; rw [this]; ring
                  have Ay : ∀ (x : Fin n → ℕ) (y e : Fin n → Fin n → ℕ) k i,
                      ν (x, y + linkUnit k i, e) * ((y k i : ℝ) + 1) = ν (x, y, e) * (τ k i * φ k i * ρ k) := by
                    intro x y e k i; rw [hν, hν]
                    have := hfadd (fun a b => τ a b * φ a b * ρ a) y k i
                    dsimp only at this ⊢
                    linear_combination ((∏ a, ρ a ^ x a) *
                      (∏ a, ∏ b, (τ a b * z a b) ^ e a b / ((e a b).factorial : ℝ))) * this
                  have Ae : ∀ (x : Fin n → ℕ) (y e : Fin n → Fin n → ℕ) k i,
                      ν (x, y, e + linkUnit k i) * ((e k i : ℝ) + 1) = ν (x, y, e) * (τ k i * z k i) := by
                    intro x y e k i; rw [hν, hν]
                    have := hfadd (fun a b => τ a b * z a b) e k i
                    dsimp only at this ⊢
                    linear_combination ((∏ a, ρ a ^ x a) *
                      (∏ a, ∏ b, (τ a b * φ a b * ρ a) ^ y a b / ((y a b).factorial : ℝ))) * this
                  have htraf : ∀ i, (∑ k, φ k i * ρ k) * (1 - ∑ j, R i j) + ∑ k, z k i = ρ i * ∑ j, φ i j := by
                    intro i
                    have h := hcirc i
                    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h
                    have hz' : ∑ j, z i j = (∑ j, R i j) * ∑ k, φ k i * ρ k := by
                      simp only [hz]; rw [Finset.sum_mul]
                    have h3 : ∑ j, φ i j * ρ i = ρ i * ∑ j, φ i j := by rw [Finset.mul_sum]; simp only [mul_comm]
                    rw [h3, hz'] at h
                    linear_combination h
                  have hpt : ∀ (H : RTState n → ℝ) (g : RTState n) (B : Prop) [Decidable B] (val : ℝ),
                      (B → g ∈ rtStates n m) → (∀ t, H t ≠ 0 → B ∧ t = g) → (B → H g = val) →
                      ∑ t ∈ rtStates n m, H t = if B then val else 0 := by
                    intro H g B _ val hg hH hv
                    split_ifs with hB
                    · rw [Finset.sum_eq_single_of_mem g (hg hB) (fun t _ hne => by
                        by_contra h; exact hne (hH t h).2)]
                      exact hv hB
                    · exact Finset.sum_eq_zero fun t _ => by by_contra h; exact hB (hH t h).1
                  clear hfadd hν hcirc
                  intro s hs
                  obtain ⟨x, y, e⟩ := s
                  have hs' := (hmemIff _).1 hs
                  dsimp only at hs'
                  have hm1 : ∀ a k i, 0 < x a →
                      ((x - Pi.single a 1, y + linkUnit k i, e) : RTState n) ∈ rtStates n m := by
                    intro a k i h; rw [hmemIff]; dsimp only; rw [hsy]
                    have h2 := hsx (x - Pi.single a 1) a; rw [hx1 _ _ h] at h2; omega
                  have hm2 : ∀ a k i, 0 < y k i →
                      ((x + Pi.single a 1, y - linkUnit k i, e) : RTState n) ∈ rtStates n m := by
                    intro a k i h; rw [hmemIff]; dsimp only; rw [hsx]
                    have h2 := hsy (y - linkUnit k i) k i; rw [hy1 _ _ _ h] at h2; omega
                  have hm3 : ∀ k i a b, 0 < y k i →
                      ((x, y - linkUnit k i, e + linkUnit a b) : RTState n) ∈ rtStates n m := by
                    intro k i a b h; rw [hmemIff]; dsimp only; rw [hsy e]
                    have h2 := hsy (y - linkUnit k i) k i; rw [hy1 _ _ _ h] at h2; omega
                  have hm3' : ∀ k i a b, 0 < e a b →
                      ((x, y + linkUnit k i, e - linkUnit a b) : RTState n) ∈ rtStates n m := by
                    intro k i a b h; rw [hmemIff]; dsimp only; rw [hsy y]
                    have h2 := hsy (e - linkUnit a b) a b; rw [hy1 _ _ _ h] at h2; omega
                  have hm4 : ∀ a k i, 0 < e k i →
                      ((x + Pi.single a 1, y, e - linkUnit k i) : RTState n) ∈ rtStates n m := by
                    intro a k i h; rw [hmemIff]; dsimp only; rw [hsx]
                    have h2 := hsy (e - linkUnit k i) k i; rw [hy1 _ _ _ h] at h2; omega
                  have hm4' : ∀ a k i, 0 < x a →
                      ((x - Pi.single a 1, y, e + linkUnit k i) : RTState n) ∈ rtStates n m := by
                    intro a k i h; rw [hmemIff]; dsimp only; rw [hsy e]
                    have h2 := hsx (x - Pi.single a 1) a; rw [hx1 _ _ h] at h2; omega

                  have hout : ∑ t ∈ rtStates n m, rtRate φ τ (toRTPolicy R) (x, y, e) t =
                      ∑ k, ∑ i, ((if 0 < x k then φ k i else 0) + (if 0 < y k i then (y k i : ℝ) / τ k i else 0) +
                        (if 0 < e k i then (e k i : ℝ) / τ k i else 0)) := by
                    unfold rtRate toRTPolicy
                    rw [Finset.sum_comm]
                    refine Finset.sum_congr rfl fun k _ => ?_
                    rw [Finset.sum_comm]
                    refine Finset.sum_congr rfl fun i _ => ?_
                    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
                    refine congrArg₂ HAdd.hAdd (congrArg₂ HAdd.hAdd ?_ ?_) ?_
                    · by_cases h : 0 < x k
                      · simp only [h, true_and, if_true]
                        rw [Finset.sum_ite_eq' (rtStates n m), if_pos (hm1 k k i h)]
                      · simp only [h, false_and, if_false, Finset.sum_const_zero]
                    · by_cases h : 0 < y k i
                      · simp only [h, if_true]
                        have hj : ∀ j, ∑ t ∈ rtStates n m,
                            (if t = (x, y - linkUnit k i, e + linkUnit i j) then R i j else 0) = R i j :=
                          fun j => by rw [Finset.sum_ite_eq' (rtStates n m), if_pos (hm3 k i i j h)]
                        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq' (rtStates n m),
                          if_pos (hm2 i k i h), Finset.sum_comm]
                        simp only [hj]
                        ring
                      · simp only [h, if_false, Finset.sum_const_zero]
                    · by_cases h : 0 < e k i
                      · simp only [h, true_and, if_true]
                        rw [Finset.sum_ite_eq' (rtStates n m), if_pos (hm4 i k i h)]
                      · simp only [h, false_and, if_false, Finset.sum_const_zero]

                  have hca : ∀ (y : Fin n → Fin n → ℕ) k i, (((y + linkUnit k i) k i : ℕ) : ℝ) = y k i + 1 := by
                    intro y k i; simp only [Pi.add_apply, hLUii]; push_cast; ring
                  have hcs : ∀ (y : Fin n → Fin n → ℕ) k i, 0 < y k i →
                      (((y - linkUnit k i) k i : ℕ) : ℝ) + 1 = y k i := by
                    intro y k i h
                    have : (y - linkUnit k i) k i + 1 = y k i := by simp only [Pi.sub_apply, hLUii]; omega
                    exact_mod_cast this
                  have hsplit : ∀ (c A D a X : ℝ) (p : Prop) [Decidable p] (Y : Fin n → ℝ),
                      c * (A + (if p then a * (X + ∑ j, Y j) else 0) + D) =
                        c * A + (c * (if p then a * X else 0) + ∑ j, c * (if p then a * Y j else 0)) + c * D := by
                    intro c A D a X p _ Y
                    split_ifs
                    · rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
                    · simp only [mul_zero, add_zero, Finset.sum_const_zero]; ring
                  have hin : ∑ t ∈ rtStates n m, ν t * rtRate φ τ (toRTPolicy R) t (x, y, e) =
                      ∑ k, ∑ i, ((if 0 < y k i then ν (x + Pi.single k 1, y - linkUnit k i, e) * φ k i else 0) +
                        ((if 0 < x i then ν (x - Pi.single i 1, y + linkUnit k i, e) * (((y k i : ℝ) + 1) / τ k i) *
                            (1 - ∑ j, R i j) else 0) +
                          ∑ j, (if 0 < e i j then ν (x, y + linkUnit k i, e - linkUnit i j) *
                            (((y k i : ℝ) + 1) / τ k i) * R i j else 0)) +
                        (if 0 < x i then ν (x - Pi.single i 1, y, e + linkUnit k i) * (((e k i : ℝ) + 1) / τ k i)
                          else 0)) := by
                    have hmul3 : ∀ (c : RTState n → ℝ) (X : RTState n → Fin n → Fin n → ℝ),
                        ∑ t ∈ rtStates n m, c t * ∑ k, ∑ i, X t k i = ∑ k, ∑ i, ∑ t ∈ rtStates n m, c t * X t k i := by
                      intro c X
                      simp only [Finset.mul_sum]
                      rw [Finset.sum_comm]
                      exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
                    unfold rtRate toRTPolicy
                    rw [hmul3]
                    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
                    simp only [hsplit]
                    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm]
                    refine congrArg₂ HAdd.hAdd (congrArg₂ HAdd.hAdd ?_ ?_) ?_
                    · refine hpt _ (x + Pi.single k 1, y - linkUnit k i, e) _ _ (fun h => hm2 k k i h) ?_ ?_
                      · intro t ht
                        beta_reduce at ht
                        split_ifs at ht with hc
                        · obtain ⟨h0, hc⟩ := hc
                          cases hc
                          exact ⟨hpy _ _ _, by rw [hx1 _ _ h0, hy2]⟩
                        · exact (ht (mul_zero _)).elim
                      · intro hB
                        rw [if_pos]
                        exact ⟨hpx _ _, by rw [hx2, hy1 _ _ _ hB]⟩
                    · refine congrArg₂ HAdd.hAdd ?_ ?_
                      · refine hpt _ (x - Pi.single i 1, y + linkUnit k i, e) _ _ (fun h => hm1 i k i h) ?_ ?_
                        · intro t ht
                          beta_reduce at ht
                          split_ifs at ht with h1 h2
                          · cases h2
                            exact ⟨hpx _ _, by rw [hx2, hy1 _ _ _ h1]⟩
                          · exact (ht (mul_eq_zero_of_right _ (mul_zero _))).elim
                          · exact (ht (mul_zero _)).elim
                        · intro hB
                          rw [if_pos (hpy _ _ _), if_pos, hca]
                          · ring
                          · rw [hx1 _ _ hB, hy2]
                      · refine Finset.sum_congr rfl fun j _ => ?_
                        refine hpt _ (x, y + linkUnit k i, e - linkUnit i j) _ _ (fun h => hm3' k i i j h) ?_ ?_
                        · intro t ht
                          beta_reduce at ht
                          split_ifs at ht with h1 h2
                          · cases h2
                            exact ⟨hpy _ _ _, by rw [hy1 _ _ _ h1, hy2]⟩
                          · exact (ht (mul_eq_zero_of_right _ (mul_zero _))).elim
                          · exact (ht (mul_zero _)).elim
                        · intro hB
                          rw [if_pos (hpy _ _ _), if_pos, hca]
                          · ring
                          · rw [hy2, hy1 _ _ _ hB]
                    · refine hpt _ (x - Pi.single i 1, y, e + linkUnit k i) _ _ (fun h => hm4' i k i h) ?_ ?_
                      · intro t ht
                        beta_reduce at ht
                        split_ifs at ht with hc
                        · obtain ⟨h0, hc⟩ := hc
                          cases hc
                          exact ⟨hpx _ _, by rw [hx2, hy1 _ _ _ h0]⟩
                        · exact (ht (mul_zero _)).elim
                      · intro hB
                        rw [if_pos, hca]
                        exact ⟨hpy _ _ _, by rw [hx1 _ _ hB, hy2]⟩

                  have E1 : ∀ k i, (if 0 < y k i then ν (x + Pi.single k 1, y - linkUnit k i, e) * φ k i else 0) =
                      ν (x, y, e) * (if 0 < y k i then (y k i : ℝ) / τ k i else 0) := by
                    intro k i
                    by_cases h : 0 < y k i
                    · rw [if_pos h, if_pos h, Ax]
                      have h1 := Ay x (y - linkUnit k i) e k i
                      rw [hy1 _ _ _ h, hcs _ _ _ h] at h1
                      rw [mul_div_assoc', h1, eq_div_iff (hτ k i).ne']; ring
                    · rw [if_neg h, if_neg h, mul_zero]
                  have E2 : ∀ i, ∑ k, ((if 0 < x i then ν (x - Pi.single i 1, y + linkUnit k i, e) *
                        (((y k i : ℝ) + 1) / τ k i) * (1 - ∑ j, R i j) else 0) +
                      (if 0 < x i then ν (x - Pi.single i 1, y, e + linkUnit k i) * (((e k i : ℝ) + 1) / τ k i)
                        else 0)) = ν (x, y, e) * ∑ j, (if 0 < x i then φ i j else 0) := by
                    intro i
                    by_cases h : 0 < x i
                    · have h0 := Ax (x - Pi.single i 1) y e i
                      rw [hx1 _ _ h] at h0
                      have hk2 : ∀ k, ν (x - Pi.single i 1, y + linkUnit k i, e) * (((y k i : ℝ) + 1) / τ k i) =
                          ν (x - Pi.single i 1, y, e) * (φ k i * ρ k) := by
                        intro k
                        rw [mul_div_assoc', Ay, div_eq_iff (hτ k i).ne']; ring
                      have hk4 : ∀ k, ν (x - Pi.single i 1, y, e + linkUnit k i) * (((e k i : ℝ) + 1) / τ k i) =
                          ν (x - Pi.single i 1, y, e) * z k i := by
                        intro k
                        rw [mul_div_assoc', Ae, div_eq_iff (hτ k i).ne']; ring
                      simp only [if_pos h, hk2, hk4]
                      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, h0]
                      linear_combination (ν (x - Pi.single i 1, y, e)) * htraf i
                    · simp only [if_neg h, add_zero, Finset.sum_const_zero, mul_zero]
                  have E3 : ∀ i j, ∑ k, (if 0 < e i j then ν (x, y + linkUnit k i, e - linkUnit i j) *
                        (((y k i : ℝ) + 1) / τ k i) * R i j else 0) =
                      ν (x, y, e) * (if 0 < e i j then (e i j : ℝ) / τ i j else 0) := by
                    intro i j
                    by_cases h : 0 < e i j
                    · have h0 := Ae x y (e - linkUnit i j) i j
                      rw [hy1 _ _ _ h, hcs _ _ _ h] at h0
                      have hk : ∀ k, ν (x, y + linkUnit k i, e - linkUnit i j) * (((y k i : ℝ) + 1) / τ k i) =
                          ν (x, y, e - linkUnit i j) * (φ k i * ρ k) := by
                        intro k
                        rw [mul_div_assoc', Ay, div_eq_iff (hτ k i).ne']; ring
                      simp only [if_pos h, hk]
                      rw [← Finset.sum_mul, ← Finset.mul_sum, mul_div_assoc', h0, eq_div_iff (hτ i j).ne', hz i j]
                      ring
                    · simp only [if_neg h, Finset.sum_const_zero, mul_zero]
                  rw [hout, hin]
                  have F1 : ∑ k, ∑ i, (if 0 < y k i then ν (x + Pi.single k 1, y - linkUnit k i, e) * φ k i
                      else 0) = ∑ k, ∑ i, ν (x, y, e) * (if 0 < y k i then (y k i : ℝ) / τ k i else 0) :=
                    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => E1 k i
                  have F2 : ∑ k, ∑ i, ((if 0 < x i then ν (x - Pi.single i 1, y + linkUnit k i, e) *
                        (((y k i : ℝ) + 1) / τ k i) * (1 - ∑ j, R i j) else 0) +
                      (if 0 < x i then ν (x - Pi.single i 1, y, e + linkUnit k i) * (((e k i : ℝ) + 1) / τ k i)
                        else 0)) = ∑ k, ∑ i, ν (x, y, e) * (if 0 < x k then φ k i else 0) := by
                    rw [Finset.sum_comm]
                    exact Finset.sum_congr rfl fun i _ => by rw [E2 i, Finset.mul_sum]
                  have F3 : ∑ k, ∑ i, ∑ j, (if 0 < e i j then ν (x, y + linkUnit k i, e - linkUnit i j) *
                        (((y k i : ℝ) + 1) / τ k i) * R i j else 0) =
                      ∑ k, ∑ i, ν (x, y, e) * (if 0 < e k i then (e k i : ℝ) / τ k i else 0) := by
                    rw [Finset.sum_comm]
                    refine Finset.sum_congr rfl fun i _ => ?_
                    rw [Finset.sum_comm]
                    exact Finset.sum_congr rfl fun j _ => E3 i j
                  have hs2 : ∀ A B : Fin n → Fin n → ℝ,
                      ∑ k, ∑ i, (A k i + B k i) = ∑ k, ∑ i, A k i + ∑ k, ∑ i, B k i := by
                    intro A B; simp only [Finset.sum_add_distrib]
                  have hs3 : ∀ A B C : Fin n → Fin n → ℝ, ∑ k, ∑ i, (A k i + B k i + C k i) =
                      ∑ k, ∑ i, A k i + ∑ k, ∑ i, B k i + ∑ k, ∑ i, C k i := by
                    intro A B C; simp only [Finset.sum_add_distrib]
                  have hs4 : ∀ (A B D : Fin n → Fin n → ℝ) (C : Fin n → Fin n → Fin n → ℝ),
                      ∑ k, ∑ i, (A k i + (B k i + ∑ j, C k i j) + D k i) =
                      ∑ k, ∑ i, A k i + ∑ k, ∑ i, B k i + ∑ k, ∑ i, ∑ j, C k i j + ∑ k, ∑ i, D k i := by
                    intro A B D C; simp only [Finset.sum_add_distrib, add_assoc]
                  have hmul : ∀ (c : ℝ) (X : Fin n → Fin n → ℝ), c * ∑ k, ∑ i, X k i = ∑ k, ∑ i, c * X k i := by
                    intro c X; simp only [Finset.mul_sum]
                  rw [hs2] at F2
                  rw [hs3, mul_add, mul_add, hmul, hmul, hmul, hs4]
                  linear_combination -(F1 + F2 + F3)
                have pPF2 : ∀ (φ τ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j) (hτ : ∀ i j, 0 < τ i j)
                    (ρ : Fin n → ℝ) (z R : Fin n → Fin n → ℝ)
                    (hρ : ∀ k, 0 < ρ k) (hR : ∀ i j, 0 ≤ R i j) (hR1 : ∀ i, ∑ j, R i j ≤ 1)
                    (hz : ∀ i j, z i j = R i j * ∑ k, φ k i * ρ k)
                    (hcirc : ∀ i, ∑ k, (φ k i * ρ k + z k i) = ∑ j, (φ i j * ρ i + z i j))
                    (hconn : SupportConnected (inducedDemand φ (fun _ _ => 1) R) (fun _ _ => 1))
                    (ν : RTState n → ℝ)
                    (hν : ∀ s : RTState n, ν s = (∏ k, ρ k ^ s.1 k) *
                      ((∏ a, ∏ b, (τ a b * φ a b * ρ a) ^ s.2.1 a b / ((s.2.1 a b).factorial : ℝ)) *
                       (∏ a, ∏ b, (τ a b * z a b) ^ s.2.2 a b / ((s.2.2 a b).factorial : ℝ))))
                    (hbal : ∀ s ∈ rtStates n m, ν s * ∑ t ∈ rtStates n m, rtRate φ τ (toRTPolicy R) s t =
                      ∑ t ∈ rtStates n m, ν t * rtRate φ τ (toRTPolicy R) t s)
                    (π : RTState n → ℝ) (hπ : IsRTStationary n m φ τ (toRTPolicy R) π),
                    ∀ s ∈ rtStates n m, π s * ∑ t ∈ rtStates n m, ν t = ν s := by
                  intro φ τ hφ hτ ρ z R hρ hR hR1 hz hcirc hconn ν hν hbal π hπ
                  clear * - φ τ hφ hτ ρ z R hρ hR hR1 hz hcirc hconn ν hν hbal π hπ
                  obtain ⟨K, hK⟩ : ∃ K : RTState n → RTState n → ℝ, K = rtRate φ τ (toRTPolicy R) := ⟨_, rfl⟩
                  have hb : ∀ s ∈ rtStates n m, π s * (∑ t ∈ rtStates n m, K s t) =
                      ∑ t ∈ rtStates n m, π t * K t s := by
                    intro s hs
                    have := hπ.2.2.2 ⟨s, hs⟩
                    simp only [tsum_fintype] at this
                    rw [hK, ← Finset.sum_coe_sort (rtStates n m) (fun t => rtRate φ τ (toRTPolicy R) s t),
                      ← Finset.sum_coe_sort (rtStates n m) (fun t => π t * rtRate φ τ (toRTPolicy R) t s)]
                    exact this
                  rw [← hK] at hbal
                  have hsum1 : ∑ t ∈ rtStates n m, π t = 1 := hπ.2.2.1
                  clear hπ
                  rcases Nat.eq_zero_or_pos n with hn | hn
                  · intro s hs
                    have hSt1 : rtStates n m = {s} :=
                      Finset.eq_singleton_iff_unique_mem.2 ⟨hs, fun t _ => Prod.ext
                        (funext fun i => by subst hn; exact i.elim0)
                        (Prod.ext (funext fun i => by subst hn; exact i.elim0)
                          (funext fun i => by subst hn; exact i.elim0))⟩
                    rw [hSt1, Finset.sum_singleton] at hsum1 ⊢
                    rw [hsum1, one_mul]
                  obtain ⟨i0, -⟩ : ∃ i0 : Fin n, True := ⟨⟨0, hn⟩, trivial⟩
                  -- membership
                  have hmemIff : ∀ t : RTState n, t ∈ rtStates n m ↔
                      (∑ i, t.1 i) + (∑ i, ∑ j, t.2.1 i j) + (∑ i, ∑ j, t.2.2 i j) = m := by
                    intro t
                    simp only [rtStates, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset,
                      Finset.mem_range]
                    constructor
                    · exact fun h => h.2
                    · intro ht
                      have hB1 : ∀ a A b c : ℕ, a ≤ A → A + b + c = m → a < m + 1 := fun a A b c h1 h2 =>
                        Nat.lt_succ_of_le (h1.trans (le_of_le_of_eq ((Nat.le_add_right A b).trans
                          (Nat.le_add_right _ c)) h2))
                      have hB2 : ∀ a a' A b c : ℕ, a ≤ a' → a' ≤ A → b + A + c = m → a < m + 1 :=
                        fun a a' A b c h1 h2 h3 => Nat.lt_succ_of_le (h1.trans (h2.trans (le_of_le_of_eq
                          ((Nat.le_add_left A b).trans (Nat.le_add_right _ c)) h3)))
                      have hB3 : ∀ a a' A b c : ℕ, a ≤ a' → a' ≤ A → b + c + A = m → a < m + 1 :=
                        fun a a' A b c h1 h2 h3 => Nat.lt_succ_of_le (h1.trans (h2.trans (le_of_le_of_eq
                          (Nat.le_add_left A (b + c)) h3)))
                      refine ⟨⟨fun i => ?_, fun i j => ?_, fun i j => ?_⟩, ht⟩
                      · exact hB1 _ _ _ _ (Finset.single_le_sum (f := t.1) (fun _ _ => Nat.zero_le _)
                          (Finset.mem_univ i)) ht
                      · exact hB2 _ _ _ _ _ (Finset.single_le_sum (f := t.2.1 i) (fun _ _ => Nat.zero_le _)
                          (Finset.mem_univ j)) (Finset.single_le_sum (f := fun i => ∑ j, t.2.1 i j)
                          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) ht
                      · exact hB3 _ _ _ _ _ (Finset.single_le_sum (f := t.2.2 i) (fun _ _ => Nat.zero_le _)
                          (Finset.mem_univ j)) (Finset.single_le_sum (f := fun i => ∑ j, t.2.2 i j)
                          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) ht
                  have hLU : ∀ i j : Fin n, (∑ a, ∑ b, linkUnit i j a b) = 1 := by
                    intro i j
                    rw [Fintype.sum_eq_single (f := fun a => ∑ b, linkUnit i j a b) i (fun a ha =>
                        Finset.sum_eq_zero fun b _ => (if_neg fun h => ha h.1 : linkUnit i j a b = 0)),
                      Fintype.sum_eq_single (f := fun b => linkUnit i j i b) j
                        (fun b hb => (if_neg fun h => hb h.2 : linkUnit i j i b = 0))]
                    exact (if_pos ⟨rfl, rfl⟩ : linkUnit i j i j = 1)
                  have hSle : ∀ (x : Fin n → ℕ) (k : Fin n), 0 < x k → Pi.single k 1 ≤ x := by
                    intro x k hk a
                    by_cases ha : a = k
                    · subst ha; rw [Pi.single_eq_same]; exact hk
                    · rw [Pi.single_eq_of_ne ha]; exact Nat.zero_le _
                  have sxsub : ∀ (x : Fin n → ℕ) k, 0 < x k → (∑ p, (x - Pi.single k 1 : Fin n → ℕ) p) + 1 = ∑ p, x p := by
                    intro x k hk
                    conv_rhs => rw [← tsub_add_cancel_of_le (hSle x k hk)]
                    simp only [Pi.add_apply]
                    rw [Finset.sum_add_distrib, Finset.sum_pi_single', if_pos (Finset.mem_univ k)]
                  have sxadd : ∀ (x : Fin n → ℕ) k, (∑ p, (x + Pi.single k 1 : Fin n → ℕ) p) = (∑ p, x p) + 1 := by
                    intro x k; simp only [Pi.add_apply]
                    rw [Finset.sum_add_distrib, Finset.sum_pi_single', if_pos (Finset.mem_univ k)]
                  have syadd : ∀ (y : Fin n → Fin n → ℕ) k i,
                      (∑ a, ∑ b, (y + linkUnit k i : Fin n → Fin n → ℕ) a b) = (∑ a, ∑ b, y a b) + 1 := by
                    intro y k i; simp only [Pi.add_apply, Finset.sum_add_distrib, hLU]
                  have sysub : ∀ (y : Fin n → Fin n → ℕ) k i, 0 < y k i →
                      (∑ a, ∑ b, (y - linkUnit k i : Fin n → Fin n → ℕ) a b) + 1 = ∑ a, ∑ b, y a b := by
                    intro y k i h
                    have : ∀ a b, y a b = (y - linkUnit k i : Fin n → Fin n → ℕ) a b + linkUnit k i a b := by
                      intro a b; simp only [Pi.sub_apply, linkUnit]
                      split_ifs with hh
                      · obtain ⟨rfl, rfl⟩ := hh; exact (Nat.sub_add_cancel h).symm
                      · rfl
                    conv_rhs => rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => this a b))]
                    simp only [Finset.sum_add_distrib, hLU]
                  have hA1 : ∀ a a' b b' c : ℕ, a' + 1 = a → b' = b + 1 → a + b + c = m → a' + b' + c = m := by
                    intro a a' b b' c h1 h2 h3; subst h1 h2
                    exact (congrArg (· + c) (Nat.add_right_comm a' 1 b)).symm.trans h3
                  have hA2 : ∀ a a' b b' c : ℕ, a' = a + 1 → b' + 1 = b → a + b + c = m → a' + b' + c = m := by
                    intro a a' b b' c h1 h2 h3; subst h1 h2
                    exact (congrArg (· + c) (Nat.add_right_comm a 1 b')).trans h3
                  have hA3 : ∀ a b b' c c' : ℕ, b' + 1 = b → c' = c + 1 → a + b + c = m → a + b' + c' = m := by
                    intro a b b' c c' h1 h2 h3; subst h1 h2
                    exact (Nat.add_right_comm (a + b') 1 c).symm.trans h3
                  have hA4 : ∀ a a' b c c' : ℕ, a' = a + 1 → c' + 1 = c → a + b + c = m → a' + b + c' = m := by
                    intro a a' b c c' h1 h2 h3; subst h1 h2
                    exact (congrArg (· + c') (Nat.add_right_comm a 1 b)).trans
                      ((Nat.add_right_comm (a + b) 1 c').trans h3)
                  have hA5 : ∀ a a' a'' b c : ℕ, a' + 1 = a → a'' = a' + 1 → a + b + c = m → a'' + b + c = m := by
                    intro a a' a'' b c h1 h2 h3; subst h1 h2; exact h3
                  have mride : ∀ s ∈ rtStates n m, ∀ k i, 0 < s.1 k →
                      ((s.1 - Pi.single k 1, s.2.1 + linkUnit k i, s.2.2) : RTState n) ∈ rtStates n m := by
                    intro s hs k i hk
                    rw [hmemIff] at hs ⊢
                    exact hA1 _ _ _ _ _ (sxsub s.1 k hk) (syadd s.2.1 k i) hs
                  have mstay : ∀ s ∈ rtStates n m, ∀ k i, 0 < s.2.1 k i →
                      ((s.1 + Pi.single i 1, s.2.1 - linkUnit k i, s.2.2) : RTState n) ∈ rtStates n m := by
                    intro s hs k i hk
                    rw [hmemIff] at hs ⊢
                    exact hA2 _ _ _ _ _ (sxadd s.1 i) (sysub s.2.1 k i hk) hs
                  have mredir : ∀ s ∈ rtStates n m, ∀ k i j, 0 < s.2.1 k i →
                      ((s.1, s.2.1 - linkUnit k i, s.2.2 + linkUnit i j) : RTState n) ∈ rtStates n m := by
                    intro s hs k i j hk
                    rw [hmemIff] at hs ⊢
                    exact hA3 _ _ _ _ _ (sysub s.2.1 k i hk) (syadd s.2.2 i j) hs
                  have marr : ∀ s ∈ rtStates n m, ∀ k i, 0 < s.2.2 k i →
                      ((s.1 + Pi.single i 1, s.2.1, s.2.2 - linkUnit k i) : RTState n) ∈ rtStates n m := by
                    intro s hs k i hk
                    rw [hmemIff] at hs ⊢
                    exact hA4 _ _ _ _ _ (sxadd s.1 i) (sysub s.2.2 k i hk) hs
                  -- the rate, piece by piece
                  obtain ⟨A, hAd⟩ : ∃ A : RTState n → RTState n → Fin n → Fin n → ℝ, A = fun s t k i =>
                      if 0 < s.1 k ∧ t = (s.1 - Pi.single k 1, s.2.1 + linkUnit k i, s.2.2) then φ k i else 0 :=
                    ⟨_, rfl⟩
                  obtain ⟨B1, hB1d⟩ : ∃ B1 : RTState n → RTState n → Fin n → Fin n → ℝ, B1 = fun s t k i =>
                      if t = (s.1 + Pi.single i 1, s.2.1 - linkUnit k i, s.2.2) then 1 - ∑ j, R i j else 0 :=
                    ⟨_, rfl⟩
                  obtain ⟨B2, hB2d⟩ : ∃ B2 : RTState n → RTState n → Fin n → Fin n → ℝ, B2 = fun s t k i =>
                      ∑ j, if t = (s.1, s.2.1 - linkUnit k i, s.2.2 + linkUnit i j) then R i j else 0 :=
                    ⟨_, rfl⟩
                  obtain ⟨B, hBd⟩ : ∃ B : RTState n → RTState n → Fin n → Fin n → ℝ, B = fun s t k i =>
                      if 0 < s.2.1 k i then (s.2.1 k i : ℝ) / τ k i * (B1 s t k i + B2 s t k i) else 0 :=
                    ⟨_, rfl⟩
                  obtain ⟨C, hCd⟩ : ∃ C : RTState n → RTState n → Fin n → Fin n → ℝ, C = fun s t k i =>
                      if 0 < s.2.2 k i ∧ t = (s.1 + Pi.single i 1, s.2.1, s.2.2 - linkUnit k i) then
                        (s.2.2 k i : ℝ) / τ k i else 0 := ⟨_, rfl⟩
                  have hKd : ∀ s t, K s t = ∑ k, ∑ i, (A s t k i + B s t k i + C s t k i) := by
                    intro s t; rw [hK, hAd, hBd, hB1d, hB2d, hCd]; rfl
                  have hA0 : ∀ s t k i, 0 ≤ A s t k i := by
                    intro s t k i; rw [hAd]; dsimp only; split_ifs
                    · exact hφ k i
                    · exact le_refl _
                  have hB10 : ∀ s t k i, 0 ≤ B1 s t k i := by
                    intro s t k i; rw [hB1d]; dsimp only; split_ifs
                    · exact sub_nonneg.2 (hR1 i)
                    · exact le_refl _
                  have hB20 : ∀ s t k i, 0 ≤ B2 s t k i := by
                    intro s t k i; rw [hB2d]
                    exact Finset.sum_nonneg fun j _ => by
                      split_ifs
                      · exact hR i j
                      · exact le_refl _
                  have hB0 : ∀ s t k i, 0 ≤ B s t k i := by
                    intro s t k i; rw [hBd]; dsimp only; split_ifs
                    · exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (hτ k i).le)
                        (add_nonneg (hB10 s t k i) (hB20 s t k i))
                    · exact le_refl _
                  have hC0 : ∀ s t k i, 0 ≤ C s t k i := by
                    intro s t k i; rw [hCd]; dsimp only; split_ifs
                    · exact div_nonneg (Nat.cast_nonneg _) (hτ k i).le
                    · exact le_refl _
                  have hT0 : ∀ s t k i, 0 ≤ A s t k i + B s t k i + C s t k i := fun s t k i =>
                    add_nonneg (add_nonneg (hA0 s t k i) (hB0 s t k i)) (hC0 s t k i)
                  have hKge : ∀ s t k i, A s t k i + B s t k i + C s t k i ≤ K s t := by
                    intro s t k i; rw [hKd]
                    exact le_trans (Finset.single_le_sum (f := fun i => A s t k i + B s t k i + C s t k i)
                      (fun i _ => hT0 s t k i) (Finset.mem_univ i))
                      (Finset.single_le_sum (f := fun k => ∑ i, (A s t k i + B s t k i + C s t k i))
                        (fun k _ => Finset.sum_nonneg fun i _ => hT0 s t k i) (Finset.mem_univ k))
                  have hride : ∀ (s : RTState n) k i, 0 < s.1 k → 0 < φ k i →
                      0 < K s (s.1 - Pi.single k 1, s.2.1 + linkUnit k i, s.2.2) := by
                    intro s k i hk hp
                    refine lt_of_lt_of_le ?_ (hKge _ _ k i)
                    have : A s (s.1 - Pi.single k 1, s.2.1 + linkUnit k i, s.2.2) k i = φ k i := by
                      rw [hAd]; exact if_pos ⟨hk, rfl⟩
                    rw [this]
                    exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hp (hB0 _ _ k i)) (hC0 _ _ k i)
                  have hstay : ∀ (s : RTState n) k i, 0 < s.2.1 k i → ∑ j, R i j < 1 →
                      0 < K s (s.1 + Pi.single i 1, s.2.1 - linkUnit k i, s.2.2) := by
                    intro s k i hk hlt
                    refine lt_of_lt_of_le ?_ (hKge _ _ k i)
                    have h1 : B1 s (s.1 + Pi.single i 1, s.2.1 - linkUnit k i, s.2.2) k i = 1 - ∑ j, R i j := by
                      rw [hB1d]; exact if_pos rfl
                    have h2 : 0 < B s (s.1 + Pi.single i 1, s.2.1 - linkUnit k i, s.2.2) k i := by
                      rw [hBd]; dsimp only; rw [if_pos hk, h1]
                      exact mul_pos (div_pos (Nat.cast_pos.2 hk) (hτ k i))
                        (add_pos_of_pos_of_nonneg (sub_pos.2 hlt) (hB20 _ _ k i))
                    exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos (hA0 _ _ k i) h2) (hC0 _ _ k i)
                  have hredir : ∀ (s : RTState n) k i j, 0 < s.2.1 k i → 0 < R i j →
                      0 < K s (s.1, s.2.1 - linkUnit k i, s.2.2 + linkUnit i j) := by
                    intro s k i j hk hj
                    refine lt_of_lt_of_le ?_ (hKge _ _ k i)
                    have h1 : R i j ≤ B2 s (s.1, s.2.1 - linkUnit k i, s.2.2 + linkUnit i j) k i := by
                      rw [hB2d]; dsimp only
                      refine le_trans (le_of_eq (if_pos rfl).symm) (Finset.single_le_sum
                        (f := fun j' => if ((s.1, s.2.1 - linkUnit k i, s.2.2 + linkUnit i j) : RTState n) =
                          (s.1, s.2.1 - linkUnit k i, s.2.2 + linkUnit i j') then R i j' else 0)
                        (fun j' _ => ?_) (Finset.mem_univ j))
                      split_ifs
                      · exact hR i j'
                      · exact le_refl _
                    have h2 : 0 < B s (s.1, s.2.1 - linkUnit k i, s.2.2 + linkUnit i j) k i := by
                      rw [hBd]; dsimp only; rw [if_pos hk]
                      exact mul_pos (div_pos (Nat.cast_pos.2 hk) (hτ k i))
                        (add_pos_of_nonneg_of_pos (hB10 _ _ k i) (lt_of_lt_of_le hj h1))
                    exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos (hA0 _ _ k i) h2) (hC0 _ _ k i)
                  have harr : ∀ (s : RTState n) k i, 0 < s.2.2 k i →
                      0 < K s (s.1 + Pi.single i 1, s.2.1, s.2.2 - linkUnit k i) := by
                    intro s k i hk
                    refine lt_of_lt_of_le ?_ (hKge _ _ k i)
                    have : C s (s.1 + Pi.single i 1, s.2.1, s.2.2 - linkUnit k i) k i = (s.2.2 k i : ℝ) / τ k i := by
                      rw [hCd]; exact if_pos ⟨hk, rfl⟩
                    rw [this]
                    exact add_pos_of_nonneg_of_pos (add_nonneg (hA0 _ _ k i) (hB0 _ _ k i))
                      (div_pos (Nat.cast_pos.2 hk) (hτ k i))
                  have mmove : ∀ (x : Fin n → ℕ) a c, ((x, 0, 0) : RTState n) ∈ rtStates n m → 0 < x a →
                      ((x - Pi.single a 1 + Pi.single c 1, 0, 0) : RTState n) ∈ rtStates n m := by
                    intro x a c hx hxa
                    rw [hmemIff] at hx ⊢
                    exact hA5 _ _ _ _ _ (sxsub x a hxa) (sxadd (x - Pi.single a 1) c) hx
                  -- reachability of the canonical state
                  have hreach : ∀ (P : RTState n → Prop),
                      (∀ s s', s ∈ rtStates n m → s' ∈ rtStates n m → P s' → 0 < K s s' → P s) →
                      P (Pi.single i0 m, 0, 0) → ∀ s ∈ rtStates n m, P s := by
                    clear * - mride mstay mredir marr mmove hSle sysub syadd hstay hride hredir harr hconn hφ hR
                      hmemIff
                    intro P hP hcanon
                    have hLUp : ∀ a c, 0 < ((0 + linkUnit a c : Fin n → Fin n → ℕ)) a c := fun a c => by
                      show 0 < 0 + linkUnit a c a c
                      rw [zero_add]; exact lt_of_lt_of_eq Nat.one_pos (if_pos ⟨rfl, rfl⟩).symm
                    have hL0 : ∀ a c, ((0 : Fin n → Fin n → ℕ) + linkUnit a c - linkUnit a c) = 0 := fun a c => by
                      rw [zero_add, tsub_self]
                    have hedge : ∀ a c, a ≠ c →
                        0 < inducedDemand φ (fun _ _ => 1) R a c * (fun _ _ => (1:ℝ)) a c →
                        ∀ x : Fin n → ℕ, ((x, 0, 0) : RTState n) ∈ rtStates n m → 0 < x a →
                        P (x - Pi.single a 1 + Pi.single c 1, 0, 0) → P (x, 0, 0) := by
                      intro a c hac hpos x hx hxa hPt
                      simp only [inducedDemand, mul_one] at hpos
                      have hs1 := mride (x, 0, 0) hx a c hxa
                      have hlu := hLUp a c
                      by_cases h1 : 0 < φ a c * (1 - ∑ k, R c k)
                      · have hRp' := pos_of_mul_pos_right h1 (hφ a c)
                        have hφp : 0 < φ a c := pos_of_mul_pos_left h1 hRp'.le
                        have hRp : ∑ k, R c k < 1 := sub_pos.1 hRp'
                        have hs2 := mstay _ hs1 a c hlu
                        have hP2 : P (x - Pi.single a 1 + Pi.single c 1,
                            (0 : Fin n → Fin n → ℕ) + linkUnit a c - linkUnit a c, 0) := by rw [hL0]; exact hPt
                        have hP1 := hP _ _ hs1 hs2 hP2 (hstay _ a c hlu hRp)
                        exact hP _ _ hx hs1 hP1 (hride (x, 0, 0) a c hxa hφp)
                      · have h2 : 0 < ∑ k, φ a k * R k c :=
                          lt_of_lt_of_le hpos (add_le_of_nonpos_left (not_lt.1 h1))
                        obtain ⟨k, -, hk⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ)
                          (f := fun _ => (0:ℝ)) (g := fun k => φ a k * R k c) (by rw [Finset.sum_const_zero]; exact h2)
                        have hφp : 0 < φ a k := pos_of_mul_pos_left hk (hR k c)
                        have hRp : 0 < R k c := pos_of_mul_pos_right hk (hφ a k)
                        have hs1 := mride (x, 0, 0) hx a k hxa
                        have hlu := hLUp a k
                        have hs2 := mredir _ hs1 a k c hlu
                        have hlu2 := hLUp k c
                        have hs3 := marr _ hs2 k c hlu2
                        have hP3 : P (x - Pi.single a 1 + Pi.single c 1,
                            (0 : Fin n → Fin n → ℕ) + linkUnit a k - linkUnit a k,
                            (0 : Fin n → Fin n → ℕ) + linkUnit k c - linkUnit k c) := by
                          rw [hL0, hL0]; exact hPt
                        have hP2 := hP _ _ hs2 hs3 hP3 (harr _ k c hlu2)
                        have hP1 := hP _ _ hs1 hs2 hP2 (hredir _ a k c hlu hRp)
                        exact hP _ _ hx hs1 hP1 (hride (x, 0, 0) a k hxa hφp)
                    have hpath : ∀ a c, Relation.ReflTransGen (fun a b => a ≠ b ∧
                        0 < inducedDemand φ (fun _ _ => 1) R a b * (fun _ _ => (1:ℝ)) a b) a c →
                        ∀ x : Fin n → ℕ, ((x, 0, 0) : RTState n) ∈ rtStates n m → 0 < x a →
                        P (x - Pi.single a 1 + Pi.single c 1, 0, 0) → P (x, 0, 0) := by
                      intro a c hac
                      induction hac using Relation.ReflTransGen.head_induction_on with
                      | refl =>
                        intro x hx hxa hPt
                        rwa [tsub_add_cancel_of_le (hSle x _ hxa)] at hPt
                      | @head a b hab hbc ih =>
                        intro x hx hxa hPt
                        have hx1 := mmove x a b hx hxa
                        have hx1b : 0 < (x - Pi.single a 1 + Pi.single b 1 : Fin n → ℕ) b := by
                          show 0 < (x - Pi.single a 1 : Fin n → ℕ) b + (Pi.single b 1 : Fin n → ℕ) b
                          rw [Pi.single_eq_same]; exact Nat.succ_pos _
                        have := ih (x - Pi.single a 1 + Pi.single b 1) hx1 hx1b
                          (by rwa [add_tsub_cancel_right])
                        exact hedge a b hab.1 hab.2 x hx hxa this
                    have hK1 : ∀ A A' E d d' N : ℕ, A' + 1 = A → d' ≤ d → 2 * A + E + d = N →
                        2 * A' + E + d' < N := by
                      intro A A' E d d' N h1 h2 h3; subst h1 h3
                      exact Nat.add_lt_add_of_lt_of_le (Nat.add_lt_add_right
                        (Nat.lt_add_of_pos_right two_pos : 2 * A' < 2 * A' + 2) E) h2
                    have hK2 : ∀ A A' E E' d N : ℕ, A' + 1 = A → E' = E + 1 → 2 * A + E + d = N →
                        2 * A' + E' + d < N := by
                      intro A A' E E' d N h1 h2 h3; subst h1 h2 h3
                      exact Nat.add_lt_add_right (lt_of_lt_of_eq (Nat.lt_succ_self (2 * A' + (E + 1)))
                        (Nat.add_right_comm (2 * A') 2 E).symm) d
                    have hK3 : ∀ A E E' d d' N : ℕ, E' + 1 = E → d' ≤ d → 2 * A + E + d = N →
                        2 * A + E' + d' < N := by
                      intro A E E' d d' N h1 h2 h3; subst h1 h3
                      exact Nat.add_lt_add_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_succ_self E') (2 * A)) h2
                    have key : ∀ N, ∀ s ∈ rtStates n m,
                        2 * (∑ a, ∑ b, s.2.1 a b) + (∑ a, ∑ b, s.2.2 a b) + (m - s.1 i0) = N → P s := by
                      intro N
                      induction N using Nat.strong_induction_on with
                      | _ N ih =>
                      intro s hs hN
                      have hsum := (hmemIff s).1 hs
                      by_cases hy : ∃ k i, 0 < s.2.1 k i
                      · obtain ⟨k, i, hki⟩ := hy
                        have h1 := sysub s.2.1 k i hki
                        by_cases hlt : ∑ j, R i j < 1
                        · have hs' := mstay s hs k i hki
                          exact hP s _ hs hs' (ih _ (hK1 _ _ _ _ _ _ h1
                            (Nat.sub_le_sub_left (Nat.le_add_right _ _) m) hN) _ hs' rfl) (hstay s k i hki hlt)
                        · obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ)
                            (f := fun _ => (0:ℝ)) (g := fun j => R i j)
                            (by rw [Finset.sum_const_zero]; exact lt_of_lt_of_le one_pos (not_lt.1 hlt))
                          have hs' := mredir s hs k i j hki
                          exact hP s _ hs hs' (ih _ (hK2 _ _ _ _ _ _ h1 (syadd s.2.2 i j) hN) _ hs' rfl)
                            (hredir s k i j hki hj)
                      · 
                        by_cases he : ∃ k i, 0 < s.2.2 k i
                        · obtain ⟨k, i, hki⟩ := he
                          have h1 := sysub s.2.2 k i hki
                          have hs' := marr s hs k i hki
                          exact hP s _ hs hs' (ih _ (hK3 _ _ _ _ _ _ h1
                            (Nat.sub_le_sub_left (Nat.le_add_right _ _) m) hN) _ hs' rfl) (harr s k i hki)
                        · 
                          obtain ⟨x, y, e⟩ := s
                          have hy0 : y = 0 := funext fun a => funext fun b => Nat.eq_zero_of_not_pos fun h => hy ⟨a, b, h⟩
                          have he0 : e = 0 := funext fun a => funext fun b => Nat.eq_zero_of_not_pos fun h => he ⟨a, b, h⟩
                          subst hy0 he0
                          have hz0 : (∑ a, ∑ b, (0 : Fin n → Fin n → ℕ) a b) = 0 :=
                            Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => rfl
                          dsimp only at hsum hN
                          rw [hz0, Nat.add_zero] at hsum
                          by_cases hx : ∃ b, b ≠ i0 ∧ 0 < x b
                          · obtain ⟨b, hb, hb0⟩ := hx
                            have hs' := mmove x b i0 hs hb0
                            have hle : x i0 + x b ≤ ∑ k, x k := by
                              have := Finset.sum_le_sum_of_subset_of_nonneg (f := x)
                                (Finset.subset_univ {i0, b}) (fun _ _ _ => Nat.zero_le _)
                              rwa [Finset.sum_pair (Ne.symm hb)] at this
                            have hx0 : (x - Pi.single b 1 + Pi.single i0 1 : Fin n → ℕ) i0 = x i0 + 1 := by
                              simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same,
                                Pi.single_eq_of_ne (Ne.symm hb), Nat.sub_zero]
                            have hlt' : x i0 < m := lt_of_lt_of_le (Nat.lt_add_of_pos_right hb0) (hle.trans hsum.le)
                            have hP' := ih _ (by
                              rw [← hN]
                              exact Nat.add_lt_add_left (lt_of_eq_of_lt (congrArg (m - ·) hx0)
                                (Nat.sub_lt_sub_left hlt' (Nat.lt_succ_self _))) _) _ hs' rfl
                            exact hpath b i0 (hconn b i0) x hs hb0 hP'
                          · 
                            have hx0 : ∀ b, b ≠ i0 → x b = 0 := fun b hb => Nat.eq_zero_of_not_pos fun h => hx ⟨b, hb, h⟩
                            have hs1 : ∑ k, x k = x i0 := Fintype.sum_eq_single i0 hx0
                            have : x = Pi.single i0 m := by
                              funext k
                              by_cases hk : k = i0
                              · subst hk; rw [Pi.single_eq_same]; exact hs1.symm.trans hsum
                              · rw [Pi.single_eq_of_ne hk]; exact hx0 k hk
                            subst this; exact hcanon
                    intro s hs
                    exact key _ s hs rfl
                  -- uniqueness
                  have hcan : ((Pi.single i0 m, 0, 0) : RTState n) ∈ rtStates n m := by
                    rw [hmemIff]
                    dsimp only
                    simp only [Pi.zero_apply, Finset.sum_const_zero, add_zero]
                    rw [Finset.sum_pi_single', if_pos (Finset.mem_univ _)]
                  have hνc : 0 < ν (Pi.single i0 m, 0, 0) := by
                    rw [hν]
                    dsimp only
                    simp only [Pi.zero_apply, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
                      Finset.prod_const_one, mul_one]
                    exact Finset.prod_pos fun k _ => pow_pos (hρ k) _
                  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = π (Pi.single i0 m, 0, 0) / ν (Pi.single i0 m, 0, 0) := ⟨_, rfl⟩
                  obtain ⟨v, hv⟩ : ∃ v : RTState n → ℝ, v = fun s => π s - c * ν s := ⟨_, rfl⟩
                  have hvb : ∀ s ∈ rtStates n m, v s * (∑ t ∈ rtStates n m, K s t) =
                      ∑ t ∈ rtStates n m, v t * K t s := by
                    intro s hs
                    rw [hv]; dsimp only
                    rw [sub_mul, mul_assoc, hb s hs, hbal s hs, Finset.mul_sum, ← Finset.sum_sub_distrib]
                    refine Finset.sum_congr rfl fun t _ => ?_; rw [sub_mul, mul_assoc]
                  have hK0 : ∀ s t, 0 ≤ K s t := fun s t => by
                    rw [hKd]; exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => hT0 s t k i
                  have hle : ∀ s ∈ rtStates n m, |v s| * ∑ t ∈ rtStates n m, K s t ≤
                      ∑ t ∈ rtStates n m, |v t| * K t s := by
                    intro s hs
                    rw [← abs_of_nonneg (Finset.sum_nonneg fun t _ => hK0 s t), ← abs_mul, hvb s hs]
                    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq (Finset.sum_congr rfl fun t _ => ?_))
                    rw [abs_mul, abs_of_nonneg (hK0 t s)]
                  have hsumA : ∑ s ∈ rtStates n m, |v s| * ∑ t ∈ rtStates n m, K s t =
                      ∑ s ∈ rtStates n m, ∑ t ∈ rtStates n m, |v t| * K t s := by
                    rw [Finset.sum_comm]
                    refine Finset.sum_congr rfl fun s _ => ?_
                    rw [Finset.mul_sum]
                  have habs : ∀ s ∈ rtStates n m, |v s| * ∑ t ∈ rtStates n m, K s t =
                      ∑ t ∈ rtStates n m, |v t| * K t s :=
                    (Finset.sum_eq_sum_iff_of_le hle).1 hsumA
                  have hzero := hreach (fun t => v t = 0) (by
                    intro s s' hs hs' h0 hpos
                    have h1 := habs s' hs'
                    rw [show v s' = 0 from h0, abs_zero, zero_mul] at h1
                    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
                      (fun u _ => mul_nonneg (abs_nonneg (v u)) (hK0 u s'))).1 h1.symm s hs
                    exact abs_eq_zero.1 (le_antisymm (le_of_mul_le_mul_right (le_of_eq (h2.trans
                      (zero_mul _).symm)) hpos) (abs_nonneg _))) (by
                      show v _ = 0
                      rw [hv]; dsimp only; rw [hc, div_mul_cancel₀ _ hνc.ne', sub_self])
                  have hπc : ∀ s ∈ rtStates n m, π s = c * ν s := by
                    intro s hs
                    have := hzero s hs
                    rw [hv] at this; exact sub_eq_zero.1 this
                  have hcZ : c * ∑ t ∈ rtStates n m, ν t = 1 := by
                    rw [← hsum1, Finset.mul_sum]
                    exact Finset.sum_congr rfl fun t ht => (hπc t ht).symm
                  intro s hs
                  rw [hπc s hs, mul_comm c, mul_assoc, hcZ, mul_one]
                have pK : ∀ (hm : 1 ≤ m) (φ τ I c : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
                    (hτ : ∀ i j, 0 < τ i j) (ρ : Fin n → ℝ) (z R : Fin n → Fin n → ℝ) (hρ : ∀ k, 0 ≤ ρ k)
                    (hz : ∀ i j, z i j = R i j * ∑ k, φ k i * ρ k)
                    (ν : RTState n → ℝ)
                    (hν : ∀ s : RTState n, ν s = (∏ k, ρ k ^ s.1 k) *
                      ((∏ a, ∏ b, (τ a b * φ a b * ρ a) ^ s.2.1 a b / ((s.2.1 a b).factorial : ℝ)) *
                       (∏ a, ∏ b, (τ a b * z a b) ^ s.2.2 a b / ((s.2.2 a b).factorial : ℝ))))
                    (π : RTState n → ℝ) (hπν : ∀ s ∈ rtStates n m, π s * ∑ t ∈ rtStates n m, ν t = ν s),
                    rtObj n m φ τ I c (toRTPolicy R) π * ∑ t ∈ rtStates n m, ν t =
                      (∑ t ∈ rtStates n (m - 1), ν t) * ∑ i, ∑ j, (φ i j * ρ i * I i j - c i j * z i j) := by
                  intro hm φ τ I c hφ hτ ρ z R hρ hz ν hν π hπν
                  clear * - hm φ τ I c hφ hτ ρ z R hρ hz ν hν π hπν
                  classical
                  have hSt : ∀ (N : ℕ) (t : RTState n), t ∈ rtStates n N ↔
                      (∑ i, t.1 i) + (∑ i, ∑ j, t.2.1 i j) + (∑ i, ∑ j, t.2.2 i j) = N := by
                    intro N t
                    simp only [rtStates, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset,
                      Finset.mem_range]
                    constructor
                    · exact fun h => h.2
                    · intro ht
                      refine ⟨⟨fun i => ?_, fun i j => ?_, fun i j => ?_⟩, ht⟩
                      · have := Finset.single_le_sum (f := t.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
                        omega
                      · have h1 := Finset.single_le_sum (f := t.2.1 i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
                        have h2 := Finset.single_le_sum (f := fun i => ∑ j, t.2.1 i j) (fun _ _ => Nat.zero_le _)
                          (Finset.mem_univ i)
                        omega
                      · have h1 := Finset.single_le_sum (f := t.2.2 i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
                        have h2 := Finset.single_le_sum (f := fun i => ∑ j, t.2.2 i j) (fun _ _ => Nat.zero_le _)
                          (Finset.mem_univ i)
                        omega
                  have hprod1 : ∀ (F G : Fin n → ℝ) (k : Fin n), (∀ a, a ≠ k → F a = G a) →
                      ∏ a, F a = F k * ∏ a ∈ univ.erase k, G a := by
                    intro F G k h
                    rw [← mul_prod_erase univ F (mem_univ k)]
                    congr 1
                    exact prod_congr rfl fun a ha => h a (ne_of_mem_erase ha)
                  obtain ⟨G1, hG1⟩ : ∃ G1, G1 = ∑ t ∈ rtStates n (m - 1), ν t := ⟨_, rfl⟩
                  -- availability identity
                  have hA : ∀ k, ∑ s ∈ rtStates n m, (if 0 < s.1 k then ν s else 0) = ρ k * G1 := by
                    intro k
                    have hsx : ∀ x : Fin n → ℕ, ∑ i, (x + Pi.single k 1 : Fin n → ℕ) i = ∑ i, x i + 1 := by
                      intro x
                      rw [Finset.sum_congr rfl (fun i _ => Pi.add_apply x (Pi.single k 1) i), sum_add_distrib,
                        Finset.sum_pi_single', if_pos (mem_univ k)]
                    have hSle : ∀ x : Fin n → ℕ, 0 < x k → Pi.single k 1 ≤ x := by
                      intro x hx i; by_cases h : i = k
                      · subst h; rw [Pi.single_eq_same]; exact hx
                      · rw [Pi.single_eq_of_ne h]; exact Nat.zero_le _
                    rw [← sum_filter, hG1, mul_sum]
                    symm
                    refine sum_nbij' (fun t => (t.1 + Pi.single k 1, t.2)) (fun s => (s.1 - Pi.single k 1, s.2))
                      ?_ ?_ ?_ ?_ ?_
                    · intro t ht
                      rw [hSt] at ht
                      rw [mem_filter, hSt]
                      refine ⟨?_, ?_⟩
                      · simp only; rw [hsx]; omega
                      · show 0 < t.1 k + (Pi.single k 1 : Fin n → ℕ) k
                        rw [Pi.single_eq_same]; omega
                    · intro s hs
                      rw [mem_filter, hSt] at hs
                      rw [hSt]
                      have hle : Pi.single k 1 ≤ s.1 := hSle s.1 hs.2
                      have he : s.1 = (s.1 - Pi.single k 1) + Pi.single k 1 := (tsub_add_cancel_of_le hle).symm
                      have := hs.1
                      rw [he, hsx] at this
                      simp only
                      omega
                    · intro t _
                      exact Prod.ext (add_tsub_cancel_right _ _) rfl
                    · intro s hs
                      rw [mem_filter] at hs
                      have hle : Pi.single k 1 ≤ s.1 := hSle s.1 hs.2
                      exact Prod.ext (tsub_add_cancel_of_le hle) rfl
                    · intro t _
                      rw [hν, hν]
                      simp only [Pi.add_apply, pow_add, prod_mul_distrib]
                      have : ∏ i, ρ i ^ (Pi.single k 1 : Fin n → ℕ) i = ρ k := by
                        rw [hprod1 _ (fun _ => 1) k (fun a ha => by rw [Pi.single_eq_of_ne ha, pow_zero]),
                          Pi.single_eq_same, pow_one, prod_const_one, mul_one]
                      rw [this]; ring
                  -- Little's law for occupied links
                  have hgen : ∀ (W : ℝ) (j : ℕ), ((j + 1 : ℕ) : ℝ) * (W ^ (j + 1) / (((j + 1).factorial : ℕ) : ℝ)) =
                      W * (W ^ j / ((j.factorial : ℕ) : ℝ)) := by
                    clear * -
                    intro W j
                    have h1 : ((j.factorial : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_pos _).ne'
                    have h2 : ((j + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
                    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ, div_mul_eq_div_div, mul_div_assoc', mul_div_assoc',
                      mul_div_cancel_left₀ _ h2]
                    ring
                  have hB : ∀ k i, ∑ s ∈ rtStates n m, (s.2.1 k i : ℝ) * ν s = τ k i * φ k i * ρ k * G1 := by
                    intro k i
                    have hLUki : linkUnit k i k i = 1 := if_pos ⟨rfl, rfl⟩
                    have hLU : (∑ a, ∑ b, linkUnit k i a b) = 1 := by
                      rw [Finset.sum_eq_single k (fun a _ ha => sum_eq_zero fun b _ =>
                            show linkUnit k i a b = 0 from if_neg (fun h => ha h.1))
                          (fun h => absurd (mem_univ k) h),
                        Finset.sum_eq_single i (fun b _ hb => show linkUnit k i k b = 0 from if_neg (fun h => hb h.2))
                          (fun h => absurd (mem_univ i) h)]
                      exact hLUki
                    have hy : ∀ y : Fin n → Fin n → ℕ, (∑ a, ∑ b, (y + linkUnit k i) a b) = (∑ a, ∑ b, y a b) + 1 := by
                      intro y; simp only [Pi.add_apply, Finset.sum_add_distrib, hLU]
                    have hLUle : ∀ y : Fin n → Fin n → ℕ, 1 ≤ y k i → linkUnit k i ≤ y := by
                      intro y hy1 a b
                      simp only [linkUnit]
                      split_ifs with h
                      · obtain ⟨rfl, rfl⟩ := h; exact hy1
                      · exact Nat.zero_le _
                    rw [← sum_filter_of_ne (p := fun s => 1 ≤ s.2.1 k i) (fun s _ h => by
                      by_contra hc
                      have : s.2.1 k i = 0 := by omega
                      simp [this] at h), hG1, mul_sum]
                    symm
                    refine sum_nbij' (fun t => (t.1, t.2.1 + linkUnit k i, t.2.2))
                      (fun s => (s.1, s.2.1 - linkUnit k i, s.2.2)) ?_ ?_ ?_ ?_ ?_
                    · intro t ht
                      rw [hSt] at ht
                      rw [mem_filter, hSt]
                      refine ⟨?_, ?_⟩
                      · simp only; rw [hy]; omega
                      · show 1 ≤ t.2.1 k i + linkUnit k i k i
                        rw [hLUki]; omega
                    · intro s hs
                      rw [mem_filter, hSt] at hs
                      rw [hSt]
                      have he : s.2.1 = (s.2.1 - linkUnit k i) + linkUnit k i :=
                        (tsub_add_cancel_of_le (hLUle _ hs.2)).symm
                      have := hs.1
                      rw [he, hy] at this
                      simp only
                      omega
                    · intro t _
                      exact Prod.ext rfl (Prod.ext (add_tsub_cancel_right _ _) rfl)
                    · intro s hs
                      rw [mem_filter] at hs
                      exact Prod.ext rfl (Prod.ext (tsub_add_cancel_of_le (hLUle _ hs.2)) rfl)
                    · intro t _
                      rw [hν, hν]
                      simp only
                      obtain ⟨x, y, e⟩ := t
                      simp only
                      set f : Fin n → Fin n → ℕ → ℝ := fun a b j =>
                        (τ a b * φ a b * ρ a) ^ j / ((j.factorial : ℕ) : ℝ) with hf
                      have h1 : ∏ a, ∏ b, (τ a b * φ a b * ρ a) ^ (y + linkUnit k i) a b /
                            (((y + linkUnit k i) a b).factorial : ℝ) =
                          f k i (y k i + 1) * ((∏ b ∈ univ.erase i, f k b (y k b)) *
                            ∏ a ∈ univ.erase k, ∏ b, f a b (y a b)) := by
                        rw [hprod1 _ (fun a => ∏ b, f a b (y a b)) k (fun a ha => prod_congr rfl fun b _ => by
                          show _ = f a b (y a b)
                          rw [Pi.add_apply, Pi.add_apply, show linkUnit k i a b = 0 from if_neg (fun h => ha h.1),
                            add_zero])]
                        rw [hprod1 _ (fun b => f k b (y k b)) i (fun b hb => by
                          show _ = f k b (y k b)
                          rw [Pi.add_apply, Pi.add_apply, show linkUnit k i k b = 0 from if_neg (fun h => hb h.2),
                            add_zero])]
                        rw [Pi.add_apply, Pi.add_apply, hLUki, mul_assoc]
                      have h2 : ∏ a, ∏ b, (τ a b * φ a b * ρ a) ^ y a b / ((y a b).factorial : ℝ) =
                          f k i (y k i) * ((∏ b ∈ univ.erase i, f k b (y k b)) *
                            ∏ a ∈ univ.erase k, ∏ b, f a b (y a b)) := by
                        rw [hprod1 _ (fun a => ∏ b, f a b (y a b)) k (fun a _ => rfl)]
                        rw [hprod1 _ (fun b => f k b (y k b)) i (fun b _ => rfl)]
                        ring
                      have h3 : ((y k i + 1 : ℕ) : ℝ) * f k i (y k i + 1) = τ k i * φ k i * ρ k * f k i (y k i) := by
                        exact hgen _ _
                      have hval : (y + linkUnit k i) k i = y k i + 1 := by
                        rw [Pi.add_apply, Pi.add_apply, hLUki]
                      rw [h1, h2, hval]
                      linear_combination (-1 : ℝ) * (∏ k, ρ k ^ x k) * ((∏ b ∈ univ.erase i, f k b (y k b)) *
                            ∏ a ∈ univ.erase k, ∏ b, f a b (y a b)) *
                          (∏ a, ∏ b, (τ a b * z a b) ^ e a b / ((e a b).factorial : ℝ)) * h3
                  have hE : rtObj n m φ τ I c (toRTPolicy R) π * ∑ t ∈ rtStates n m, ν t =
                      ∑ s ∈ rtStates n m, ν s * ((∑ k, ∑ i, if 0 < s.1 k then φ k i * I k i else 0) -
                        ∑ k, ∑ i, (s.2.1 k i : ℝ) / τ k i * ∑ j, R i j * c i j) := by
                    unfold rtObj toRTPolicy
                    rw [sum_mul]
                    refine sum_congr rfl fun s hs => ?_
                    rw [← hπν s hs]; ring
                  have hE2 : ∀ s : RTState n, ν s * ((∑ k, ∑ i, if 0 < s.1 k then φ k i * I k i else 0) -
                        ∑ k, ∑ i, (s.2.1 k i : ℝ) / τ k i * ∑ j, R i j * c i j) =
                      (∑ k, ∑ i, (if 0 < s.1 k then ν s else 0) * (φ k i * I k i)) -
                        ∑ k, ∑ i, ((s.2.1 k i : ℝ) * ν s) * ((∑ j, R i j * c i j) / τ k i) := by
                    intro s
                    rw [mul_sub, mul_sum, mul_sum]
                    congr 1
                    · refine sum_congr rfl fun k _ => ?_
                      rw [mul_sum]; refine sum_congr rfl fun i _ => ?_
                      split_ifs <;> ring
                    · refine sum_congr rfl fun k _ => ?_
                      rw [mul_sum]; refine sum_congr rfl fun i _ => ?_
                      ring
                  rw [hE, sum_congr rfl (fun s _ => hE2 s), sum_sub_distrib]
                  have hS1 : ∑ s ∈ rtStates n m, ∑ k, ∑ i, (if 0 < s.1 k then ν s else 0) * (φ k i * I k i) =
                      ∑ k, ∑ i, ρ k * G1 * (φ k i * I k i) := by
                    rw [sum_comm]; refine sum_congr rfl fun k _ => ?_
                    rw [sum_comm]; refine sum_congr rfl fun i _ => ?_
                    rw [← sum_mul, hA]
                  have hS2 : ∑ s ∈ rtStates n m, ∑ k, ∑ i, ((s.2.1 k i : ℝ) * ν s) * ((∑ j, R i j * c i j) / τ k i) =
                      ∑ k, ∑ i, τ k i * φ k i * ρ k * G1 * ((∑ j, R i j * c i j) / τ k i) := by
                    rw [sum_comm]; refine sum_congr rfl fun k _ => ?_
                    rw [sum_comm]; refine sum_congr rfl fun i _ => ?_
                    rw [← sum_mul, hB]
                  have hT : ∑ i, ∑ j, c i j * z i j = ∑ k, ∑ i, φ k i * ρ k * ∑ j, R i j * c i j := by
                    simp only [hz, mul_sum]
                    calc _ = ∑ i, ∑ k, ∑ j, c i j * (R i j * (φ k i * ρ k)) := sum_congr rfl fun i _ => sum_comm
                      _ = ∑ k, ∑ i, ∑ j, c i j * (R i j * (φ k i * ρ k)) := sum_comm
                      _ = _ := sum_congr rfl fun k _ => sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
                  have hsub : ∑ i, ∑ j, (φ i j * ρ i * I i j - c i j * z i j) =
                      ∑ i, ∑ j, φ i j * ρ i * I i j - ∑ i, ∑ j, c i j * z i j := by
                    simp only [sum_sub_distrib]
                  rw [hS1, hS2, ← hG1, hsub, hT, mul_sub, mul_sum, mul_sum]
                  congr 1
                  · exact sum_congr rfl fun k _ => by rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
                  · refine sum_congr rfl fun k _ => ?_
                    rw [mul_sum]
                    refine sum_congr rfl fun i _ => ?_
                    have := (hτ k i).ne'
                    rw [mul_div_assoc', div_eq_iff this]
                    ring
                have pBS1 : ∀ (ρ : Fin n → ℝ) (w u : Fin n → Fin n → ℝ)
                    (ν : RTState n → ℝ)
                    (hν : ∀ s : RTState n, ν s = (∏ k, ρ k ^ s.1 k) *
                      ((∏ a, ∏ b, w a b ^ s.2.1 a b / ((s.2.1 a b).factorial : ℝ)) *
                       (∏ a, ∏ b, u a b ^ s.2.2 a b / ((s.2.2 a b).factorial : ℝ)))) (N : ℕ),
                    ∑ t ∈ rtStates n N, ν t = ∑ k ∈ range (N + 1),
                      (∑ x ∈ states n k, ∏ i, ρ i ^ x i) *
                        ((∑ a, ∑ b, (w a b + u a b)) ^ (N - k) / ((N - k).factorial : ℝ)) := by
                  intro ρ w u ν hν N
                  clear * - ρ w u ν hν N
                  classical
                  obtain ⟨F, hF⟩ : ∃ F : (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℝ,
                      F = Sum.elim (fun q => w q.1 q.2) (fun q => u q.1 q.2) := ⟨_, rfl⟩
                  have hL : (∑ a, ∑ b, (w a b + u a b)) = ∑ i, F i := by
                    rw [Fintype.sum_sum_type, hF, Fintype.sum_prod_type, Fintype.sum_prod_type, ← sum_add_distrib]
                    refine sum_congr rfl fun a _ => ?_
                    rw [← sum_add_distrib]; rfl
                  have hmult : ∀ j : ℕ, ∑ g ∈ piAntidiag (univ : Finset ((Fin n × Fin n) ⊕ (Fin n × Fin n))) j,
                      ∏ i, F i ^ g i / ((g i).factorial : ℝ) = (∑ i, F i) ^ j / (j.factorial : ℝ) := by
                    intro j
                    rw [sum_pow_eq_sum_piAntidiag, sum_div]
                    refine sum_congr rfl fun g hg => ?_
                    rw [mem_piAntidiag] at hg
                    have hspec := Nat.multinomial_spec (s := univ) (f := g)
                    rw [hg.1] at hspec
                    have hpos : (0:ℝ) < ∏ i, ((g i).factorial : ℝ) :=
                      prod_pos fun i _ => Nat.cast_pos.2 (Nat.factorial_pos _)
                    have hmpos : (0:ℝ) < (Nat.multinomial univ g : ℝ) := Nat.cast_pos.2 (Nat.multinomial_pos _ _)
                    have hjf : (j.factorial : ℝ) = (∏ i, ((g i).factorial : ℝ)) * (Nat.multinomial univ g : ℝ) := by
                      rw [← hspec]; push_cast; rfl
                    rw [prod_div_distrib, hjf, mul_comm (∏ i, ((g i).factorial : ℝ)), ← div_div,
                      mul_div_cancel_left₀ _ hmpos.ne']
                  have hSt : ∀ (M : ℕ) (t : RTState n), t ∈ rtStates n M ↔
                      (∑ i, t.1 i) + (∑ i, ∑ j, t.2.1 i j) + (∑ i, ∑ j, t.2.2 i j) = M := by
                    intro M t
                    unfold rtStates
                    simp only [mem_filter, mem_product, Fintype.mem_piFinset, mem_range]
                    constructor
                    · exact fun h => h.2
                    · intro h
                      refine ⟨⟨fun i => ?_, fun i j => ?_, fun i j => ?_⟩, h⟩
                      · have := single_le_sum (fun i _ => Nat.zero_le (t.1 i)) (mem_univ i); omega
                      · have h1 := single_le_sum (fun j _ => Nat.zero_le (t.2.1 i j)) (mem_univ j)
                        have h2 := single_le_sum (fun i _ => Nat.zero_le (∑ j, t.2.1 i j)) (mem_univ i); omega
                      · have h1 := single_le_sum (fun j _ => Nat.zero_le (t.2.2 i j)) (mem_univ j)
                        have h2 := single_le_sum (fun i _ => Nat.zero_le (∑ j, t.2.2 i j)) (mem_univ i); omega
                  have hS : ∀ (k : ℕ) (x : Fin n → ℕ), x ∈ states n k ↔ ∑ i, x i = k := by
                    intro k x
                    unfold states
                    simp only [mem_filter, Fintype.mem_piFinset, mem_range]
                    constructor
                    · exact fun h => h.2
                    · intro h
                      refine ⟨fun i => ?_, h⟩
                      have := single_le_sum (fun i _ => Nat.zero_le (x i)) (mem_univ i); omega
                  have hsumι : ∀ g : (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℕ, ∑ i, g i =
                      (∑ a, ∑ b, g (Sum.inl (a, b))) + ∑ a, ∑ b, g (Sum.inr (a, b)) := by
                    intro g
                    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
                  rw [← sum_fiberwise_of_maps_to (g := fun t : RTState n => ∑ i, t.1 i) (t := range (N + 1))
                    (fun t ht => by rw [hSt] at ht; rw [mem_range]; omega)]
                  refine sum_congr rfl fun k hk => ?_
                  rw [mem_range] at hk
                  rw [hL, ← hmult (N - k), sum_mul_sum, ← sum_product']
                  symm
                  refine sum_nbij'
                    (fun p => (p.1, (fun a b => p.2 (Sum.inl (a, b)), fun a b => p.2 (Sum.inr (a, b)))))
                    (fun t => (t.1, fun i => Sum.elim (fun q => t.2.1 q.1 q.2) (fun q => t.2.2 q.1 q.2) i))
                    ?_ ?_ ?_ ?_ ?_
                  · intro p hp
                    rw [mem_product, hS, mem_piAntidiag, hsumι] at hp
                    rw [mem_filter, hSt]
                    refine ⟨?_, hp.1⟩
                    simp only
                    omega
                  · intro t ht
                    rw [mem_filter, hSt] at ht
                    rw [mem_product, hS, mem_piAntidiag, hsumι]
                    refine ⟨ht.2, ?_, fun i _ => mem_univ i⟩
                    simp only [Sum.elim_inl, Sum.elim_inr]
                    omega
                  · intro p _
                    refine Prod.ext rfl ?_
                    funext i
                    rcases i with ⟨a, b⟩ | ⟨a, b⟩ <;> rfl
                  · intro t _
                    rfl
                  · intro p _
                    rw [hν]
                    congr 1
                    rw [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_prod_type, hF]
                    rfl
                have pBS2 : ∀ (ρ : Fin n → ℝ) (hρ : ∀ k, 0 ≤ ρ k ∧ ρ k ≤ 1) (k : ℕ),
                    ((k : ℝ) + 1) * ∑ x ∈ states n (k + 1), ∏ i, ρ i ^ x i ≤
                      ((k : ℝ) + n) * ∑ x ∈ states n k, ∏ i, ρ i ^ x i := by
                  intro ρ hρ k
                  clear * - ρ hρ k
                  classical
                  have hmemS : ∀ (N : ℕ) (x : Fin n → ℕ), x ∈ states n N ↔ ∑ i, x i = N := by
                    intro N x
                    unfold states
                    rw [mem_filter, Fintype.mem_piFinset]
                    constructor
                    · exact fun h => h.2
                    · intro h
                      refine ⟨fun i => ?_, h⟩
                      rw [mem_range]; have := single_le_sum (fun i _ => Nat.zero_le (x i)) (mem_univ i); omega
                  have hf0 : ∀ x : Fin n → ℕ, 0 ≤ ∏ i, ρ i ^ x i := fun x =>
                    prod_nonneg fun i _ => pow_nonneg (hρ i).1 _
                  have hshift : ∀ (i : Fin n) (x : Fin n → ℕ),
                      ∏ j, ρ j ^ ((x + Pi.single i 1 : Fin n → ℕ)) j = ρ i * ∏ j, ρ j ^ x j := by
                    intro i x
                    simp only [Pi.add_apply, pow_add, prod_mul_distrib]
                    rw [mul_comm]; congr 1
                    rw [prod_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, pow_zero])
                      (fun h => absurd (mem_univ i) h)]
                    rw [Pi.single_eq_same, pow_one]
                  have hi : ∀ i : Fin n, ∑ x ∈ states n (k + 1), (x i : ℝ) * ∏ j, ρ j ^ x j ≤
                      ∑ x ∈ states n k, ((x i : ℝ) + 1) * ∏ j, ρ j ^ x j := by
                    intro i
                    have hinj : Set.InjOn (fun x : Fin n → ℕ => x + Pi.single i 1) (states n k) := by
                      intro a _ b _ h; exact add_right_cancel h
                    have hsub : (states n k).image (fun x : Fin n → ℕ => x + Pi.single i 1) ⊆ states n (k + 1) := by
                      intro y hy
                      obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
                      rw [hmemS] at hx ⊢
                      simp only [Pi.add_apply, sum_add_distrib, hx]
                      rw [Finset.sum_pi_single']; simp
                    rw [← sum_subset hsub (fun y hy hny => by
                      have : y i = 0 := by
                        by_contra hne
                        apply hny
                        refine mem_image.2 ⟨y - Pi.single i 1, ?_, ?_⟩
                        · rw [hmemS] at hy ⊢
                          have h1 : ∀ j, ((y - Pi.single i 1 : Fin n → ℕ)) j + (Pi.single i 1 : Fin n → ℕ) j = y j := by
                            intro j
                            by_cases hj : j = i
                            · subst hj; simp only [Pi.sub_apply, Pi.single_eq_same]; omega
                            · simp [Pi.single_eq_of_ne hj]
                          have h2 : ∑ j, (((y - Pi.single i 1 : Fin n → ℕ)) j + (Pi.single i 1 : Fin n → ℕ) j) = ∑ j, y j :=
                            sum_congr rfl fun j _ => h1 j
                          rw [sum_add_distrib, Finset.sum_pi_single'] at h2
                          simp only [mem_univ, if_true] at h2
                          omega
                        · funext j
                          by_cases hj : j = i
                          · subst hj; simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]; omega
                          · simp [Pi.single_eq_of_ne hj]
                      rw [this]; simp)]
                    rw [sum_image hinj]
                    refine sum_le_sum fun x _ => ?_
                    rw [hshift]
                    simp only [Pi.add_apply, Pi.single_eq_same, Nat.cast_add, Nat.cast_one]
                    have h1 : 0 ≤ ((x i : ℝ) + 1) * ∏ j, ρ j ^ x j :=
                      mul_nonneg (by positivity) (hf0 x)
                    have h2 := mul_le_mul_of_nonneg_left (hρ i).2 h1
                    linarith only [h2]
                  have eL : ((k : ℝ) + 1) * ∑ x ∈ states n (k + 1), ∏ i, ρ i ^ x i =
                      ∑ i, ∑ x ∈ states n (k + 1), (x i : ℝ) * ∏ j, ρ j ^ x j := by
                    rw [sum_comm, mul_sum]
                    refine sum_congr rfl fun x hx => ?_
                    rw [← sum_mul]
                    have h := (hmemS _ x).1 hx
                    have h' : ((∑ i, x i : ℕ) : ℝ) = (k : ℝ) + 1 := by rw [h]; push_cast; ring
                    rw [← h', Nat.cast_sum]
                  have eR : ∑ i, ∑ x ∈ states n k, ((x i : ℝ) + 1) * ∏ j, ρ j ^ x j =
                      ((k : ℝ) + n) * ∑ x ∈ states n k, ∏ i, ρ i ^ x i := by
                    rw [sum_comm, mul_sum]
                    refine sum_congr rfl fun x hx => ?_
                    rw [← sum_mul]
                    have h := (hmemS _ x).1 hx
                    have h' : ((∑ i, x i : ℕ) : ℝ) = (k : ℝ) := by rw [h]
                    rw [sum_add_distrib, ← Nat.cast_sum, h']
                    simp
                  rw [eL, ← eR]
                  exact sum_le_sum fun i _ => hi i
                have pBSc : ∀ (hm : 100 ≤ m) (hn : 1 ≤ n) (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
                    (hrat : ∀ k : ℕ, ((k : ℝ) + 1) * a (k + 1) ≤ ((k : ℝ) + n) * a k)
                    (L : ℝ) (hL0 : 0 ≤ L) (hL : L ≤ m),
                    delayFactor n m * ∑ k ∈ range (m + 1), a k * (L ^ (m - k) / ((m - k).factorial : ℝ)) ≤
                      ∑ k ∈ range (m - 1 + 1), a k * (L ^ (m - 1 - k) / ((m - 1 - k).factorial : ℝ)) := by
                  intro hm hn a ha hrat L hL0 hL
                  clear * - hm hn a ha hrat L hL0 hL
                  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (m * Real.log m) := ⟨_, rfl⟩
                  have hm' : (100:ℝ) ≤ m := by have := (Nat.cast_le (α := ℝ)).mpr hm; rwa [Nat.cast_ofNat] at this
                  have hmpos : (0:ℝ) < m := by linarith only [hm']
                  have hlog1 : 1 ≤ Real.log m := by
                    rw [Real.le_log_iff_exp_le hmpos]
                    linarith only [Real.exp_one_lt_d9, hm']
                  have hsq : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hmpos.le
                  have hsqm : 10 ≤ Real.sqrt m := by
                    rw [show (10:ℝ) = Real.sqrt (10 * 10) from (Real.sqrt_mul_self (by norm_num)).symm]
                    exact Real.sqrt_le_sqrt (by linarith only [hm'])
                  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
                  have hss : s * s = m * Real.log m := by
                    rw [hs]; exact Real.mul_self_sqrt (mul_nonneg hmpos.le (by linarith only [hlog1]))
                  have hs_ge : Real.sqrt m ≤ s := by
                    rw [hs]; exact Real.sqrt_le_sqrt (le_mul_of_one_le_right hmpos.le hlog1)
                  have hlogsq : Real.log m < 2 * Real.sqrt m := by
                    have h1 : Real.log m = 2 * Real.log (Real.sqrt m) := by rw [Real.log_sqrt hmpos.le]; ring
                    have h2 := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt m by linarith only [hsqm])
                    linarith only [h1, h2]
                  have h2s : 2 * s < m := by
                    have h1 : m * Real.log m < m * (2 * Real.sqrt m) := mul_lt_mul_of_pos_left hlogsq hmpos
                    have h2 : 8 * Real.sqrt m ≤ m := by
                      have := mul_le_mul_of_nonneg_right hsqm (Real.sqrt_nonneg (m:ℝ))
                      linarith only [this, hsq, hsqm]
                    have h3 := mul_le_mul_of_nonneg_left h2 hmpos.le
                    have h4 : (2*s)*(2*s) < (m:ℝ)*m := by linarith only [h1, h3, hss]
                    by_contra hc
                    have := mul_self_le_mul_self hmpos.le (le_of_not_gt hc); linarith only [this, h4]
                  have hs1 : 10 ≤ s := le_trans hsqm hs_ge
                  have hms0 : 0 ≤ (m:ℝ) - s := by linarith only [h2s, hs1]


                  have hseq : ∀ p : ℕ → ℝ, (∀ k, 0 ≤ p k) →
                      (∀ k : ℕ, 1 ≤ k → (k:ℝ) * p k ≤ ((m:ℝ) - 2 * s) * p (k-1)) →
                      s * (∑ i ∈ range (m + 1 - (⌊(m:ℝ) - s⌋₊ + 1)), p ((⌊(m:ℝ) - s⌋₊ + 1) + i)) ≤
                        3 * ∑ k ∈ range (m + 1), p k := by
                    intro p hp0 hst
                    clear * - hsqm hs_ge h2s hmpos hsq hss hp0 hst
                    obtain ⟨K, hK⟩ : ∃ K, K = ⌊(m:ℝ) - s⌋₊ + 1 := ⟨_, rfl⟩
                    rw [← hK]
                    have hs1 : 10 ≤ s := le_trans hsqm hs_ge
                    have hms0 : 0 ≤ (m:ℝ) - s := by linarith only [h2s, hs1]
                    have hKgt : (m:ℝ) - s < K := by rw [hK, Nat.cast_add, Nat.cast_one]; exact Nat.lt_floor_add_one _
                    have hKle : (K:ℝ) ≤ m - s + 1 := by
                      rw [hK, Nat.cast_add, Nat.cast_one]; linarith only [Nat.floor_le hms0]
                    have hKm : K ≤ m := by
                      have : (K:ℝ) ≤ m := by linarith only [hKle, hs1]
                      exact Nat.cast_le.mp this
                    obtain ⟨J, hJ⟩ : ∃ J, J = ⌊s⌋₊ := ⟨_, rfl⟩
                    have hJs : (J:ℝ) ≤ s := by rw [hJ]; exact Nat.floor_le (by linarith only [hs1])
                    have hJs' : s < J + 1 := by rw [hJ]; exact Nat.lt_floor_add_one _
                    have hJK : J ≤ K := by
                      have : (J:ℝ) ≤ K := by linarith only [hJs, hKgt, h2s]
                      exact Nat.cast_le.mp this
                    obtain ⟨L, hL⟩ : ∃ L, L = ⌊Real.sqrt m⌋₊ := ⟨_, rfl⟩
                    have hLs' : Real.sqrt m < L + 1 := by rw [hL]; exact Nat.lt_floor_add_one _
                    have hLs : (L:ℝ) ≤ Real.sqrt m := by rw [hL]; exact Nat.floor_le (by linarith only [hsqm])
                    have hLJ : L ≤ J := by rw [hL, hJ]; exact Nat.floor_le_floor hs_ge
                    have hVpos : 0 < (m:ℝ) - 2 * s := by linarith only [h2s]
                    -- upper bound on the tail
                    have hup : s * (∑ i ∈ range (m + 1 - K), p (K + i)) ≤ m * p K := by
                      obtain ⟨N, hN⟩ : ∃ N, N + 1 = m + 1 - K := ⟨m - K, by omega⟩
                      have hS1 : ∑ i ∈ range (N + 1), p (K + i) = ∑ i ∈ range N, p (K + (i+1)) + p K :=
                        sum_range_succ' (fun i => p (K + i)) N
                      have hS2 : ∑ i ∈ range (N + 1), p (K + i) = ∑ i ∈ range N, p (K + i) + p (K + N) :=
                        sum_range_succ (fun i => p (K + i)) N
                      rw [← hN, hS1]
                      have hstep : ∀ i, ((K:ℝ) + 1) * p (K + (i+1)) ≤ ((m:ℝ) - 2 * s) * p (K + i) := by
                        intro i
                        have h := hst (K + (i+1)) (Nat.le_add_left _ _)
                        rw [Nat.add_succ_sub_one] at h
                        have : ((K:ℝ) + 1) ≤ ((K + (i+1) : ℕ) : ℝ) := by
                          rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]; linarith only [(i.cast_nonneg : (0:ℝ) ≤ i)]
                        exact le_trans (mul_le_mul_of_nonneg_right this (hp0 _)) h
                      have hsum : ((K:ℝ) + 1) * (∑ i ∈ range N, p (K + (i+1))) ≤
                          ((m:ℝ) - 2 * s) * ∑ i ∈ range N, p (K + i) := by
                        rw [mul_sum, mul_sum]; exact sum_le_sum fun i _ => hstep i
                      have hT0 : 0 ≤ ∑ i ∈ range N, p (K + (i+1)) := sum_nonneg fun i _ => hp0 _
                      have hpK := hp0 K
                      have hpN := hp0 (K + N)
                      have e1 := mul_le_mul_of_nonneg_left (show ∑ i ∈ range N, p (K + i) ≤
                        ∑ i ∈ range N, p (K + (i+1)) + p K by linarith only [hS1, hS2, hpN]) hVpos.le
                      have e2 : s * (∑ i ∈ range N, p (K + (i+1))) ≤
                          ((K:ℝ) + 1 - ((m:ℝ) - 2 * s)) * (∑ i ∈ range N, p (K + (i+1))) :=
                        mul_le_mul_of_nonneg_right (by linarith only [hKgt]) hT0
                      have e3 := mul_le_mul_of_nonneg_right hs1 hpK
                      linear_combination hsum + e1 + e2 + e3 + 10 * hpK
                    -- lower bound by the window
                    have hlog_ineq : ∀ j : ℕ, j + 1 ≤ J → Real.exp ((s - j) / m) ≤ ((K:ℝ) - j) / ((m:ℝ) - 2 * s) := by
                      intro j hj
                      have hj' : (j:ℝ) + 1 ≤ J := by rw [← Nat.cast_succ]; exact Nat.cast_le.mpr hj
                      have hj0 : (0:ℝ) ≤ j := j.cast_nonneg
                      obtain ⟨u, hu⟩ : ∃ u, u = (s - j) / m := ⟨_, rfl⟩
                      rw [← hu, le_div_iff₀ hVpos]
                      have hum : u * m = s - j := by rw [hu]; exact div_mul_cancel₀ _ hmpos.ne'
                      have hE : Real.exp u * (1 - u) ≤ 1 := by
                        have h1 := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-u)) (Real.exp_pos u).le
                        have h2 : Real.exp u * Real.exp (-u) = 1 := by
                          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
                        linear_combination h1 + h2
                      have hEm : Real.exp u * ((m:ℝ) - s + j) ≤ m := by
                        have := mul_le_mul_of_nonneg_left hE hmpos.le
                        linear_combination this + Real.exp u * hum
                      have hA : 0 < (m:ℝ) - s + j := by linarith only [hj0, h2s, hs1]
                      have hj2 : (j:ℝ) * j ≤ s * s := mul_self_le_mul_self hj0 (by linarith only [hj', hJs])
                      have key : Real.exp u * ((m:ℝ) - 2 * s) * ((m:ℝ) - s + j) ≤ ((m:ℝ) - s - j) * ((m:ℝ) - s + j) := by
                        have ha := mul_le_mul_of_nonneg_left hEm hVpos.le
                        linear_combination ha + hj2
                      have := le_of_mul_le_mul_right key hA
                      linarith only [this, hKgt]
                    have hlow : ∀ j : ℕ, j ≤ J →
                        p K * Real.exp (((j:ℝ) * s - (j:ℝ) * ((j:ℝ) - 1) / 2) / m) ≤ p (K - j) := by
                      intro j
                      induction j with
                      | zero =>
                        intro _
                        simp only [Nat.cast_zero, zero_mul, zero_div, sub_self, Real.exp_zero, mul_one, Nat.sub_zero,
                          le_refl]
                      | succ j ih =>
                        intro hj
                        have ih := ih (Nat.le_of_succ_le hj)
                        have hjK : j + 1 ≤ K := le_trans hj hJK
                        have h := hst (K - j) (by omega)
                        rw [Nat.sub_sub] at h
                        rw [Nat.cast_sub (by omega : j ≤ K)] at h
                        have hl := hlog_ineq j hj
                        have hE : (((j+1:ℕ):ℝ) * s - ((j+1:ℕ):ℝ) * (((j+1:ℕ):ℝ) - 1) / 2) / m =
                            ((j:ℝ) * s - (j:ℝ) * ((j:ℝ) - 1) / 2) / m + (s - j) / m := by
                          rw [Nat.cast_succ]; ring
                        rw [hE, Real.exp_add, ← mul_assoc]
                        calc p K * Real.exp (((j:ℝ) * s - (j:ℝ) * ((j:ℝ) - 1) / 2) / m) * Real.exp ((s - j) / m)
                            ≤ p (K - j) * (((K:ℝ) - j) / ((m:ℝ) - 2 * s)) :=
                              mul_le_mul ih hl (Real.exp_pos _).le (hp0 _)
                          _ = ((K:ℝ) - j) * p (K - j) / ((m:ℝ) - 2 * s) := by ring
                          _ ≤ ((m:ℝ) - 2 * s) * p (K - (j+1)) / ((m:ℝ) - 2 * s) :=
                              div_le_div_of_nonneg_right h hVpos.le
                          _ = p (K - (j+1)) := mul_div_cancel_left₀ _ hVpos.ne'
                    have hexp : Real.sqrt m / 2 ≤ Real.exp (Real.log m / 2 - 1 / 2) := by
                      rw [sub_eq_add_neg, Real.exp_add]
                      have h1 : Real.exp (Real.log m / 2) = Real.sqrt m := by
                        rw [← Real.log_sqrt hmpos.le, Real.exp_log (by linarith only [hsqm])]
                      have h2 : 1 / 2 ≤ Real.exp (-(1/2)) := by
                        have := Real.add_one_le_exp (-(1/2):ℝ); linarith only [this]
                      rw [h1]
                      have := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg (m:ℝ))
                      linarith only [this]
                    have hwin : ∀ l ∈ range L, p K * (Real.sqrt m / 2) ≤ p (K - J + l) := by
                      intro l hl
                      rw [mem_range] at hl
                      have hlJ : l ≤ J := by omega
                      have h := hlow (J - l) (Nat.sub_le _ _)
                      rw [show K - (J - l) = K - J + l by omega, Nat.cast_sub hlJ] at h
                      refine le_trans ?_ h
                      apply mul_le_mul_of_nonneg_left _ (hp0 _)
                      refine le_trans hexp (Real.exp_le_exp.2 ?_)
                      have hl' : (l:ℝ) + 1 ≤ L := by rw [← Nat.cast_succ]; exact Nat.cast_le.mpr hl
                      have hl0 : (0:ℝ) ≤ l := l.cast_nonneg
                      have hlJ' : (l:ℝ) ≤ J := Nat.cast_le.mpr hlJ
                      have d0 : 0 ≤ s - ((J:ℝ) - l) := by linarith only [hl0, hJs]
                      have d1 : s - ((J:ℝ) - l) ≤ Real.sqrt m := by linarith only [hJs', hl', hLs]
                      have d2 : (s - ((J:ℝ) - l)) * (s - ((J:ℝ) - l)) ≤ m :=
                        le_trans (mul_self_le_mul_self d0 d1) hsq.le
                      have hj0 : 0 ≤ (J:ℝ) - l := by linarith only [hlJ']
                      rw [le_div_iff₀ hmpos]
                      linear_combination (1/2:ℝ) * d2 + (1/2:ℝ) * hj0 - (1/2:ℝ) * hss
                    have hZ : (L:ℝ) * (p K * (Real.sqrt m / 2)) ≤ ∑ k ∈ range (m + 1), p k := by
                      have h1 := sum_le_sum hwin
                      rw [sum_const, card_range, nsmul_eq_mul] at h1
                      refine le_trans h1 ?_
                      have h2 : ∑ l ∈ range L, p (K - J + l) = ∑ k ∈ Ico (K - J) (K - J + L), p k := by
                        rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
                      rw [h2]
                      exact sum_le_sum_of_subset_of_nonneg (fun k hk => by
                        rw [mem_Ico] at hk; rw [mem_range]; omega) (fun i _ _ => hp0 _)
                    have hfin : (m:ℝ) * p K ≤ 3 * ∑ k ∈ range (m + 1), p k := by
                      have hpK := hp0 K
                      have h1 : Real.sqrt m ≤ 3 * L / 2 := by linarith only [hLs', hsqm]
                      have h2 : (m:ℝ) * p K ≤ (3 * L / 2) * Real.sqrt m * p K := by
                        rw [show (m:ℝ) * p K = Real.sqrt m * Real.sqrt m * p K by rw [hsq]]
                        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)) hpK
                      linarith only [h2, hZ]
                    linarith only [hup, hfin]

                  have hδ : delayFactor n m = (1 - 2 * s / m) * (s / (s + n - 1) - 3 / s) := by
                    have e0 : s = m * Real.sqrt (Real.log m / m) := by
                      rw [hs, show (m:ℝ) * Real.log m = (m * m) * (Real.log m / m) by
                          rw [mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ hmpos.ne'],
                        Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self hmpos.le]
                    have e : 2 * Real.sqrt (Real.log m / m) = 2 * s / m := by
                      rw [e0, mul_left_comm, mul_div_cancel_left₀ _ hmpos.ne']
                    unfold delayFactor epsilon
                    rw [e, ← hs]
                  rw [hδ]
                  obtain ⟨c, hc⟩ : ∃ c, c = 1 - 2 * s / m := ⟨_, rfl⟩
                  obtain ⟨β, hβ⟩ : ∃ β, β = s / (s + n - 1) := ⟨_, rfl⟩
                  rw [← hc, ← hβ]
                  have hcm : c * m = m - 2 * s := by rw [hc, sub_mul, one_mul, div_mul_cancel₀ _ hmpos.ne']
                  have hc0 : 0 < c := by rw [hc]; have := (div_lt_one hmpos).2 h2s; linarith only [this]
                  have hc1 : c ≤ 1 := by
                    rw [hc]; have : 0 ≤ 2 * s / m := div_nonneg (by linarith only [hs1]) hmpos.le
                    linarith only [this]
                  have hn' : (1:ℝ) ≤ n := Nat.one_le_cast.mpr hn
                  have hsn : 0 < s + n - 1 := by linarith only [hs1, hn']
                  have hβ0 : 0 ≤ β := by rw [hβ]; exact div_nonneg (by linarith only [hs1]) hsn.le
                  have hβ1 : β ≤ 1 := by rw [hβ, div_le_one hsn]; linarith only [hn']
                  have hs3 : 0 ≤ 3 / s := div_nonneg (show (0:ℝ) ≤ 3 by norm_num) (by linarith only [hs1])
                  have hspos : 0 < s := by linarith only [hs1]
                  have hδβ : c * (β - 3 / s) ≤ β := by
                    rcases le_or_gt 0 (β - 3 / s) with h | h
                    · have := mul_le_mul_of_nonneg_right hc1 h; linarith only [this, hs3]
                    · have := mul_neg_of_pos_of_neg hc0 h; linarith only [this, hβ0]
                  -- generic shift identity
                  have hfac : ∀ (x : ℝ) (i : ℕ), ((i:ℝ) + 1) * (x ^ (i + 1) / ((i + 1).factorial : ℝ)) =
                      x * (x ^ i / (i.factorial : ℝ)) := by
                    intro x i
                    have hi0 : ((i:ℝ) + 1) ≠ 0 := ne_of_gt (by linarith only [(i.cast_nonneg : (0:ℝ) ≤ i)])
                    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ, ← mul_div_assoc,
                      mul_div_mul_left _ _ hi0, mul_comm (x ^ i) x, mul_div_assoc]
                  have hTL : ∀ (α : ℕ → ℝ) (Λ : ℝ) (Y : ℕ → ℝ), (∀ k, Y k = Λ ^ (m - k) / ((m - k).factorial : ℝ)) →
                      Λ * ∑ k ∈ range m, α k * Y (k + 1) = ∑ k ∈ range (m + 1), ((m:ℝ) - k) * (α k * Y k) := by
                    clear * - hfac
                    intro α Λ Y hY
                    rw [sum_range_succ, sub_self, zero_mul, add_zero, mul_sum]
                    refine sum_congr rfl fun k hk => ?_
                    rw [mem_range] at hk
                    obtain ⟨j, hj⟩ : ∃ j, m - k = j + 1 := ⟨m - 1 - k, by omega⟩
                    have hj2 : m - (k + 1) = j := by omega
                    have hmk : (m:ℝ) - k = j + 1 := by
                      have : m = k + (j + 1) := by omega
                      rw [this, Nat.cast_add, Nat.cast_succ, add_sub_cancel_left]
                    rw [hY, hY, hj, hj2, hmk, mul_left_comm ((j:ℝ) + 1), hfac, mul_left_comm Λ]
                  rcases hL0.eq_or_lt with h0 | hLpos
                  · -- L = 0
                    subst h0
                    clear hTL hseq hδ hc hs hss hsq hlogsq hsqm hs_ge hlog1
                    have e1 : ∑ k ∈ range (m + 1), a k * ((0:ℝ) ^ (m - k) / ((m - k).factorial : ℝ)) = a m := by
                      rw [sum_range_succ, Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
                      rw [sum_eq_zero fun k hk => by rw [zero_pow (by rw [mem_range] at hk; omega), zero_div, mul_zero],
                        zero_add]
                    have e2 : ∑ k ∈ range (m - 1 + 1), a k * ((0:ℝ) ^ (m - 1 - k) / ((m - 1 - k).factorial : ℝ)) =
                        a (m - 1) := by
                      rw [sum_range_succ, Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
                      rw [sum_eq_zero fun k hk => by rw [zero_pow (by rw [mem_range] at hk; omega), zero_div, mul_zero],
                        zero_add]
                    rw [e1, e2]
                    have h := hrat (m - 1)
                    rw [Nat.sub_add_cancel (by omega : 1 ≤ m), Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at h
                    have hD : 0 < (m:ℝ) - 1 + n := by linarith only [hm', hn']
                    have hβD : β * ((m:ℝ) - 1 + n) ≤ m := by
                      rw [hβ, div_mul_eq_mul_div, div_le_iff₀ hsn]
                      have := mul_nonneg (show (0:ℝ) ≤ m - s by linarith only [h2s, hs1]) (show (0:ℝ) ≤ n - 1 by linarith only [hn'])
                      linear_combination this
                    have h1 : c * (β - 3 / s) * a m ≤ β * a m := mul_le_mul_of_nonneg_right hδβ (ha m)
                    have h2 : β * ((m:ℝ) - 1 + n) * a m ≤ m * a m := mul_le_mul_of_nonneg_right hβD (ha m)
                    have h3 : ((m:ℝ) - 1 + n) * (β * a m) ≤ ((m:ℝ) - 1 + n) * a (m - 1) := by
                      linear_combination h2 + h
                    linarith only [h1, le_of_mul_le_mul_left h3 hD]
                  -- L > 0
                  obtain ⟨ā, hā⟩ : ∃ ā : ℕ → ℝ, ā = fun k => ∏ j ∈ range k, (((j:ℝ) + n) / ((j:ℝ) + 1)) := ⟨_, rfl⟩
                  have hārec : ∀ k, ā (k + 1) = ā k * (((k:ℝ) + n) / ((k:ℝ) + 1)) := fun k => by
                    rw [hā]; exact prod_range_succ _ _
                  have hā0 : ∀ k, 0 < ā k := fun k => by
                    rw [hā]
                    exact prod_pos fun j _ => div_pos (by linarith only [hn', (j.cast_nonneg : (0:ℝ) ≤ j)])
                      (by linarith only [(j.cast_nonneg : (0:ℝ) ≤ j)])
                  have hārec' : ∀ k : ℕ, ((k:ℝ) + 1) * ā (k + 1) = ((k:ℝ) + n) * ā k := fun k => by
                    rw [hārec]
                    have : (k:ℝ) + 1 ≠ 0 := by linarith only [(k.cast_nonneg : (0:ℝ) ≤ k)]
                    field_simp
                  have hāmono : Monotone ā := by
                    refine monotone_nat_of_le_succ fun k => ?_
                    have hk1 : (0:ℝ) < k + 1 := by linarith only [(k.cast_nonneg : (0:ℝ) ≤ k)]
                    refine le_of_mul_le_mul_left ?_ hk1
                    rw [hārec']
                    exact mul_le_mul_of_nonneg_right (by linarith only [hn']) (hā0 k).le
                  obtain ⟨a', ha'⟩ : ∃ a' : ℕ → ℝ, a' = fun k => c ^ k * a k := ⟨_, rfl⟩
                  have ha'0 : ∀ k, 0 ≤ a' k := fun k => by rw [ha']; exact mul_nonneg (pow_nonneg hc0.le _) (ha k)
                  have hstep : ∀ l : ℕ, a' (l + 1) * ā l ≤ a' l * ā (l + 1) := by
                    intro l
                    have hl1 : (0:ℝ) < l + 1 := by linarith only [(l.cast_nonneg : (0:ℝ) ≤ l)]
                    refine le_of_mul_le_mul_left ?_ hl1
                    have e1 : ((l:ℝ) + 1) * (a' (l + 1) * ā l) = c ^ (l + 1) * (((l:ℝ) + 1) * a (l + 1)) * ā l := by
                      rw [ha']; ring
                    have e2 : ((l:ℝ) + 1) * (a' l * ā (l + 1)) = c ^ l * (((l:ℝ) + n) * a l) * ā l := by
                      rw [mul_left_comm, hārec', ha']; ring
                    rw [e1, e2]
                    have hn0 : 0 ≤ ((l:ℝ) + n) * a l :=
                      mul_nonneg (by linarith only [hn', (l.cast_nonneg : (0:ℝ) ≤ l)]) (ha l)
                    refine mul_le_mul_of_nonneg_right ?_ (hā0 l).le
                    calc c ^ (l + 1) * (((l:ℝ) + 1) * a (l + 1)) ≤ c ^ (l + 1) * (((l:ℝ) + n) * a l) :=
                          mul_le_mul_of_nonneg_left (hrat l) (pow_nonneg hc0.le _)
                      _ ≤ c ^ l * (((l:ℝ) + n) * a l) :=
                          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hc0.le hc1 (Nat.le_succ l)) hn0
                  have hratio : ∀ k l, k ≤ l → a' l * ā k ≤ a' k * ā l := by
                    intro k l hkl
                    induction l, hkl using Nat.le_induction with
                    | base => exact le_refl _
                    | succ l hkl ih =>
                      refine le_of_mul_le_mul_left ?_ (hā0 l)
                      have h1 := mul_le_mul_of_nonneg_right (hstep l) (hā0 k).le
                      have h2 := mul_le_mul_of_nonneg_right ih (hā0 (l + 1)).le
                      linear_combination h1 + h2
                  obtain ⟨X, hX'⟩ : ∃ X : ℕ → ℝ, ∀ k, X k = (c * L) ^ (m - k) / ((m - k).factorial : ℝ) := ⟨_, fun _ => rfl⟩
                  have hcL : 0 < c * L := mul_pos hc0 hLpos
                  have hX0 : ∀ k, 0 ≤ X k := fun k => by
                    rw [hX']; exact div_nonneg (pow_nonneg hcL.le _) (Nat.cast_nonneg _)
                  -- comparison
                  have hcomp : (∑ k ∈ range (m + 1), ((m:ℝ) - k) * (ā k * X k)) * (∑ k ∈ range (m + 1), a' k * X k) ≤
                      (∑ k ∈ range (m + 1), ((m:ℝ) - k) * (a' k * X k)) * (∑ k ∈ range (m + 1), ā k * X k) := by
                    clear * - hX0 hratio
                    obtain ⟨G, hG⟩ : ∃ G : ℕ → ℕ → ℝ, ∀ k l, G k l = ((m:ℝ) - k) * X k * X l * (a' k * ā l - ā k * a' l) :=
                      ⟨_, fun _ _ => rfl⟩
                    have hGs : ∀ k l, 0 ≤ G k l + G l k := by
                      intro k l
                      have e : G k l + G l k = X k * X l * (((l:ℝ) - k) * (a' k * ā l - a' l * ā k)) := by rw [hG, hG]; ring
                      rw [e]
                      refine mul_nonneg (mul_nonneg (hX0 k) (hX0 l)) ?_
                      rcases le_total k l with h | h
                      · exact mul_nonneg (by have : (k:ℝ) ≤ l := Nat.cast_le.mpr h
                                             linarith only [this]) (by linarith only [hratio k l h])
                      · exact mul_nonneg_of_nonpos_of_nonpos (by have : (l:ℝ) ≤ k := Nat.cast_le.mpr h
                                                                 linarith only [this])
                          (by linarith only [hratio l k h])
                    have hsym : ∑ k ∈ range (m + 1), ∑ l ∈ range (m + 1), G k l =
                        ∑ k ∈ range (m + 1), ∑ l ∈ range (m + 1), G l k := sum_comm
                    have hpos : 0 ≤ ∑ k ∈ range (m + 1), ∑ l ∈ range (m + 1), G k l := by
                      have : 0 ≤ ∑ k ∈ range (m + 1), ∑ l ∈ range (m + 1), (G k l + G l k) :=
                        sum_nonneg fun k _ => sum_nonneg fun l _ => hGs k l
                      simp only [sum_add_distrib] at this
                      linarith only [this, hsym]
                    have hdiff : (∑ k ∈ range (m + 1), ((m:ℝ) - k) * (a' k * X k)) * (∑ k ∈ range (m + 1), ā k * X k) -
                        (∑ k ∈ range (m + 1), ((m:ℝ) - k) * (ā k * X k)) * (∑ k ∈ range (m + 1), a' k * X k) =
                        ∑ k ∈ range (m + 1), ∑ l ∈ range (m + 1), G k l := by
                      rw [sum_mul_sum, sum_mul_sum, ← sum_sub_distrib]
                      refine sum_congr rfl fun k _ => ?_
                      rw [← sum_sub_distrib]
                      refine sum_congr rfl fun l _ => ?_
                      rw [hG]; ring
                    linarith only [hdiff, hpos]
                  -- the bound for ā
                  have hābound : (β - 3 / s) * ∑ k ∈ range (m + 1), ā k * X k ≤ ∑ k ∈ range m, ā k * X (k + 1) := by
                    clear * - hseq hā0 hāmono hārec' hcL hcm hL hc0 hX' hX0 hms0 hs1 hspos hβ hsn hn' hβ0 hβ1 hfac
                    obtain ⟨p, hp⟩ : ∃ p : ℕ → ℝ, ∀ j, p j = ā (m - j) * ((c * L) ^ j / (j.factorial : ℝ)) := ⟨_, fun _ => rfl⟩
                    have hp0 : ∀ j, 0 ≤ p j := fun j => by
                      rw [hp]; exact mul_nonneg (hā0 _).le (div_nonneg (pow_nonneg hcL.le _) (Nat.cast_nonneg _))
                    have hcLm : c * L ≤ (m:ℝ) - 2 * s := by
                      rw [← hcm]; exact mul_le_mul_of_nonneg_left hL hc0.le
                    have hst : ∀ k : ℕ, 1 ≤ k → (k:ℝ) * p k ≤ ((m:ℝ) - 2 * s) * p (k-1) := by
                      intro k hk
                      obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
                      rw [Nat.add_sub_cancel, hp, hp]
                      have hQ : 0 ≤ (c * L) ^ i / (i.factorial : ℝ) := div_nonneg (pow_nonneg hcL.le _) (Nat.cast_nonneg _)
                      rw [Nat.cast_succ, mul_left_comm, hfac]
                      calc ā (m - (i + 1)) * (c * L * ((c * L) ^ i / (i.factorial : ℝ)))
                          ≤ ā (m - i) * (((m:ℝ) - 2 * s) * ((c * L) ^ i / (i.factorial : ℝ))) :=
                            mul_le_mul (hāmono (Nat.sub_le_sub_left (Nat.le_succ i) m)) (mul_le_mul_of_nonneg_right hcLm hQ)
                              (mul_nonneg hcL.le hQ) (hā0 _).le
                        _ = ((m:ℝ) - 2 * s) * (ā (m - i) * ((c * L) ^ i / (i.factorial : ℝ))) := by ring
                    have hS := hseq p hp0 hst
                    obtain ⟨K, hK⟩ : ∃ K, K = ⌊(m:ℝ) - s⌋₊ + 1 := ⟨_, rfl⟩
                    rw [← hK] at hS
                    have hKm : K ≤ m := by
                      have h1 : (K:ℝ) ≤ m - s + 1 := by
                        rw [hK, Nat.cast_add, Nat.cast_one]; linarith only [Nat.floor_le hms0]
                      have : (K:ℝ) ≤ m := by linarith only [h1, hs1]
                      exact Nat.cast_le.mp this
                    have hP : ∑ j ∈ range (m + 1), p j = ∑ k ∈ range (m + 1), ā k * X k := by
                      rw [← sum_range_reflect]
                      refine sum_congr rfl fun j hj => ?_
                      rw [mem_range] at hj
                      rw [hp, hX', show m + 1 - 1 - j = m - j by rw [Nat.add_sub_cancel], Nat.sub_sub_self (Nat.lt_succ_iff.mp hj)]
                    obtain ⟨sm, hsm⟩ : ∃ sm, sm = ∑ k ∈ range (m + 1), (if ((k:ℕ):ℝ) < s then ā k * X k else 0) := ⟨_, rfl⟩
                    have hsmeq : sm = ∑ i ∈ range (m + 1 - K), p (K + i) := by
                      have hgen : ∀ N, ∑ k ∈ range (K + N), (if K ≤ k then p k else 0) = ∑ i ∈ range N, p (K + i) := by
                        intro N
                        rw [sum_range_add, sum_eq_zero (fun k hk => if_neg (by rw [mem_range] at hk; omega)), zero_add]
                        exact sum_congr rfl fun i _ => if_pos (by omega)
                      have h2 := hgen (m + 1 - K)
                      rw [Nat.add_sub_cancel' (by omega : K ≤ m + 1)] at h2
                      rw [← h2, hsm, ← sum_range_reflect]
                      refine sum_congr rfl fun j hj => ?_
                      rw [mem_range] at hj
                      rw [show m + 1 - 1 - j = m - j by rw [Nat.add_sub_cancel]]
                      have hiff : ((m - j : ℕ) : ℝ) < s ↔ K ≤ j := by
                        rw [Nat.cast_sub (by omega : j ≤ m), hK, Nat.add_one_le_iff, Nat.floor_lt hms0]
                        constructor <;> intro h <;> linarith only [h]
                      by_cases hKj : K ≤ j
                      · rw [if_pos (hiff.2 hKj), if_pos hKj, hp, hX', Nat.sub_sub_self (Nat.lt_succ_iff.mp hj)]
                      · rw [if_neg (fun h => hKj (hiff.1 h)), if_neg hKj]
                    rw [← hsmeq, hP] at hS
                    obtain ⟨Sb, hSb⟩ : ∃ Sb, Sb = ∑ k ∈ range (m + 1), ā k * X k := ⟨_, rfl⟩
                    rw [← hSb] at hS ⊢
                    obtain ⟨h, hh⟩ : ∃ h : ℕ → ℝ, ∀ k : ℕ, h k = if (k:ℝ) < s then 0 else β * (ā k * X k) := ⟨_, fun _ => rfl⟩
                    have hhs : ∑ k ∈ range (m + 1), h k = β * Sb - β * sm := by
                      rw [hSb, hsm, mul_sum, mul_sum, ← sum_sub_distrib]
                      refine sum_congr rfl fun k _ => ?_
                      rw [hh]
                      split_ifs <;> ring
                    have hh0 : h 0 = 0 := by rw [hh, if_pos (by rw [Nat.cast_zero]; exact hspos)]
                    have hhle : ∀ k, h (k + 1) ≤ ā k * X (k + 1) := by
                      intro k
                      rw [hh]
                      split_ifs with hk
                      · exact mul_nonneg (hā0 k).le (hX0 _)
                      · rw [not_lt] at hk
                        rw [← mul_assoc]
                        refine mul_le_mul_of_nonneg_right ?_ (hX0 _)
                        have hk1 : (0:ℝ) < k + 1 := by linarith only [(k.cast_nonneg : (0:ℝ) ≤ k)]
                        refine le_of_mul_le_mul_left ?_ hk1
                        have hk' : s ≤ (k:ℝ) + 1 := by rw [Nat.cast_succ] at hk; exact hk
                        have hb : β * ((k:ℝ) + n) ≤ (k:ℝ) + 1 := by
                          rw [hβ, div_mul_eq_mul_div, div_le_iff₀ hsn]
                          have := mul_nonneg (show (0:ℝ) ≤ k + 1 - s by linarith only [hk'])
                            (show (0:ℝ) ≤ n - 1 by linarith only [hn'])
                          linear_combination this
                        have e : ((k:ℝ) + 1) * (β * ā (k + 1)) = β * (((k:ℝ) + n) * ā k) := by
                          rw [mul_left_comm, hārec']
                        rw [e, ← mul_assoc]
                        exact mul_le_mul_of_nonneg_right hb (hā0 k).le
                    have hsum : ∑ k ∈ range (m + 1), h k ≤ ∑ k ∈ range m, ā k * X (k + 1) := by
                      rw [sum_range_succ', hh0, add_zero]; exact sum_le_sum fun k _ => hhle k
                    have hsm0 : 0 ≤ sm := by
                      rw [hsm]; exact sum_nonneg fun k _ => by
                        split_ifs
                        · exact mul_nonneg (hā0 k).le (hX0 k)
                        · exact le_refl 0
                    have hsm3 : sm ≤ 3 / s * Sb := by
                      refine le_of_mul_le_mul_left ?_ hspos
                      have : s * (3 / s * Sb) = 3 * Sb := by field_simp
                      rw [this]; exact hS
                    have := mul_le_mul_of_nonneg_left hsm0 hβ0
                    have := mul_le_mul_of_nonneg_right hβ1 hsm0
                    linarith only [hhs, hsum, hsm3, this, mul_le_mul_of_nonneg_right hβ1 hsm0, mul_le_mul_of_nonneg_left hsm0 hβ0]
                  -- assemble
                  obtain ⟨Y0, hY0'⟩ : ∃ Y0 : ℕ → ℝ, ∀ k, Y0 k = L ^ (m - k) / ((m - k).factorial : ℝ) := ⟨_, fun _ => rfl⟩
                  have hscale : ∀ k ∈ range (m + 1), a' k * X k = c ^ m * (a k * Y0 k) := by
                    intro k hk
                    rw [mem_range] at hk
                    rw [ha', hX', hY0', mul_pow, ← Nat.add_sub_cancel' (show k ≤ m by omega), pow_add,
                      Nat.add_sub_cancel_left]
                    ring
                  have hS' : ∑ k ∈ range (m + 1), a' k * X k = c ^ m * ∑ k ∈ range (m + 1), a k * Y0 k := by
                    rw [mul_sum]; exact sum_congr rfl hscale
                  have hT' : ∑ k ∈ range (m + 1), ((m:ℝ) - k) * (a' k * X k) =
                      c ^ m * ∑ k ∈ range (m + 1), ((m:ℝ) - k) * (a k * Y0 k) := by
                    rw [mul_sum]; refine sum_congr rfl fun k hk => ?_
                    rw [hscale k hk]; ring
                  have hTb := hTL ā (c * L) X hX'
                  have hT0 := hTL a L Y0 hY0'
                  have hSb0 : 0 < ∑ k ∈ range (m + 1), ā k * X k := by
                    have h1 : ā m * X m ≤ ∑ k ∈ range (m + 1), ā k * X k :=
                      single_le_sum (f := fun k => ā k * X k) (fun k _ => mul_nonneg (hā0 k).le (hX0 k))
                        (mem_range.2 (Nat.lt_succ_self m))
                    have h2 : X m = 1 := by rw [hX', Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
                    rw [h2, mul_one] at h1
                    linarith only [h1, hā0 m]
                  have hS'0 : 0 ≤ ∑ k ∈ range (m + 1), a' k * X k := sum_nonneg fun k _ => mul_nonneg (ha'0 k) (hX0 k)
                  -- β' (cL) Sb S' ≤ Tb S' ≤ T' Sb
                  have k1 : (β - 3 / s) * (c * L) * (∑ k ∈ range (m + 1), ā k * X k) ≤
                      ∑ k ∈ range (m + 1), ((m:ℝ) - k) * (ā k * X k) := by
                    rw [← hTb, mul_assoc, mul_comm (c * L), ← mul_assoc]
                    exact (mul_le_mul_of_nonneg_right hābound hcL.le).trans_eq (mul_comm _ _)
                  have k2 := mul_le_mul_of_nonneg_right k1 hS'0
                  have k3 : (β - 3 / s) * (c * L) * (∑ k ∈ range (m + 1), a' k * X k) ≤
                      ∑ k ∈ range (m + 1), ((m:ℝ) - k) * (a' k * X k) := by
                    refine le_of_mul_le_mul_right ?_ hSb0
                    linarith only [k2, hcomp]
                  rw [hS', hT', ← hT0] at k3
                  have hcmL : 0 < c ^ m * L := mul_pos (pow_pos hc0 _) hLpos
                  have k4 : (c ^ m * L) * (c * (β - 3 / s) * ∑ k ∈ range (m + 1), a k * Y0 k) ≤
                      (c ^ m * L) * ∑ k ∈ range m, a k * Y0 (k + 1) := by
                    linear_combination k3
                  have k5 := le_of_mul_le_mul_left k4 hcmL
                  rw [Nat.sub_add_cancel (show 1 ≤ m from le_trans (by norm_num) hm)]
                  refine le_trans (le_of_eq ?_) (le_trans k5 (le_of_eq (sum_congr rfl fun k _ => ?_)))
                  · simp only [hY0']
                  · rw [hY0', Nat.sub_sub, Nat.add_comm k 1]
                ------------------------------------------------------------------ glue
                obtain ⟨⟨⟨hq01, hz0, hcirc, hzle⟩, hrate⟩, hoptmax⟩ := hopt
                have hq01' : ∀ i, 0 ≤ qt i ∧ qt i ≤ 1 := fun i => (hq01 i i)
                -- objective value V
                have hV0 : 0 ≤ alg8Obj φ I c qt zt := by
                  have h0 : IsAlg9Feasible φ τ m (fun _ => 0) (fun _ _ => 0) :=
                    ⟨⟨fun i j => ⟨le_refl _, zero_le_one⟩, fun i j => le_refl _,
                      fun i => by simp only [mul_zero, add_zero],
                      fun i => by simp only [mul_zero, Finset.sum_const_zero, le_refl]⟩,
                      by simp only [mul_zero, add_zero, Finset.sum_const_zero]; exact Nat.cast_nonneg m⟩
                  have h1 := hoptmax _ _ h0
                  have h2 : alg8Obj φ I c (fun _ => 0) (fun _ _ => 0) = 0 := by
                    simp only [alg8Obj, mul_zero, zero_mul, sub_zero, Finset.sum_const_zero]
                  rw [h2] at h1; exact h1
                have hUB : ∀ (r : RTState n → Fin n → Fin n → Fin n → ℝ) (π : RTState n → ℝ),
                    IsRTPolicy n m r → IsRTStationary n m φ τ r π → rtObj n m φ τ I c r π ≤ alg8Obj φ I c qt zt := by
                  intro r π hr hπ
                  obtain ⟨q, z, hf, he⟩ := pU φ τ I c hφ hτ r π hr hπ
                  rw [← he]; exact hoptmax q z hf
                clear pU
                -- n ≥ 1
                have hn : 1 ≤ n := by
                  rcases Nat.eq_zero_or_pos n with h0 | h0
                  · exfalso
                    subst h0
                    have hE : rtStates 0 m = ∅ := by
                      apply Finset.eq_empty_of_forall_notMem
                      intro s hs
                      simp only [rtStates, mem_filter] at hs
                      have := hs.2
                      simp only [Finset.univ_eq_empty, Finset.sum_empty] at this
                      omega
                    have h1 := hπt.2.2.1
                    rw [hE, Finset.sum_empty] at h1
                    exact zero_ne_one h1
                  · exact h0
                -- the redirection matrix
                have hD0 : ∀ i, 0 ≤ ∑ k, φ k i * qt k := fun i =>
                  Finset.sum_nonneg fun k _ => mul_nonneg (hφ k i) (hq01' k).1
                have hrtv : ∀ i j, rt i j = zt i j / ∑ k, φ k i * qt k := by
                  intro i j; rw [hrt]; rfl
                have hzsum : ∀ i, ∑ j, zt i j ≤ ∑ k, φ k i * qt k := fun i => hzle i
                have hR : ∀ i j, 0 ≤ rt i j := fun i j => by
                  rw [hrtv]; exact div_nonneg (hz0 i j) (hD0 i)
                have hR1 : ∀ i, ∑ j, rt i j ≤ 1 := by
                  intro i
                  simp only [hrtv]
                  rw [← Finset.sum_div]
                  rcases (hD0 i).eq_or_lt with h | h
                  · rw [← h, div_zero]; exact zero_le_one
                  · exact div_le_one_of_le₀ (hzsum i) (hD0 i)
                have hz : ∀ i j, zt i j = rt i j * ∑ k, φ k i * qt k := by
                  intro i j
                  rw [hrtv]
                  rcases (hD0 i).eq_or_lt with h | h
                  · rw [← h, mul_zero]
                    have h1 : zt i j ≤ ∑ j, zt i j :=
                      Finset.single_le_sum (fun j _ => hz0 i j) (Finset.mem_univ j)
                    have := hzsum i
                    linarith only [h1, this, hz0 i j, h]
                  · rw [div_mul_cancel₀ _ h.ne']
                have hpol : IsRTPolicy n m (toRTPolicy rt) := fun s _ k i => ⟨fun j => hR i j, hR1 i⟩
                -- ε facts and delayFactor ≤ 1
                have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm
                have hdf1 : delayFactor n m ≤ 1 := by
                  clear * - hmR hn
                  have hlog : Real.log m < m / 4 := by
                    have h1 := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ m / 4 by linarith only [hmR])
                    rw [Real.log_lt_iff_lt_exp (by linarith only [hmR])]
                    have h2 : (m:ℝ) * 100 ≤ m * m := mul_le_mul_of_nonneg_left hmR (by linarith only [hmR])
                    linarith only [h1, h2, hmR]
                  have hmpos : (0:ℝ) < m := by linarith only [hmR]
                  have hlogpos : 0 < Real.log m := Real.log_pos (by linarith only [hmR])
                  have hε0 : 0 ≤ epsilon m := by
                    unfold epsilon; exact mul_nonneg zero_le_two (Real.sqrt_nonneg _)
                  have hε1 : epsilon m < 1 := by
                    unfold epsilon
                    have h2 : Real.log m / m < 1 / 4 := by rw [div_lt_iff₀ hmpos]; linarith only [hlog]
                    have h3 : Real.sqrt (Real.log m / m) < 1 / 2 := by
                      rw [show (1:ℝ)/2 = Real.sqrt (1/4) by
                        rw [show (1:ℝ)/4 = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
                      exact Real.sqrt_lt_sqrt (div_nonneg hlogpos.le hmpos.le) h2
                    linarith only [h3]
                  have hs : 0 < Real.sqrt (m * Real.log m) := Real.sqrt_pos.2 (mul_pos hmpos hlogpos)
                  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
                  have hb1 : Real.sqrt (m * Real.log m) / (Real.sqrt (m * Real.log m) + n - 1) -
                      3 / Real.sqrt (m * Real.log m) ≤ 1 := by
                    have h1 : Real.sqrt (m * Real.log m) / (Real.sqrt (m * Real.log m) + n - 1) ≤ 1 :=
                      div_le_one_of_le₀ (by linarith only [hn']) (by linarith only [hn', hs])
                    have h2 : 0 < 3 / Real.sqrt (m * Real.log m) := div_pos three_pos hs
                    linarith only [h1, h2]
                  unfold delayFactor
                  rcases le_or_gt (Real.sqrt (m * Real.log m) / (Real.sqrt (m * Real.log m) + n - 1) -
                      3 / Real.sqrt (m * Real.log m)) 0 with h | h
                  · have := mul_nonpos_of_nonneg_of_nonpos (show (0:ℝ) ≤ 1 - epsilon m by linarith only [hε1]) h
                    linarith only [this]
                  · have := mul_le_mul_of_nonneg_left hb1 (show (0:ℝ) ≤ 1 - epsilon m by linarith only [hε1])
                    linarith only [this, hε0]
                have hmemrt : rtObj n m φ τ I c (toRTPolicy rt) πt ∈ {v : ℝ | ∃ r π, IsRTPolicy n m r ∧
                    IsRTStationary n m φ τ r π ∧ v = rtObj n m φ τ I c r π} :=
                  ⟨_, _, hpol, hπt, rfl⟩
                -- the two cases
                by_cases hq0 : qt = 0
                · ---------------- qt = 0
                  have hzt0 : ∀ i j, zt i j = 0 := by
                    intro i j
                    have h1 : zt i j ≤ ∑ j, zt i j :=
                      Finset.single_le_sum (fun j _ => hz0 i j) (Finset.mem_univ j)
                    have h2 := hzsum i
                    simp only [hq0, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h2
                    linarith only [h1, h2, hz0 i j]
                  have hV : alg8Obj φ I c qt zt = 0 := by
                    simp [alg8Obj, hq0, hzt0]
                  have hrt0 : ∀ i j, rt i j = 0 := by
                    intro i j; rw [hrtv, hzt0, zero_div]
                  refine ⟨fun Opt hOpt hO => ?_, fun hB r π hr hπ => ?_⟩
                  · have hle : rtObj n m φ τ I c (toRTPolicy rt) πt ≤ Opt := hOpt.1 hmemrt
                    have hOle : Opt ≤ 0 := by
                      rw [← hV]; refine hOpt.2 ?_
                      rintro v ⟨r, π, hr, hπ, rfl⟩; exact hUB r π hr hπ
                    have hneg : Opt < 0 := lt_of_le_of_ne hOle hO
                    rw [le_div_iff_of_neg hneg]
                    have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hdf1) hneg.le
                    have h2 : (1 - delayFactor n m) * Opt = Opt - delayFactor n m * Opt := by ring
                    linarith only [h1, h2, hle]
                  · have hB' : ∀ i, 0 ≤ ∑ j, φ i j * I i j := hB.resolve_left (fun h => h hq0)
                    have hobj0 : 0 ≤ rtObj n m φ τ I c (toRTPolicy rt) πt := by
                      unfold rtObj
                      refine Finset.sum_nonneg fun s _ => mul_nonneg (hπt.1 s) ?_
                      have h2 : (∑ k, ∑ i, (s.2.1 k i : ℝ) / τ k i * ∑ j, toRTPolicy rt s k i j * c i j) = 0 := by
                        simp [toRTPolicy, hrt0]
                      rw [h2, sub_zero]
                      refine Finset.sum_nonneg fun k _ => ?_
                      by_cases hk : 0 < s.1 k
                      · simp only [hk, if_true]; exact hB' k
                      · simp [hk]
                    have hle := hUB r π hr hπ
                    rw [hV] at hle
                    rw [max_eq_right hle, mul_zero]
                    exact hobj0
                · ---------------- qt ≠ 0
                  have hconnS := hconn.resolve_right hq0
                  have hcirc' : ∀ i, ∑ k, (φ k i * qt k + zt k i) = ∑ j, (φ i j * qt i + zt i j) :=
                    fun i => hcirc i
                  have hq0' : ∀ k, 0 ≤ qt k := fun k => (hq01' k).1
                  have hφb0 : ∀ a b, 0 ≤ inducedDemand φ (fun _ _ => 1) rt a b := by
                    intro a b; unfold inducedDemand
                    have h1 : 0 ≤ 1 - ∑ k, rt b k := by linarith only [hR1 b]
                    exact add_nonneg (mul_nonneg (mul_nonneg (hφ a b) zero_le_one) h1)
                      (Finset.sum_nonneg fun k _ => mul_nonneg (mul_nonneg (hφ a k) zero_le_one) (hR k b))
                  have htraf : ∀ k, ∑ a, qt a * inducedDemand φ (fun _ _ => 1) rt a k = (∑ j, φ k j) * qt k := by
                    intro k
                    unfold inducedDemand
                    simp only [mul_one]
                    have e1 : ∑ a, qt a * (φ a k * (1 - ∑ l, rt k l) + ∑ l, φ a l * rt l k) =
                        (∑ a, φ a k * qt a) * (1 - ∑ l, rt k l) + ∑ l, rt l k * ∑ a, φ a l * qt a := by
                      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
                      congr 1
                      · exact Finset.sum_congr rfl fun a _ => by ring
                      · rw [Finset.sum_comm]
                        exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring
                    rw [e1]
                    have e2 : ∀ l, rt l k * ∑ a, φ a l * qt a = zt l k := fun l => (hz l k).symm
                    have e3 : (∑ a, φ a k * qt a) * (∑ l, rt k l) = ∑ l, zt k l := by
                      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by rw [hz k l]; ring
                    simp only [e2]
                    have hc := hcirc' k
                    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hc
                    have e4 : ∑ j, φ k j * qt k = (∑ j, φ k j) * qt k := by rw [Finset.sum_mul]
                    linear_combination hc - e3 + e4
                  have hqpos : ∀ k, 0 < qt k := by
                    have hprop : ∀ a b, Relation.ReflTransGen (fun a b => a ≠ b ∧
                        0 < inducedDemand φ (fun _ _ => 1) rt a b * (fun _ _ => (1:ℝ)) a b) a b →
                        qt b = 0 → qt a = 0 := by
                      intro a b h
                      induction h with
                      | refl => exact id
                      | tail _ hbc ih =>
                        rename_i b' c' _
                        intro hc0; apply ih
                        have hsum := htraf c'
                        rw [hc0, mul_zero] at hsum
                        have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
                          mul_nonneg (hq0' a) (hφb0 a c'))).1 hsum b' (Finset.mem_univ _)
                        have hpos : 0 < inducedDemand φ (fun _ _ => 1) rt b' c' := by
                          have := hbc.2; simpa using this
                        rcases mul_eq_zero.1 hall with h | h
                        · exact h
                        · exact absurd h hpos.ne'
                    obtain ⟨k0, hk0⟩ : ∃ k0, qt k0 ≠ 0 := by
                      by_contra hcon; simp only [ne_eq, not_exists, not_not] at hcon; exact hq0 (funext hcon)
                    intro k
                    rcases (hq0' k).eq_or_lt with h | h
                    · exact absurd (hprop k0 k (hconnS k0 k) h.symm) hk0
                    · exact h
                  obtain ⟨ν, hν⟩ : ∃ ν : RTState n → ℝ, ∀ s : RTState n, ν s = (∏ k, qt k ^ s.1 k) *
                      ((∏ a, ∏ b, (τ a b * φ a b * qt a) ^ s.2.1 a b / ((s.2.1 a b).factorial : ℝ)) *
                       (∏ a, ∏ b, (τ a b * zt a b) ^ s.2.2 a b / ((s.2.2 a b).factorial : ℝ))) :=
                    ⟨_, fun s => rfl⟩
                  have hbal := pPF1 φ τ hφ hτ qt zt rt hq0' hR hR1 hz hcirc' ν hν
                  have hπν := pPF2 φ τ hφ hτ qt zt rt hqpos hR hR1 hz hcirc' hconnS ν hν hbal πt hπt
                  have hK := pK (by omega) φ τ I c hφ hτ qt zt rt hq0' hz ν hν πt hπν
                  have hG1 := pBS1 qt (fun a b => τ a b * φ a b * qt a) (fun a b => τ a b * zt a b) ν hν
                  clear pPF1 pPF2 pK pBS1
                  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = ∑ a, ∑ b, (τ a b * φ a b * qt a + τ a b * zt a b) := ⟨_, rfl⟩
                  have hG1' : ∀ N, ∑ t ∈ rtStates n N, ν t = ∑ k ∈ range (N + 1),
                      (∑ x ∈ states n k, ∏ i, qt i ^ x i) * (L ^ (N - k) / ((N - k).factorial : ℝ)) := by
                    intro N; rw [hLdef]; exact hG1 N
                  have hL0 : 0 ≤ L := by
                    rw [hLdef]
                    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
                      add_nonneg (mul_nonneg (mul_nonneg (hτ a b).le (hφ a b)) (hq0' a)) (mul_nonneg (hτ a b).le (hz0 a b))
                  have hL : L ≤ m := by
                    rw [hLdef]
                    have : ∑ a, ∑ b, (τ a b * φ a b * qt a + τ a b * zt a b) =
                        ∑ i, ∑ j, τ i j * (φ i j * qt i + zt i j) :=
                      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
                    rw [this]; exact hrate
                  have hB := pBSc hm hn (fun k => ∑ x ∈ states n k, ∏ i, qt i ^ x i)
                    (fun k => Finset.sum_nonneg fun x _ => Finset.prod_nonneg fun i _ => pow_nonneg (hq0' i) _)
                    (pBS2 qt hq01') L hL0 hL
                  clear pBSc pBS2
                  have hdfG : delayFactor n m * ∑ t ∈ rtStates n m, ν t ≤ ∑ t ∈ rtStates n (m - 1), ν t := by
                    rw [hG1' m, hG1' (m - 1)]; exact hB
                  -- positivity of the normalising constant
                  have hν0 : ∀ s, 0 ≤ ν s := fun s => by
                    rw [hν]
                    exact mul_nonneg (Finset.prod_nonneg fun k _ => pow_nonneg (hq0' k) _)
                      (mul_nonneg (Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun b _ =>
                        div_nonneg (pow_nonneg (mul_nonneg (mul_nonneg (hτ a b).le (hφ a b)) (hq0' a)) _)
                          (Nat.cast_nonneg _))
                        (Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun b _ =>
                          div_nonneg (pow_nonneg (mul_nonneg (hτ a b).le (hz0 a b)) _) (Nat.cast_nonneg _)))
                  obtain ⟨k0⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
                  have hs0 : ((fun k => if k = k0 then m else 0, fun _ _ => 0, fun _ _ => 0) : RTState n) ∈
                      rtStates n m := by
                    simp only [rtStates, mem_filter, mem_product, Fintype.mem_piFinset, mem_range]
                    refine ⟨⟨fun k => by split_ifs <;> omega, fun a b => by omega, fun a b => by omega⟩, ?_⟩
                    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero]
                  have hνs0 : 0 < ν ((fun k => if k = k0 then m else 0, fun _ _ => 0, fun _ _ => 0) : RTState n) := by
                    rw [hν]
                    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, Finset.prod_const_one, mul_one]
                    exact Finset.prod_pos fun k _ => pow_pos (hqpos k) _
                  have hZpos : 0 < ∑ t ∈ rtStates n m, ν t :=
                    lt_of_lt_of_le hνs0 (Finset.single_le_sum (fun t _ => hν0 t) hs0)
                  have hG10 : 0 ≤ ∑ t ∈ rtStates n (m - 1), ν t := Finset.sum_nonneg fun t _ => hν0 t
                  -- conclusions about X = rtObj of rt
                  have hKV : rtObj n m φ τ I c (toRTPolicy rt) πt * ∑ t ∈ rtStates n m, ν t =
                      (∑ t ∈ rtStates n (m - 1), ν t) * alg8Obj φ I c qt zt := hK
                  clear hK hG1 hG1' hB hbal hπν
                  obtain ⟨X, hX⟩ : ∃ X, X = rtObj n m φ τ I c (toRTPolicy rt) πt := ⟨_, rfl⟩
                  obtain ⟨V, hVd⟩ : ∃ V, V = alg8Obj φ I c qt zt := ⟨_, rfl⟩
                  obtain ⟨Z, hZd⟩ : ∃ Z, Z = ∑ t ∈ rtStates n m, ν t := ⟨_, rfl⟩
                  obtain ⟨G1, hG1d⟩ : ∃ G1, G1 = ∑ t ∈ rtStates n (m - 1), ν t := ⟨_, rfl⟩
                  rw [← hX, ← hVd, ← hZd, ← hG1d] at hKV
                  rw [← hZd, ← hG1d] at hdfG
                  rw [← hZd] at hZpos
                  rw [← hG1d] at hG10
                  rw [← hVd] at hV0
                  have hXdf : delayFactor n m * V ≤ X := by
                    have h1 : 0 ≤ V * (G1 - delayFactor n m * Z) :=
                      mul_nonneg hV0 (by linarith only [hdfG])
                    have h2 : (X - delayFactor n m * V) * Z = V * (G1 - delayFactor n m * Z) := by
                      linear_combination hKV
                    have h3 : 0 ≤ (X - delayFactor n m * V) * Z := h2 ▸ h1
                    have h4 := (mul_nonneg_iff_of_pos_right hZpos).1 h3
                    linarith only [h4]
                  have hX0 : 0 ≤ X := by
                    have h1 : 0 ≤ X * Z := by rw [hKV]; exact mul_nonneg hG10 hV0
                    exact (mul_nonneg_iff_of_pos_right hZpos).1 h1
                  rw [← hX] at hmemrt ⊢
                  rw [← hVd] at hUB
                  refine ⟨fun Opt hOpt hO => ?_, fun _ r π hr hπ => ?_⟩
                  · have hle : X ≤ Opt := hOpt.1 hmemrt
                    have hOle : Opt ≤ V := by
                      refine hOpt.2 ?_
                      rintro v ⟨r, π, hr, hπ, rfl⟩; exact hUB r π hr hπ
                    have hpos : 0 < Opt := lt_of_le_of_ne (le_trans hX0 hle) (Ne.symm hO)
                    rw [le_div_iff₀ hpos]
                    rcases le_or_gt 0 (delayFactor n m) with hd | hd
                    · have := mul_le_mul_of_nonneg_left hOle hd
                      linarith only [this, hXdf]
                    · have := mul_neg_of_neg_of_pos hd hpos
                      linarith only [this, hX0]
                  · have hle := hUB r π hr hπ
                    have hmx : max (rtObj n m φ τ I c r π) 0 ≤ V := max_le hle hV0
                    rcases le_or_gt 0 (delayFactor n m) with hd | hd
                    · have := mul_le_mul_of_nonneg_left hmx hd
                      linarith only [this, hXdf]
                    · have := mul_nonpos_of_nonpos_of_nonneg hd.le (le_max_right (rtObj n m φ τ I c r π) 0)
                      linarith only [this, hX0]
