-- Prove2me | solution 1 for SharedVehicleApprox.Pricing.Supplement.theorem_22
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:05:56.727905+00:00
-- url     : https://prove2.me/submissions/034e9757-31ef-4762-b44c-c667a94008d9

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_SupplyRedirection
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_Algorithm3

open Finset QueueingFundamentals.Networks

open SharedVehicleApprox
open SharedVehicleApprox.Pricing
open SharedVehicleApprox.Pricing.Supplement

/-- Theorem 22, p. 26 (corrected: the routing of `(q̃, r̃)` is strongly connected, unless `q̃ = 0`,
and the denominator misprint in `r̃` is repaired): the state-independent prices and redirection
probabilities returned by Algorithm 3 earn at least `m/(m+n−1)` times the objective of every
state-dependent pricing and redirection policy under every stationary law of it. -/
theorem solution {n m : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (I : Fin n → Fin n → ℝ → ℝ)
    (hR : ∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (rewardCurve I i j))
    (c qt zt rt : Fin n → Fin n → ℝ) (hopt : IsAlg3Optimal φ I c qt zt)
    (hrt : rt = redirectProb φ qt zt)
    (hconn : SupportConnected (inducedDemand φ qt rt) (fun _ _ => 1) ∨ qt = 0)
    (πt : (Fin n → ℕ) → ℝ)
    (hπt : IsRedirectStationary n m φ (toPolicy qt) (toRedirect rt) πt)
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (r : (Fin n → ℕ) → Fin n → Fin n → Fin n → ℝ)
    (π : (Fin n → ℕ) → ℝ)
    (hqr : IsRedirectPolicy n m q r) (hπ : IsRedirectStationary n m φ q r π) :
    (m : ℝ) / ((m : ℝ) + n - 1) * redirectObj n m φ I c q r π ≤
      redirectObj n m φ I c (toPolicy qt) (toRedirect rt) πt := by
        classical
        rcases Nat.eq_zero_or_pos n with hn0 | hnpos
        · subst hn0; simp [redirectObj]
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · subst hm0
          have hR0 : redirectObj n 0 φ I c (toPolicy qt) (toRedirect rt) πt = 0 := by
            unfold redirectObj
            apply Finset.sum_eq_zero
            intro x hx
            simp [states] at hx
            simp [toPolicy, hx.1, rewardCurve]
          rw [hR0]; simp
        obtain ⟨⟨hqt01, hzt0, hcirc, hzle⟩, hoptle⟩ := hopt
        obtain ⟨hπ0, hπoff, hπ1, hπbal⟩ := hπ
        obtain ⟨hπt0, hπtoff, hπt1, hπtbal⟩ := hπt
        obtain ⟨hqpol, hrpol⟩ := hqr
        have hmem : ∀ (x : Fin n → ℕ) (N : ℕ), x ∈ states n N ↔ (∀ i, x i ≤ N) ∧ ∑ i, x i = N := by
          intro x N; simp [states, Fintype.mem_piFinset, Nat.lt_succ_iff]
        have hsub : ∀ (t : Fin n) (x : Fin n → ℕ), 1 ≤ x t → x - Pi.single t 1 + Pi.single t 1 = x := by
          intro t x h; ext s; by_cases hs : s = t
          · subst hs; simp; omega
          · simp [Pi.single_apply, hs]
        have hsumadd : ∀ (t : Fin n) (y : Fin n → ℕ), ∑ s, ((y + Pi.single t (1:ℕ) : Fin n → ℕ)) s = ∑ s, y s + 1 := by
          intro t y; simp [Finset.sum_add_distrib]
        have hmemadd : ∀ (t : Fin n) (y : Fin n → ℕ), y ∈ states n (m-1) → y + Pi.single t 1 ∈ states n m := by
          intro t y hy
          rw [hmem] at hy ⊢
          refine ⟨fun i => ?_, by rw [hsumadd, hy.2]; omega⟩
          have := hy.1 i
          by_cases hs : i = t
          · subst hs; simp; omega
          · simp [Pi.single_apply, hs]; omega
        have hmemsub : ∀ (t : Fin n) (x : Fin n → ℕ), x ∈ states n m → 1 ≤ x t → x - Pi.single t 1 ∈ states n (m-1) := by
          intro t x hx h1
          rw [hmem] at hx ⊢
          have h2 := hsumadd t (x - Pi.single t 1)
          rw [hsub t x h1, hx.2] at h2
          refine ⟨fun i => ?_, by omega⟩
          have := hx.1 i
          obtain ⟨w, hw⟩ : ∃ w : Fin n → ℕ, w = x - Pi.single t 1 := ⟨_, rfl⟩
          rw [← hw] at h2 ⊢
          have h3 : w i ≤ x i := by rw [hw]; simp
          by_cases hs : i = t
          · subst hs; rw [hw]; simp; omega
          · have : ∑ s, w s ≥ w i :=
              Finset.single_le_sum (f := fun s => w s) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
            omega
        have hbij : ∀ (t : Fin n) (F : (Fin n → ℕ) → ℝ), ∑ x ∈ (states n m).filter (fun x => 1 ≤ x t), F x = ∑ y ∈ states n (m-1), F (y + Pi.single t 1) := by
          intro t F
          symm
          apply Finset.sum_nbij' (fun y => y + Pi.single t 1) (fun x => x - Pi.single t 1)
          · intro y hy
            simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
            exact ⟨hmemadd t y hy, by simp⟩
          · intro x hx
            simp only [Finset.mem_coe, Finset.mem_filter] at hx ⊢
            exact hmemsub t x hx.1 hx.2
          · intro y hy; ext s; simp
          · intro x hx
            simp only [Finset.mem_coe, Finset.mem_filter] at hx
            exact hsub t x hx.2
          · intro y hy; rfl
        have hms : ∀ (x : Fin n → ℕ) (k j : Fin n), k ≠ j → 1 ≤ x j → moveState x k j = x - Pi.single j 1 + Pi.single k 1 := by
          intro x k j hkj hx; ext s
          by_cases hsk : s = k
          · subst hsk; simp [moveState, Pi.single_apply, hkj]
          · by_cases hsj : s = j
            · subst hsj; simp [moveState, Pi.single_apply, hsk]
            · simp [moveState, Pi.single_apply, hsk, hsj]
        have hmove : ∀ k j : Fin n, k ≠ j → ∀ F : (Fin n → ℕ) → ℝ, ∑ x ∈ (states n m).filter (fun x => 1 ≤ x j), F (moveState x k j) = ∑ y ∈ (states n m).filter (fun y => 1 ≤ y k), F y := by
          intro k j hkj F
          rw [hbij j, hbij k]
          apply Finset.sum_congr rfl
          intro w hw
          congr 1
          rw [hms _ k j hkj (by simp)]
          ext s; simp
        -- flow identity for (q, r, π)
        obtain ⟨ρ, hρdef⟩ : ∃ ρ : (Fin n → ℕ) → Fin n → Fin n → ℝ, ρ = redirectRate φ q r := ⟨_, rfl⟩
        rw [← hρdef] at hπbal
        simp only [one_mul] at hπbal
        have hρ0 : ∀ y ∈ states n m, ∀ k j, y k = 0 → ρ y k j = 0 := by
          intro y hy k j hk
          have h1 : ∀ i, q y k i = 0 := fun i => ((hqpol y hy k i).2.2 hk)
          simp [hρdef, redirectRate, h1]
        have hkey : ∀ (i k j : Fin n), ∑ x ∈ states n m, (x i : ℝ) * inflowTerm (fun _ _ => 1) ρ π x k j
            = ∑ y ∈ states n m, ((y i : ℝ) + (if i = j then 1 else 0) - (if i = k then 1 else 0)) * (π y * ρ y k j) := by
          intro i k j
          by_cases hkj : k = j
          · subst hkj
            apply Finset.sum_congr rfl
            intro x hx
            simp [inflowTerm]; try ring
          · obtain ⟨F, hF⟩ : ∃ F : (Fin n → ℕ) → ℝ, F = fun y : Fin n → ℕ => ((y i : ℝ) + (if i = j then 1 else 0) - (if i = k then 1 else 0)) * (π y * ρ y k j) := ⟨_, rfl⟩
            have e1 : ∑ x ∈ states n m, (x i : ℝ) * inflowTerm (fun _ _ => 1) ρ π x k j
                = ∑ x ∈ (states n m).filter (fun x => 1 ≤ x j), F (moveState x k j) := by
              rw [Finset.sum_filter, hF]
              apply Finset.sum_congr rfl
              intro x hx
              by_cases h1 : 1 ≤ x j
              · simp only [inflowTerm, hkj, if_false, h1, if_true]
                have hxi : ((moveState x k j) i : ℝ) = (x i : ℝ) - (if i = j then 1 else 0) + (if i = k then 1 else 0) := by
                  rw [hms x k j hkj h1]
                  by_cases hik : i = k
                  · subst hik; simp [hkj]
                  · by_cases hij : i = j
                    · subst hij; simp [hik, Nat.cast_sub h1]
                    · simp [hik, hij]
                rw [hxi]; ring
              · simp [inflowTerm, hkj, h1]
            rw [e1, hmove k j hkj F, Finset.sum_filter, hF]
            apply Finset.sum_congr rfl
            intro y hy
            by_cases h : 1 ≤ y k
            · rw [if_pos h]
            · rw [if_neg h, hρ0 y hy k j (by omega)]; simp
        have hflow : ∀ i, ∑ x ∈ states n m, π x * (∑ k, ρ x k i - ∑ j, ρ x i j) = 0 := by
          intro i
          have h1 : ∑ x ∈ states n m, (x i : ℝ) * (π x * ∑ k, ∑ j, ρ x k j)
              = ∑ k, ∑ j, ∑ x ∈ states n m, (x i : ℝ) * inflowTerm (fun _ _ => 1) ρ π x k j := by
            rw [Finset.sum_congr rfl (fun x hx => by rw [hπbal x hx])]
            simp only [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro k _
            rw [Finset.sum_comm]
          simp only [hkey] at h1
          have h2 : ∑ k, ∑ j, ∑ y ∈ states n m, ((y i : ℝ) + (if i = j then 1 else 0) - (if i = k then 1 else 0)) * (π y * ρ y k j)
              = ∑ y ∈ states n m, (y i : ℝ) * (π y * ∑ k, ∑ j, ρ y k j) + ∑ y ∈ states n m, π y * (∑ k, ρ y k i - ∑ j, ρ y i j) := by
            rw [← Finset.sum_add_distrib]
            rw [Finset.sum_comm]
            rw [Finset.sum_congr rfl (fun k _ => Finset.sum_comm)]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro y _
            simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
              Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, mul_sub]
            rw [Finset.sum_comm (f := fun x x_1 => if i = x then π y * ρ y x_1 x else 0)]
            simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
            rw [Finset.sum_comm (f := fun x x_1 => (y i : ℝ) * (π y * ρ y x_1 x))]
            ring
          linarith
        -- upper bound
        obtain ⟨qb, hqb⟩ : ∃ qb : Fin n → Fin n → ℝ, qb = fun k i => ∑ x ∈ states n m, π x * q x k i := ⟨_, rfl⟩
        obtain ⟨zb, hzb⟩ : ∃ zb : Fin n → Fin n → ℝ,
            zb = fun i j => ∑ x ∈ states n m, π x * ∑ k, φ k i * q x k i * r x k i j := ⟨_, rfl⟩
        have hρout : ∀ x i, ∑ j, ρ x i j = ∑ j, φ i j * q x i j := by
          intro x i; rw [hρdef]
          simp only [redirectRate, Finset.sum_add_distrib, mul_sub, mul_one, Finset.sum_sub_distrib]
          rw [Finset.sum_comm (f := fun j l => φ i l * q x i l * r x i l j)]
          simp only [Finset.mul_sum]; ring
        have hρin : ∀ x i, ∑ k, ρ x k i = ∑ k, φ k i * q x k i - ∑ l, ∑ k, φ k i * q x k i * r x k i l
            + ∑ l, ∑ k, φ k l * q x k l * r x k l i := by
          intro x i; rw [hρdef]
          simp only [redirectRate, Finset.sum_add_distrib, mul_sub, mul_one, Finset.sum_sub_distrib, Finset.mul_sum]
          rw [Finset.sum_comm (f := fun l k => φ k i * q x k i * r x k i l)]
          rw [Finset.sum_comm (f := fun l k => φ k l * q x k l * r x k l i)]
        have E1 : ∀ i, ∑ k, φ k i * qb k i = ∑ x ∈ states n m, π x * ∑ k, φ k i * q x k i := by
          intro i; rw [hqb]; simp only [Finset.mul_sum]; rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro x _; ring
        have E1' : ∀ i, ∑ j, φ i j * qb i j = ∑ x ∈ states n m, π x * ∑ j, φ i j * q x i j := by
          intro i; rw [hqb]; simp only [Finset.mul_sum]; rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro x _; ring
        have E2 : ∀ i, ∑ l, zb i l = ∑ x ∈ states n m, π x * ∑ l, ∑ k, φ k i * q x k i * r x k i l := by
          intro i; rw [hzb]; simp only [Finset.mul_sum]; rw [Finset.sum_comm]
        have E3 : ∀ i, ∑ l, zb l i = ∑ x ∈ states n m, π x * ∑ l, ∑ k, φ k l * q x k l * r x k l i := by
          intro i; rw [hzb]; simp only [Finset.mul_sum]; rw [Finset.sum_comm]
        have hfeas : IsAlg3Feasible φ qb zb := by
          refine ⟨fun i j => ⟨?_, ?_⟩, fun i j => ?_, fun i => ?_, fun i => ?_⟩
          · rw [hqb]; apply Finset.sum_nonneg; intro x hx; exact mul_nonneg (hπ0 x) (hqpol x hx i j).1
          · rw [hqb, ← hπ1]; apply Finset.sum_le_sum; intro x hx
            exact mul_le_of_le_one_right (hπ0 x) (hqpol x hx i j).2.1
          · rw [hzb]; apply Finset.sum_nonneg; intro x hx; apply mul_nonneg (hπ0 x)
            apply Finset.sum_nonneg; intro k _
            exact mul_nonneg (mul_nonneg (hφ k i) (hqpol x hx k i).1) ((hrpol x hx k i).1 j)
          · have h := hflow i
            simp only [mul_sub, Finset.sum_sub_distrib, hρout, hρin, mul_add, Finset.sum_add_distrib] at h
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, E1, E1', E2, E3]
            linarith
          · rw [E2, E1]
            apply Finset.sum_le_sum; intro x hx
            apply mul_le_mul_of_nonneg_left _ (hπ0 x)
            rw [Finset.sum_comm]
            apply Finset.sum_le_sum; intro k _
            rw [← Finset.mul_sum]
            exact mul_le_of_le_one_right (mul_nonneg (hφ k i) (hqpol x hx k i).1) (hrpol x hx k i).2
        have hUpper1 : redirectObj n m φ I c q r π ≤ alg3Obj φ I c qb zb := by
          have hJ : ∀ k i, ∑ x ∈ states n m, π x * rewardCurve I k i (q x k i) ≤ rewardCurve I k i (qb k i) := by
            intro k i
            have := (hR k i).le_map_sum (t := states n m) (w := π) (p := fun x => q x k i)
              (fun x _ => hπ0 x) hπ1 (fun x hx => ⟨(hqpol x hx k i).1, (hqpol x hx k i).2.1⟩)
            simpa [smul_eq_mul, hqb] using this
          have hcost : ∑ x ∈ states n m, π x * ∑ k, ∑ i, φ k i * (q x k i * ∑ j, r x k i j * c i j)
              = ∑ i, ∑ j, c i j * zb i j := by
            rw [hzb]; simp only [Finset.mul_sum]
            have step1 : ∀ x, ∑ k, ∑ i, ∑ j, π x * (φ k i * (q x k i * (r x k i j * c i j)))
                = ∑ i, ∑ j, ∑ k, c i j * (π x * (φ k i * q x k i * r x k i j)) := by
              intro x; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _; ring
            rw [Finset.sum_congr rfl (fun x _ => step1 x), Finset.sum_comm]
            apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
          have hrew : ∑ x ∈ states n m, π x * ∑ k, ∑ i, φ k i * rewardCurve I k i (q x k i)
              = ∑ k, ∑ i, φ k i * ∑ x ∈ states n m, π x * rewardCurve I k i (q x k i) := by
            simp only [Finset.mul_sum]
            rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _; rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro x _; ring
          have hsplit : redirectObj n m φ I c q r π = ∑ x ∈ states n m, π x * ∑ k, ∑ i, φ k i * rewardCurve I k i (q x k i)
              - ∑ x ∈ states n m, π x * ∑ k, ∑ i, φ k i * (q x k i * ∑ j, r x k i j * c i j) := by
            unfold redirectObj
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl; intro x _
            rw [← mul_sub, ← Finset.sum_sub_distrib]
            congr 1; apply Finset.sum_congr rfl; intro k _
            rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
          rw [hsplit, hcost, hrew]
          unfold alg3Obj
          simp only [Finset.sum_sub_distrib]
          have : ∑ k, ∑ i, φ k i * ∑ x ∈ states n m, π x * rewardCurve I k i (q x k i) ≤ ∑ k, ∑ i, φ k i * rewardCurve I k i (qb k i) := by
            apply Finset.sum_le_sum; intro k _; apply Finset.sum_le_sum; intro i _
            exact mul_le_mul_of_nonneg_left (hJ k i) (hφ k i)
          linarith
        have hUpper : redirectObj n m φ I c q r π ≤ alg3Obj φ I c qt zt := hUpper1.trans (hoptle qb zb hfeas)
        -- facts about rt
        have hD0 : ∀ i, 0 ≤ ∑ k, φ k i * qt k i := fun i =>
          Finset.sum_nonneg (fun k _ => mul_nonneg (hφ k i) (hqt01 k i).1)
        have hDrt : ∀ i j, (∑ k, φ k i * qt k i) * rt i j = zt i j := by
          intro i j
          rw [hrt]; simp only [redirectProb]
          by_cases hD : ∑ k, φ k i * qt k i = 0
          · have h1 : zt i j = 0 := le_antisymm
              ((Finset.single_le_sum (fun k _ => hzt0 i k) (Finset.mem_univ j)).trans (by have := hzle i; rw [hD] at this; exact this))
              (hzt0 i j)
            rw [hD, h1]; simp
          · field_simp
        have hrt0 : ∀ i j, 0 ≤ rt i j := by
          intro i j; rw [hrt]; exact div_nonneg (hzt0 i j) (hD0 i)
        have hrtsum : ∀ i, ∑ j, rt i j ≤ 1 := by
          intro i; rw [hrt]; simp only [redirectProb]; rw [← Finset.sum_div]
          exact div_le_one_of_le₀ (hzle i) (hD0 i)
        obtain ⟨B, hB⟩ : ∃ B : Fin n → Fin n → ℝ,
            B = fun k i => φ k i * (rewardCurve I k i (qt k i) - qt k i * ∑ j, rt i j * c i j) := ⟨_, rfl⟩
        have hBsum : ∑ k, ∑ i, B k i = alg3Obj φ I c qt zt := by
          rw [hB]; unfold alg3Obj
          simp only [mul_sub, Finset.sum_sub_distrib]
          congr 1
          have h1 : ∀ i, ∑ k, φ k i * (qt k i * ∑ j, rt i j * c i j) = ∑ j, c i j * zt i j := by
            intro i
            have : ∀ j, c i j * zt i j = (∑ k, φ k i * qt k i) * rt i j * c i j := by intro j; rw [hDrt]; ring
            simp only [this, Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _; ring
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun i _ => h1 i)
        have hRHS : redirectObj n m φ I c (toPolicy qt) (toRedirect rt) πt
            = ∑ k, (∑ x ∈ states n m, πt x * (if 0 < x k then 1 else 0)) * ∑ i, B k i := by
          unfold redirectObj
          have h1 : ∀ x : Fin n → ℕ, ∀ k i, φ k i * (rewardCurve I k i (toPolicy qt x k i)
              - toPolicy qt x k i * ∑ j, toRedirect rt x k i j * c i j) = (if 0 < x k then 1 else 0) * B k i := by
            intro x k i
            rw [hB]; simp only [toPolicy, toRedirect]
            split_ifs <;> simp [rewardCurve]
          simp only [h1]
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro k _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro x _
          ring
        have hcoef : 0 ≤ (m : ℝ) / ((m : ℝ) + n - 1) := by
          apply div_nonneg (by positivity)
          have : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
          linarith
        rcases hconn with hconn | hq0
        swap
        · subst hq0
          have hB0 : ∀ k i, B k i = 0 := by intro k i; rw [hB]; simp [rewardCurve]
          have hR0 : redirectObj n m φ I c (toPolicy 0) (toRedirect rt) πt = 0 := by
            rw [hRHS]; simp [hB0]
          have hA0 : alg3Obj φ I c 0 zt = 0 := by rw [← hBsum]; simp [hB0]
          rw [hR0]; rw [hA0] at hUpper
          exact mul_nonpos_of_nonneg_of_nonpos hcoef hUpper
        -- connected case
        obtain ⟨φb, hφb⟩ : ∃ φb : Fin n → Fin n → ℝ, φb = inducedDemand φ qt rt := ⟨_, rfl⟩
        rw [← hφb] at hconn
        have hφb0 : ∀ i j, 0 ≤ φb i j := by
          intro i j; rw [hφb]; unfold inducedDemand
          apply add_nonneg
          · exact mul_nonneg (mul_nonneg (hφ i j) (hqt01 i j).1) (by linarith [hrtsum j])
          · exact Finset.sum_nonneg (fun k _ => mul_nonneg (mul_nonneg (hφ i k) (hqt01 i k).1) (hrt0 k j))
        have hrow : ∀ j, ∑ i, φb j i = ∑ i, φ j i * qt j i := by
          intro j; rw [hφb]; unfold inducedDemand
          simp only [Finset.sum_add_distrib, mul_sub, mul_one, Finset.sum_sub_distrib]
          rw [Finset.sum_comm (f := fun i k => φ j k * qt j k * rt k i)]
          simp only [Finset.mul_sum]; ring
        have hcol : ∀ j, ∑ i, φb i j = ∑ i, φ j i * qt j i := by
          intro j; rw [hφb]; unfold inducedDemand
          simp only [Finset.sum_add_distrib, mul_sub, mul_one, Finset.sum_sub_distrib]
          have e1 : ∑ i, φ i j * qt i j * ∑ k, rt j k = ∑ k, zt j k := by
            rw [← Finset.sum_mul, Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => hDrt j k)
          have e2 : ∑ i, ∑ k, φ i k * qt i k * rt k j = ∑ k, zt k j := by
            rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _; rw [← Finset.sum_mul]; exact hDrt k j
          have e3 := hcirc j
          simp only [Finset.sum_add_distrib] at e3
          rw [e1, e2]; linarith
        obtain ⟨ρt, hρt⟩ : ∃ ρt : (Fin n → ℕ) → Fin n → Fin n → ℝ,
            ρt = redirectRate φ (toPolicy qt) (toRedirect rt) := ⟨_, rfl⟩
        rw [← hρt] at hπtbal
        simp only [one_mul] at hπtbal
        have hρtv : ∀ x k j, ρt x k j = if 0 < x k then φb k j else 0 := by
          intro x k j; rw [hρt, hφb]; unfold redirectRate inducedDemand toPolicy toRedirect
          split_ifs <;> simp
        have hne : (states n m).Nonempty := Finset.nonempty_of_sum_ne_zero (by rw [hπt1]; norm_num)
        obtain ⟨x0, hx0, hx0max⟩ := Finset.exists_max_image (states n m) πt hne
        obtain ⟨M, hM⟩ : ∃ M, M = πt x0 := ⟨_, rfl⟩
        have hle : ∀ y ∈ states n m, πt y ≤ M := by rw [hM]; exact hx0max
        have hmsmem : ∀ x ∈ states n m, ∀ i j, i ≠ j → 1 ≤ x j → moveState x i j ∈ states n m := by
          intro x hx i j hij h; rw [hms x i j hij h]; exact hmemadd i _ (hmemsub j x hx h)
        have hstep : ∀ x ∈ states n m, πt x = M → ∀ i a, i ≠ a → 1 ≤ x a → 0 < φb i a →
            πt (moveState x i a) = M := by
          intro x hx hxM i a hia hxa hpos
          have hbal := hπtbal x hx
          have hTU : ∀ i j, inflowTerm (fun _ _ => 1) ρt πt x i j ≤ M * (if 1 ≤ x j then φb i j else 0) := by
            intro i j
            by_cases hij : i = j
            · subst hij
              rw [show inflowTerm (fun _ _ => 1) ρt πt x i i = πt x * ρt x i i by simp [inflowTerm]]
              rw [hρtv, hxM]
              by_cases h : 1 ≤ x i
              · simp [h, show 0 < x i by omega]
              · simp [h, show ¬ 0 < x i by omega]
            · simp only [inflowTerm, if_neg hij]
              by_cases h : 1 ≤ x j
              · rw [if_pos h, if_pos h, hρtv, if_pos (by simp [moveState])]
                simp only [mul_one]
                exact mul_le_mul_of_nonneg_right (hle _ (hmsmem x hx i j hij h)) (hφb0 i j)
              · rw [if_neg h, if_neg h]; simp
          have hsum : ∑ i, ∑ j, inflowTerm (fun _ _ => 1) ρt πt x i j
              = ∑ i, ∑ j, M * (if 1 ≤ x j then φb i j else 0) := by
            rw [← hbal, hxM]
            simp only [hρtv, ← Finset.mul_sum]
            congr 1
            rw [Finset.sum_comm (f := fun i j => if 1 ≤ x j then φb i j else 0)]
            apply Finset.sum_congr rfl; intro b _
            by_cases h : 1 ≤ x b
            · simp only [show 0 < x b by omega, h, if_true]; rw [hrow, hcol]
            · simp only [show ¬ 0 < x b by omega, h, if_false, Finset.sum_const_zero]
          have hnn : ∀ i j, 0 ≤ M * (if 1 ≤ x j then φb i j else 0) - inflowTerm (fun _ _ => 1) ρt πt x i j :=
            fun i j => sub_nonneg.mpr (hTU i j)
          have hz : ∑ i, ∑ j, (M * (if 1 ≤ x j then φb i j else 0) - inflowTerm (fun _ _ => 1) ρt πt x i j) = 0 := by
            simp only [Finset.sum_sub_distrib]; rw [hsum]; ring
          rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hnn i j))] at hz
          have hz2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn i j)).mp (hz i (Finset.mem_univ _)) a
            (Finset.mem_univ _)
          simp only [inflowTerm, if_neg hia, if_pos hxa, hρtv] at hz2
          rw [if_pos (by simp [moveState])] at hz2
          have h3 : (πt (moveState x i a) - M) * φb i a = 0 := by linear_combination -hz2
          rcases mul_eq_zero.mp h3 with h | h
          · linarith
          · linarith
        have hpath : ∀ i j, Relation.ReflTransGen (fun a b => a ≠ b ∧ 0 < φb a b * 1) i j →
            ∀ x ∈ states n m, πt x = M → 1 ≤ x j →
              (x - Pi.single j 1 + Pi.single i 1 ∈ states n m ∧ πt (x - Pi.single j 1 + Pi.single i 1) = M) := by
          intro i j h
          induction h using Relation.ReflTransGen.head_induction_on with
          | refl => intro x hx hxM hxj; rw [hsub j x hxj]; exact ⟨hx, hxM⟩
          | @head a b hab hbc ih =>
            intro x hx hxM hxj
            obtain ⟨hx', hx'M⟩ := ih x hx hxM hxj
            have hb : 1 ≤ (x - Pi.single j 1 + Pi.single b 1 : Fin n → ℕ) b := by simp
            have heq : moveState (x - Pi.single j 1 + Pi.single b 1 : Fin n → ℕ) a b = x - Pi.single j 1 + Pi.single a 1 := by
              rw [hms _ a b hab.1 hb]; ext s; simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
              split_ifs <;> omega
            rw [← heq]
            exact ⟨hmsmem _ hx' a b hab.1 hb, hstep _ hx' hx'M a b hab.1 hb (by simpa using hab.2)⟩
        have hall : ∀ d : ℕ, ∀ x ∈ states n m, πt x = M → ∀ y ∈ states n m, ∑ t, (x t - y t) = d → πt y = M := by
          intro d
          induction d with
          | zero =>
            intro x hx hxM y hy hd
            have hle2 : ∀ t ∈ Finset.univ, x t ≤ y t := by
              intro t _; have := (Finset.sum_eq_zero_iff.mp hd) t (Finset.mem_univ t); omega
            have hs : ∑ t, x t = ∑ t, y t := by rw [((hmem x m).mp hx).2, ((hmem y m).mp hy).2]
            have := (Finset.sum_eq_sum_iff_of_le hle2).mp hs
            have hxy : x = y := funext fun t => this t (Finset.mem_univ t)
            rw [← hxy]; exact hxM
          | succ d ih =>
            intro x hx hxM y hy hd
            obtain ⟨j, -, hj⟩ : ∃ j ∈ Finset.univ, y j < x j := by
              by_contra hcon; push_neg at hcon
              have : ∑ t, (x t - y t) = 0 :=
                Finset.sum_eq_zero (fun t _ => by have := hcon t (Finset.mem_univ t); omega)
              omega
            obtain ⟨i, hi⟩ : ∃ i, x i < y i := by
              by_contra hcon; push_neg at hcon
              have := Finset.sum_lt_sum (fun t _ => hcon t) ⟨j, Finset.mem_univ j, hj⟩
              rw [((hmem x m).mp hx).2, ((hmem y m).mp hy).2] at this
              omega
            have hij : i ≠ j := by rintro rfl; omega
            obtain ⟨hx', hx'M⟩ := hpath i j (hconn i j) x hx hxM (by omega)
            apply ih _ hx' hx'M y hy
            have hpt : ∀ t, x t - y t = ((x - Pi.single j 1 + Pi.single i 1 : Fin n → ℕ) t - y t) + (if t = j then 1 else 0) := by
              intro t
              simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
              by_cases htj : t = j
              · subst htj; simp [Ne.symm hij] <;> omega
              · by_cases hti : t = i
                · subst hti; simp [htj] <;> omega
                · simp [htj, hti]
            have : ∑ t, (x t - y t) = ∑ t, ((x - Pi.single j 1 + Pi.single i 1 : Fin n → ℕ) t - y t) + 1 := by
              rw [Finset.sum_congr rfl (fun t _ => hpt t), Finset.sum_add_distrib]; simp
            omega
        have hunif : ∀ y ∈ states n m, πt y = M := fun y hy => hall _ x0 hx0 hM.symm y hy rfl
        have hcardM : M * ((states n m).card : ℝ) = 1 := by
          rw [← hπt1, Finset.sum_congr rfl hunif, Finset.sum_const, nsmul_eq_mul]; ring
        have hcardk : ∀ k, (((states n m).filter (fun x => 1 ≤ x k)).card : ℝ) = (states n (m-1)).card := by
          intro k
          have := hbij k (fun _ => 1)
          simpa using this
        have h2 : ∀ y ∈ states n (m-1), ∑ t, (((y + Pi.single t 1 : Fin n → ℕ) t : ℕ) : ℝ) = (m : ℝ) + n - 1 := by
          intro y hy
          have hy2 := ((hmem y (m-1)).mp hy).2
          have e : ∀ t, (((y + Pi.single t 1 : Fin n → ℕ) t : ℕ) : ℝ) = (y t : ℝ) + 1 := by intro t; simp
          simp only [e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_one]
          rw [← Nat.cast_sum, hy2, Nat.cast_sub hmpos]; push_cast; ring
        have hdouble : (m : ℝ) * (states n m).card = ((m:ℝ) + n - 1) * (states n (m-1)).card := by
          have h1 : ∀ x ∈ states n m, (m : ℝ) = ∑ t, (x t : ℝ) := by
            intro x hx; rw [← ((hmem x m).mp hx).2]; push_cast; rfl
          calc (m : ℝ) * (states n m).card = ∑ x ∈ states n m, ∑ t, (x t : ℝ) := by
                rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]; exact Finset.sum_congr rfl h1
            _ = ∑ t, ∑ x ∈ states n m, (x t : ℝ) := Finset.sum_comm
            _ = ∑ t, ∑ x ∈ (states n m).filter (fun x => 1 ≤ x t), (x t : ℝ) := by
                apply Finset.sum_congr rfl; intro t _
                rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro x _
                split_ifs with h
                · rfl
                · have : x t = 0 := by omega
                  simp [this]
            _ = ∑ t, ∑ y ∈ states n (m-1), (((y + Pi.single t 1 : Fin n → ℕ) t : ℕ) : ℝ) := by
                apply Finset.sum_congr rfl; intro t _; exact hbij t (fun x => (x t : ℝ))
            _ = ∑ y ∈ states n (m-1), ∑ t, (((y + Pi.single t 1 : Fin n → ℕ) t : ℕ) : ℝ) := Finset.sum_comm
            _ = ∑ y ∈ states n (m-1), ((m : ℝ) + n - 1) := Finset.sum_congr rfl h2
            _ = ((m:ℝ) + n - 1) * (states n (m-1)).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        have hA : ∀ k, ∑ x ∈ states n m, πt x * (if 0 < x k then 1 else 0) = (m : ℝ) / ((m : ℝ) + n - 1) := by
          intro k
          have e1 : ∑ x ∈ states n m, πt x * (if 0 < x k then 1 else 0)
              = M * (((states n m).filter (fun x => 1 ≤ x k)).card : ℝ) := by
            rw [Finset.card_filter]
            push_cast
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro x hx
            rw [hunif x hx]
            by_cases h : 1 ≤ x k
            · simp [h, show 0 < x k by omega]
            · simp [h, show ¬ 0 < x k by omega]
          rw [e1, hcardk]
          have hpos : (0:ℝ) < (m : ℝ) + n - 1 := by
            have : (1:ℝ) ≤ n := by exact_mod_cast hnpos
            have : (1:ℝ) ≤ m := by exact_mod_cast hmpos
            linarith
          rw [eq_div_iff hpos.ne']
          calc M * (states n (m-1)).card * ((m:ℝ) + n - 1) = M * (((m:ℝ) + n - 1) * (states n (m-1)).card) := by ring
            _ = M * ((m : ℝ) * (states n m).card) := by rw [hdouble]
            _ = (m : ℝ) * (M * (states n m).card) := by ring
            _ = m := by rw [hcardM, mul_one]
        rw [hRHS]
        simp only [hA]
        rw [← Finset.mul_sum, hBsum]
        exact mul_le_mul_of_nonneg_left hUpper hcoef
