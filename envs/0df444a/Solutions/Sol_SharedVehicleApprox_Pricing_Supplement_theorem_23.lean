-- Prove2me | solution 1 for SharedVehicleApprox.Pricing.Supplement.theorem_23
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:06:15.205001+00:00
-- url     : https://prove2.me/submissions/3b81ec0a-2843-41ab-9b66-11a33c7ac938

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_DemandRedirection
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_Algorithm4

open Finset QueueingFundamentals.Networks

open SharedVehicleApprox
open SharedVehicleApprox.Pricing
open SharedVehicleApprox.Pricing.Supplement

/-- Theorem 23, p. 27 (corrected: the routing of `(q̃, r̃)` is strongly connected, unless
`q̃ = 0`): the state-independent prices and matching probabilities returned by Algorithm 4 earn at
least `m/(m+n−1)` times the objective of every state-dependent pricing and matching policy under
every stationary law of it. -/
theorem solution {n m : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (I : Fin n → Fin n → ℝ → ℝ)
    (hR : ∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (rewardCurve I i j))
    (E : Finset (Fin n × Fin n))
    (qt zt rt : Fin n → Fin n → ℝ) (hopt : IsAlg4Optimal φ I E qt zt)
    (hrt : rt = matchProb φ qt zt)
    (hconn : SupportConnected (matchDemand φ qt rt) (fun _ _ => 1) ∨ qt = 0)
    (πt : (Fin n → ℕ) → ℝ) (hπt : IsMatchStationary n m φ (toQuote qt) (toMatch rt) πt)
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (r : (Fin n → ℕ) → Fin n → Fin n → Fin n → ℝ)
    (π : (Fin n → ℕ) → ℝ)
    (hqr : IsMatchPolicy n m E q r) (hπ : IsMatchStationary n m φ q r π) :
    (m : ℝ) / ((m : ℝ) + n - 1) * matchObj n m φ I q r π ≤
      matchObj n m φ I (toQuote qt) (toMatch rt) πt := by
        classical
        have hmemN : ∀ (N : ℕ) (x : Fin n → ℕ), x ∈ states n N ↔ ∑ k, x k = N := by
          intro N x
          simp only [states, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
          constructor
          · exact fun h => h.2
          · intro h
            refine ⟨fun k => ?_, h⟩
            have := Finset.single_le_sum (f := x) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
            omega
        have hshift2 : ∀ (a b : Fin n → ℕ) (i j : Fin n),
            (∀ l, a l + (if l = j then 1 else 0) = b l + (if l = i then 1 else 0)) →
            ∑ l, a l = ∑ l, b l := by
          intro a b i j h
          have := Finset.sum_congr rfl (fun l (_ : l ∈ (Finset.univ : Finset (Fin n))) => h l)
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at this
          simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
          omega
        have hmv : ∀ (x : Fin n → ℕ) (i j : Fin n), i ≠ j → 1 ≤ x j → ∀ l,
            moveState x i j l + (if l = j then 1 else 0) = x l + (if l = i then 1 else 0) := by
          intro x i j hij hj l
          simp only [moveState, Function.update_apply]
          by_cases h1 : l = i
          · subst h1; simp [hij]
          · by_cases h2 : l = j
            · subst h2; simp [h1]; omega
            · simp [h1, h2]
        have hmvi : ∀ (x : Fin n → ℕ) (i j : Fin n), i ≠ j → moveState x i j i = x i + 1 := by
          intro x i j hij
          simp [moveState]
        have hmvS : ∀ x ∈ states n m, ∀ i j, i ≠ j → 1 ≤ x j → moveState x i j ∈ states n m := by
          intro x hx i j hij hj
          rw [hmemN] at hx ⊢
          rw [← hx]
          exact hshift2 _ _ i j (hmv x i j hij hj)
        have hmvinv : ∀ (x : Fin n → ℕ) (i j : Fin n), i ≠ j → 1 ≤ x j →
            moveState (moveState x i j) j i = x := by
          intro x i j hij hj
          funext l
          have h1 := hmv x i j hij hj l
          have h2 := hmv (moveState x i j) j i (Ne.symm hij) (by rw [hmvi x i j hij]; omega) l
          by_cases a1 : l = i
          · subst a1; simp only [hij, Ne.symm hij, if_true, if_false] at h1 h2; omega
          · by_cases a2 : l = j
            · subst a2; simp only [a1, if_true, if_false] at h1 h2; omega
            · simp only [a1, a2, if_false] at h1 h2; omega
        have R1 : ∀ i j : Fin n, i ≠ j → ∀ F : (Fin n → ℕ) → (Fin n → ℕ) → ℝ,
            ∑ x ∈ states n m, (if 1 ≤ x j then F x (moveState x i j) else 0) =
              ∑ y ∈ states n m, (if 1 ≤ y i then F (moveState y j i) y else 0) := by
          intro i j hij F
          rw [← Finset.sum_filter, ← Finset.sum_filter]
          apply Finset.sum_nbij' (fun x => moveState x i j) (fun y => moveState y j i)
          · intro x hx
            simp only [Finset.mem_filter] at hx ⊢
            exact ⟨hmvS x hx.1 i j hij hx.2, by rw [hmvi x i j hij]; omega⟩
          · intro y hy
            simp only [Finset.mem_filter] at hy ⊢
            exact ⟨hmvS y hy.1 j i (Ne.symm hij) hy.2, by rw [hmvi y j i (Ne.symm hij)]; omega⟩
          · intro x hx
            simp only [Finset.mem_coe, Finset.mem_filter] at hx
            exact hmvinv x i j hij hx.2
          · intro y hy
            simp only [Finset.mem_coe, Finset.mem_filter] at hy
            exact hmvinv y j i (Ne.symm hij) hy.2
          · intro x hx
            simp only [Finset.mem_coe, Finset.mem_filter] at hx
            rw [hmvinv x i j hij hx.2]
        have hG : ∀ (ρ : (Fin n → ℕ) → Fin n → Fin n → ℝ) (p : (Fin n → ℕ) → ℝ),
            IsStationary n m (fun _ _ => 1) ρ p → (∀ y i j, ¬ 0 < y i → ρ y i j = 0) →
            ∀ a : Fin n, ∑ y ∈ states n m, p y * ∑ i, ρ y i a =
              ∑ y ∈ states n m, p y * ∑ j, ρ y a j := by
          intro ρ p hp hρ0 a
          obtain ⟨-, -, -, hb⟩ := hp
          have h1 : ∑ x ∈ states n m, (x a : ℝ) * (p x * ∑ i, ∑ j, 1 * ρ x i j) =
              ∑ x ∈ states n m, (x a : ℝ) * ∑ i, ∑ j, inflowTerm (fun _ _ => 1) ρ p x i j :=
            Finset.sum_congr rfl (fun x hx => by rw [hb x hx])
          have hL : ∀ x : Fin n → ℕ, (x a : ℝ) * (p x * ∑ i, ∑ j, 1 * ρ x i j) =
              ∑ i, ∑ j, (if i = j then (x a : ℝ) * p x * ρ x i j else 0) +
                ∑ i, ∑ j, (if i = j then 0 else (x a : ℝ) * p x * ρ x i j) := by
            intro x
            simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
            split_ifs <;> ring
          have hRt : ∀ x : Fin n → ℕ, (x a : ℝ) * ∑ i, ∑ j, inflowTerm (fun _ _ => 1) ρ p x i j =
              ∑ i, ∑ j, (if i = j then (x a : ℝ) * p x * ρ x i j else 0) +
                ∑ i, ∑ j, (if i = j then 0 else if 1 ≤ x j then
                  (x a : ℝ) * (p (moveState x i j) * ρ (moveState x i j) i j) else 0) := by
            intro x
            simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
            unfold inflowTerm
            by_cases hij : i = j
            · subst hij; simp; ring
            · by_cases hj : 1 ≤ x j <;> simp [hij, hj]
          simp only [hL, hRt, Finset.sum_add_distrib, add_right_inj] at h1
          have hsw : ∀ f : (Fin n → ℕ) → Fin n → Fin n → ℝ,
              ∑ x ∈ states n m, ∑ i, ∑ j, f x i j = ∑ i, ∑ j, ∑ x ∈ states n m, f x i j := by
            intro f
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.sum_comm]
          rw [hsw, hsw] at h1
          have hterm : ∀ i j, (∑ x ∈ states n m, (if i = j then 0 else if 1 ≤ x j then
                  (x a : ℝ) * (p (moveState x i j) * ρ (moveState x i j) i j) else 0)) -
                ∑ x ∈ states n m, (if i = j then 0 else (x a : ℝ) * p x * ρ x i j) =
                ∑ y ∈ states n m, p y * (ρ y i j *
                  ((if a = j then 1 else 0) - (if a = i then 1 else 0))) := by
            intro i j
            by_cases hij : i = j
            · subst hij; simp
            · simp only [hij, if_false]
              rw [R1 i j hij (fun x y => (x a : ℝ) * (p y * ρ y i j)), ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl (fun y _ => ?_)
              by_cases hy : 1 ≤ y i
              · simp only [hy, if_true]
                have := hmv y j i (Ne.symm hij) hy a
                have hc : ((moveState y j i a : ℕ) : ℝ) + (if a = i then 1 else 0) =
                    (y a : ℝ) + (if a = j then 1 else 0) := by
                  have := congrArg (fun t : ℕ => (t : ℝ)) this
                  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at this
                  exact this
                have : ((moveState y j i a : ℕ) : ℝ) = (y a : ℝ) + (if a = j then 1 else 0) -
                  (if a = i then 1 else 0) := by linarith
                rw [this]; ring
              · simp only [hy, if_false]
                rw [hρ0 y i j (by omega)]; ring
          have h2 : ∑ i, ∑ j, ∑ y ∈ states n m, p y * (ρ y i j *
                  ((if a = j then 1 else 0) - (if a = i then 1 else 0))) = 0 := by
            simp only [← hterm, Finset.sum_sub_distrib, h1, sub_self]
          rw [← hsw] at h2
          have h3 : ∀ y, ∑ i, ∑ j, p y * (ρ y i j *
                  ((if a = j then 1 else 0) - (if a = i then 1 else 0))) =
                p y * ∑ i, ρ y i a - p y * ∑ j, ρ y a j := by
            intro y
            simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
              Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
            congr 1
            · simp
            · rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
              simp
          simp only [h3, Finset.sum_sub_distrib] at h2
          linarith
        have hA : matchObj n m φ I q r π ≤ elevObj φ I qt := by
          have hflow := hG (matchRate φ q r) π hπ (fun y i j h => by simp [matchRate, h])
          obtain ⟨hπ0, -, hπ1, -⟩ := hπ
          set B : (Fin n → ℕ) → Fin n → Fin n → Fin n → ℝ :=
            fun x i j k => if 0 < x k then r x i j k else 0 with hB
          set C : (Fin n → ℕ) → Fin n → Fin n → ℝ :=
            fun x i j => if 0 < x i then 1 - ∑ l, r x i j l else 0 with hC
          have hserve : ∀ x i j, serveProb r x i j = ∑ k, B x i j k + C x i j := by
            intro x i j
            unfold serveProb assignProb
            have : ∀ k, (if 0 < x k then r x i j k + (if k = i then 1 - ∑ l, r x i j l else 0) else 0) =
                B x i j k + (if k = i then C x i j else 0) := by
              intro k
              by_cases hki : k = i
              · subst hki; by_cases hk : 0 < x k <;> simp [hB, hC, hk]
              · by_cases hk : 0 < x k <;> simp [hB, hk, hki]
            rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_add_distrib, Finset.sum_ite_eq']
            simp
          have hρ : ∀ x k j, matchRate φ q r x k j =
              ∑ i, φ i j * q x i j * (B x i j k + if k = i then C x i j else 0) := by
            intro x k j
            unfold matchRate
            by_cases hk : 0 < x k
            · rw [if_pos hk]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              unfold assignProb
              by_cases hki : k = i
              · subst hki; simp [hB, hC, hk]
              · simp [hB, hk, hki]
            · rw [if_neg hk]
              symm
              refine Finset.sum_eq_zero (fun i _ => ?_)
              by_cases hki : k = i
              · subst hki; simp [hB, hC, hk]
              · simp [hB, hk, hki]
          have hin : ∀ x a, ∑ k, matchRate φ q r x k a =
              ∑ i, φ i a * q x i a * serveProb r x i a := by
            intro x a
            simp only [hρ, hserve]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq']
            simp
          have hout : ∀ x a, ∑ j, matchRate φ q r x a j =
              ∑ i, ∑ j, φ i j * q x i j * B x i j a + ∑ j, φ a j * q x a j * C x a j := by
            intro x a
            simp only [hρ, mul_add, Finset.sum_add_distrib]
            congr 1
            · rw [Finset.sum_comm]
            · refine Finset.sum_congr rfl (fun j _ => ?_)
              simp [mul_ite]
          have hB0 : ∀ x ∈ states n m, ∀ i j k, 0 ≤ B x i j k := by
            intro x hx i j k
            simp only [hB]; split_ifs
            · exact (hqr x hx i j).2.1 k
            · exact le_refl _
          have hC0 : ∀ x ∈ states n m, ∀ i j, 0 ≤ C x i j := by
            intro x hx i j
            simp only [hC]; split_ifs
            · linarith [(hqr x hx i j).2.2.2]
            · exact le_refl _
          have hs01 : ∀ x ∈ states n m, ∀ i j, 0 ≤ serveProb r x i j ∧ serveProb r x i j ≤ 1 := by
            intro x hx i j
            rw [hserve]
            have h1 : 0 ≤ ∑ k, B x i j k := Finset.sum_nonneg (fun k _ => hB0 x hx i j k)
            have h2 : ∑ k, B x i j k ≤ ∑ k, r x i j k := Finset.sum_le_sum (fun k _ => by
              simp only [hB]; split_ifs
              · exact le_refl _
              · exact (hqr x hx i j).2.1 k)
            have h3 := (hqr x hx i j).2.2.2
            refine ⟨by linarith [hC0 x hx i j], ?_⟩
            simp only [hC]; split_ifs <;> linarith
          set q' : Fin n → Fin n → ℝ := fun i j => ∑ x ∈ states n m, π x * (q x i j * serveProb r x i j)
            with hq'
          set z' : Fin n → Fin n → ℝ := fun i k => ∑ x ∈ states n m, π x * ∑ j, φ i j * q x i j * B x i j k
            with hz'
          have hsw1 : ∀ f : (Fin n → ℕ) → Fin n → ℝ,
              ∑ k, ∑ x ∈ states n m, π x * f x k = ∑ x ∈ states n m, π x * ∑ k, f x k := by
            intro f; rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
          have hφq' : ∀ i j, φ i j * q' i j =
              ∑ x ∈ states n m, π x * (φ i j * q x i j * serveProb r x i j) := by
            intro i j; simp only [hq', Finset.mul_sum]
            exact Finset.sum_congr rfl (fun x _ => by ring)
          have e_in : ∀ a, ∑ k, φ k a * q' k a =
              ∑ x ∈ states n m, π x * ∑ k, matchRate φ q r x k a := by
            intro a; simp only [hφq', hin]; exact hsw1 _
          have e_out_q : ∀ a, ∑ j, φ a j * q' a j = ∑ x ∈ states n m, π x *
              (∑ j, φ a j * q x a j * ∑ k, B x a j k + ∑ j, φ a j * q x a j * C x a j) := by
            intro a; simp only [hφq']; rw [hsw1]
            refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [← Finset.sum_add_distrib]
            refine congrArg _ (Finset.sum_congr rfl (fun j _ => ?_))
            rw [hserve]; ring
          have e_zrow : ∀ a, ∑ k, z' a k =
              ∑ x ∈ states n m, π x * ∑ j, φ a j * q x a j * ∑ k, B x a j k := by
            intro a; simp only [hz']; rw [hsw1]
            refine Finset.sum_congr rfl (fun x _ => ?_)
            simp only [Finset.mul_sum]; rw [Finset.sum_comm]
          have e_zcol : ∀ a, ∑ j, z' j a =
              ∑ x ∈ states n m, π x * ∑ i, ∑ j, φ i j * q x i j * B x i j a := by
            intro a; simp only [hz']; rw [hsw1]
          have hfeas : IsAlg4Feasible φ E q' z' := by
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · intro i j
              constructor
              · exact Finset.sum_nonneg (fun x hx => mul_nonneg (hπ0 x)
                  (mul_nonneg (hqr x hx i j).1.1 (hs01 x hx i j).1))
              · calc q' i j ≤ ∑ x ∈ states n m, π x * 1 :=
                      Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left
                        (mul_le_one₀ (hqr x hx i j).1.2 (hs01 x hx i j).1 (hs01 x hx i j).2) (hπ0 x))
                  _ = 1 := by simp [hπ1]
            · intro i k
              exact Finset.sum_nonneg (fun x hx => mul_nonneg (hπ0 x) (Finset.sum_nonneg (fun j _ =>
                mul_nonneg (mul_nonneg (hφ i j) (hqr x hx i j).1.1) (hB0 x hx i j k))))
            · intro i k hik
              apply Finset.sum_eq_zero
              intro x hx
              rw [Finset.sum_eq_zero (fun j _ => by simp [hB, (hqr x hx i j).2.2.1 k hik])]
              simp
            · intro a
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib, e_in, e_zrow, e_out_q, e_zcol, hflow]
              simp only [hout, mul_add, Finset.sum_add_distrib]
              ring
            · intro a
              rw [e_zcol, e_in, hflow]
              apply Finset.sum_le_sum
              intro x hx
              rw [hout]
              apply mul_le_mul_of_nonneg_left _ (hπ0 x)
              have : 0 ≤ ∑ j, φ a j * q x a j * C x a j := Finset.sum_nonneg (fun j _ =>
                mul_nonneg (mul_nonneg (hφ a j) (hqr x hx a j).1.1) (hC0 x hx a j))
              linarith
          have hJ : ∀ i j, ∑ x ∈ states n m, π x * (rewardCurve I i j (q x i j) * serveProb r x i j) ≤
              rewardCurve I i j (q' i j) := by
            intro i j
            have hR0 : rewardCurve I i j 0 = 0 := by simp [rewardCurve]
            have key : ∀ x ∈ states n m, rewardCurve I i j (q x i j) * serveProb r x i j ≤
                rewardCurve I i j (q x i j * serveProb r x i j) := by
              intro x hx
              obtain ⟨hs0, hs1⟩ := hs01 x hx i j
              have hb1 : (0:ℝ) ≤ 1 - serveProb r x i j := by linarith
              have := (hR i j).2 (show q x i j ∈ Set.Icc (0:ℝ) 1 from
                ⟨(hqr x hx i j).1.1, (hqr x hx i j).1.2⟩) (show (0:ℝ) ∈ Set.Icc (0:ℝ) 1 from
                ⟨le_refl _, zero_le_one⟩) hs0 hb1 (by ring)
              simp only [smul_eq_mul, hR0, mul_zero, add_zero] at this
              rw [mul_comm (q x i j), mul_comm (rewardCurve I i j (q x i j))]
              exact this
            calc ∑ x ∈ states n m, π x * (rewardCurve I i j (q x i j) * serveProb r x i j)
                ≤ ∑ x ∈ states n m, π x • rewardCurve I i j (q x i j * serveProb r x i j) :=
                  Finset.sum_le_sum (fun x hx => by
                    rw [smul_eq_mul]; exact mul_le_mul_of_nonneg_left (key x hx) (hπ0 x))
              _ ≤ rewardCurve I i j (∑ x ∈ states n m, π x • (q x i j * serveProb r x i j)) :=
                  (hR i j).le_map_sum (fun x _ => hπ0 x) hπ1 (fun x hx =>
                    ⟨mul_nonneg (hqr x hx i j).1.1 (hs01 x hx i j).1,
                      mul_le_one₀ (hqr x hx i j).1.2 (hs01 x hx i j).1 (hs01 x hx i j).2⟩)
              _ = rewardCurve I i j (q' i j) := by simp only [smul_eq_mul, hq']
          calc matchObj n m φ I q r π = ∑ i, ∑ j, φ i j * ∑ x ∈ states n m,
                π x * (rewardCurve I i j (q x i j) * serveProb r x i j) := by
                unfold matchObj
                simp only [Finset.mul_sum]
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl (fun i _ => ?_)
                rw [Finset.sum_comm]
                exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun x _ => by ring))
            _ ≤ ∑ i, ∑ j, φ i j * rewardCurve I i j (q' i j) :=
                Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
                  mul_le_mul_of_nonneg_left (hJ i j) (hφ i j)))
            _ = elevObj φ I q' := rfl
            _ ≤ elevObj φ I qt := hopt.2 q' z' hfeas
        have hshift1 : ∀ (a b : Fin n → ℕ) (k : Fin n),
            (∀ l, a l + (if l = k then 1 else 0) = b l) → ∑ l, a l + 1 = ∑ l, b l := by
          intro a b k h
          have := Finset.sum_congr rfl (fun l (_ : l ∈ (Finset.univ : Finset (Fin n))) => h l)
          rw [Finset.sum_add_distrib] at this
          simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
          omega
        have hBpart : 0 < m → 0 < n → SupportConnected (matchDemand φ qt rt) (fun _ _ => 1) →
            matchObj n m φ I (toQuote qt) (toMatch rt) πt =
              (m : ℝ) / ((m : ℝ) + n - 1) * elevObj φ I qt := by
          intro hm hn hc
          obtain ⟨⟨hq01, hz0, -, hbal, hcol⟩, -⟩ := hopt
          have hD0 : ∀ i, 0 ≤ ∑ k, φ i k * qt i k :=
            fun i => Finset.sum_nonneg (fun k _ => mul_nonneg (hφ i k) (hq01 i k).1)
          have hzrow : ∀ i, ∑ l, zt i l ≤ ∑ k, φ i k * qt i k := by
            intro i
            have h1 := hbal i
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h1
            have h2 := hcol i
            linarith
          have hDr : ∀ i k, (∑ l, φ i l * qt i l) * rt i k = zt i k := by
            intro i k
            rw [hrt]; unfold matchProb
            by_cases h : ∑ l, φ i l * qt i l = 0
            · have : zt i k = 0 := by
                have := Finset.single_le_sum (f := zt i) (fun l _ => hz0 i l) (Finset.mem_univ k)
                have := hzrow i; have := hz0 i k; linarith
              rw [this, h]; simp
            · field_simp
          have hrt0 : ∀ i k, 0 ≤ rt i k := by
            intro i k; rw [hrt]; exact div_nonneg (hz0 i k) (hD0 i)
          have hrt1 : ∀ i, ∑ l, rt i l ≤ 1 := by
            intro i
            by_cases h : ∑ l, φ i l * qt i l = 0
            · have : ∀ l, rt i l = 0 := by
                intro l; rw [hrt]; unfold matchProb; rw [h, div_zero]
              simp [this]
            · have hpos : 0 < ∑ l, φ i l * qt i l := lt_of_le_of_ne (hD0 i) (Ne.symm h)
              have : ∑ l, rt i l = (∑ l, zt i l) / ∑ l, φ i l * qt i l := by
                rw [Finset.sum_div, hrt]; rfl
              rw [this, div_le_one hpos]; exact hzrow i
          set φb := matchDemand φ qt rt with hφb
          have hφb0 : ∀ k j, 0 ≤ φb k j := by
            intro k j
            simp only [hφb, matchDemand]
            have := hrt1 k
            exact add_nonneg (mul_nonneg (mul_nonneg (hφ k j) (hq01 k j).1) (by linarith))
              (Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (hφ i j) (hq01 i j).1) (hrt0 i k)))
          have hrow : ∀ k, ∑ j, φb k j = ∑ j, φb j k := by
            intro k
            have e1 : ∑ j, φb k j = (∑ j, φ k j * qt k j) - ∑ l, zt k l + ∑ i, zt i k := by
              simp only [hφb, matchDemand, Finset.sum_add_distrib, ← Finset.sum_mul]
              rw [Finset.sum_comm (f := fun j i => φ i j * qt i j * rt i k)]
              have h1 : ∑ i, ∑ j, φ i j * qt i j * rt i k = ∑ i, zt i k := by
                refine Finset.sum_congr rfl (fun i _ => ?_); rw [← Finset.sum_mul]; exact hDr i k
              have h2 : (∑ j, φ k j * qt k j) * ∑ l, rt k l = ∑ l, zt k l := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun l _ => hDr k l)
              rw [h1, mul_sub, mul_one, h2]
            have e2 : ∑ j, φb j k = ∑ j, φ j k * qt j k := by
              simp only [hφb, matchDemand, Finset.sum_add_distrib, mul_sub, mul_one,
                Finset.sum_sub_distrib]
              rw [Finset.sum_comm (f := fun j i => φ i k * qt i k * rt i j)]
              have : ∑ i, ∑ j, φ i k * qt i k * rt i j = ∑ i, φ i k * qt i k * ∑ l, rt i l := by
                refine Finset.sum_congr rfl (fun i _ => ?_); rw [Finset.mul_sum]
              rw [this]; ring
            have h3 := hbal k
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h3
            rw [e1, e2]; linarith
          have hρt : ∀ x k j, matchRate φ (toQuote qt) (toMatch rt) x k j =
              if 0 < x k then φb k j else 0 := by
            intro x k j
            unfold matchRate toQuote toMatch assignProb
            simp only [hφb, matchDemand]
            split_ifs
            · simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
                Finset.mem_univ, if_true]
              ring
            · rfl
          obtain ⟨hπt0, hπtS, hπt1, hπtb⟩ := hπt
          have hne : (states n m).Nonempty := by
            by_contra h
            rw [Finset.not_nonempty_iff_eq_empty] at h
            rw [h] at hπt1; simp at hπt1
          obtain ⟨x0, hx0S, hx0max⟩ := Finset.exists_max_image (states n m) πt hne
          have hsplit : ∀ f : Fin n → Fin n → ℝ,
              ∑ i, ∑ j, (if i = j then 0 else f i j) = ∑ i, ∑ j, f i j - ∑ i, f i i := by
            intro f
            have : ∀ i j, (if i = j then 0 else f i j) = f i j - if i = j then f i j else 0 := by
              intro i j; split_ifs <;> simp
            simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
          have hds : ∀ x : Fin n → ℕ, ∑ i, ∑ j, (if i = j then 0 else if 0 < x i then φb i j else 0) =
              ∑ i, ∑ j, (if i = j then 0 else if 1 ≤ x j then φb i j else 0) := by
            intro x
            rw [hsplit (fun i j => if 0 < x i then φb i j else 0),
              hsplit (fun i j => if 1 ≤ x j then φb i j else 0)]
            congr 1
            · rw [Finset.sum_comm (f := fun i j => if 1 ≤ x j then φb i j else 0)]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              by_cases hi : 0 < x i
              · have hi' : 1 ≤ x i := hi
                simp only [hi, hi', if_true]; exact hrow i
              · have hi' : ¬ 1 ≤ x i := hi
                simp only [hi, hi', if_false, Finset.sum_const_zero]
          have hP : ∀ x ∈ states n m, πt x = πt x0 → ∀ i j, i ≠ j → 1 ≤ x j → 0 < φb i j →
              πt (moveState x i j) = πt x0 := by
            intro x hx hxM i0 j0 hij0 hj0 hφpos
            have hb := hπtb x hx
            have hL : ∑ i, ∑ j, (fun _ _ => (1:ℝ)) i j * matchRate φ (toQuote qt) (toMatch rt) x i j =
                ∑ i, ∑ j, (if i = j then (if 0 < x i then φb i j else 0) else 0) +
                  ∑ i, ∑ j, (if i = j then 0 else if 1 ≤ x j then φb i j else 0) := by
              rw [← hds, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [hρt]; split_ifs <;> simp
            have hRt : ∑ i, ∑ j, inflowTerm (fun _ _ => 1) (matchRate φ (toQuote qt) (toMatch rt)) πt x i j =
                πt x * ∑ i, ∑ j, (if i = j then (if 0 < x i then φb i j else 0) else 0) +
                  ∑ i, ∑ j, (if i = j then 0 else if 1 ≤ x j then πt (moveState x i j) * φb i j else 0) := by
              simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
              unfold inflowTerm
              by_cases hij : i = j
              · subst hij; simp [hρt]
              · by_cases hj : 1 ≤ x j
                · simp [hij, hj, hρt, hmvi x i j hij]
                · simp [hij, hj]
            rw [hL, hRt, mul_add, add_right_inj, hxM] at hb
            have hfg : ∀ i j, (if i = j then 0 else if 1 ≤ x j then πt (moveState x i j) * φb i j else 0) ≤
                (if i = j then 0 else if 1 ≤ x j then πt x0 * φb i j else 0) := by
              intro i j
              split_ifs
              · exact le_refl _
              · exact mul_le_mul_of_nonneg_right
                  (by by_cases hy : moveState x i j ∈ states n m
                      · exact hx0max _ hy
                      · rw [hπtS _ hy]; exact hπt0 x0) (hφb0 i j)
              · exact le_refl _
            have hsum : ∑ i, ∑ j, (if i = j then 0 else if 1 ≤ x j then πt (moveState x i j) * φb i j else 0) =
                ∑ i, ∑ j, (if i = j then 0 else if 1 ≤ x j then πt x0 * φb i j else 0) := by
              rw [← hb, Finset.mul_sum]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun j _ => ?_)
              split_ifs <;> simp
            have hout := (Finset.sum_eq_sum_iff_of_le (fun i _ => Finset.sum_le_sum (fun j _ => hfg i j))).1
              hsum i0 (Finset.mem_univ _)
            have hin := (Finset.sum_eq_sum_iff_of_le (fun j _ => hfg i0 j)).1 hout j0 (Finset.mem_univ _)
            simp only [hij0, hj0, if_false, if_true] at hin
            exact mul_right_cancel₀ hφpos.ne' hin
          have hreach : ∀ i j, Relation.ReflTransGen
              (fun a b => a ≠ b ∧ 0 < matchDemand φ qt rt a b * (fun _ _ => (1:ℝ)) a b) i j →
              ∀ x ∈ states n m, πt x = πt x0 → 1 ≤ x j → ∃ y ∈ states n m, πt y = πt x0 ∧
                ∀ l, y l + (if l = j then 1 else 0) = x l + (if l = i then 1 else 0) := by
            intro i j h
            induction h using Relation.ReflTransGen.head_induction_on with
            | refl => intro x hx hxM _; exact ⟨x, hx, hxM, fun l => rfl⟩
            | @head a c hab _ ih =>
              intro x hx hxM hxj
              obtain ⟨y, hy, hyM, hyeq⟩ := ih x hx hxM hxj
              have hyc : 1 ≤ y c := by
                have := hyeq c
                by_cases hcj : c = j
                · subst hcj; simp only [if_true] at this; omega
                · simp only [hcj, if_false, if_true] at this; omega
              have hac : a ≠ c := hab.1
              have hpos : 0 < φb a c := by simpa using hab.2
              refine ⟨moveState y a c, hmvS y hy a c hac hyc, hP y hy hyM a c hac hyc hpos, fun l => ?_⟩
              have h1 := hyeq l
              have h2 := hmv y a c hac hyc l
              split_ifs at h1 h2 ⊢ <;> omega
          have key : ∀ d : ℕ, ∀ x ∈ states n m, πt x = πt x0 → ∀ y ∈ states n m,
              ∑ k, (x k - y k) = d → πt y = πt x0 := by
            intro d
            induction d using Nat.strong_induction_on with
            | _ d ih =>
            intro x hx hxM y hy hd
            have hxs := (hmemN m x).1 hx
            have hys := (hmemN m y).1 hy
            by_cases hd0 : d = 0
            · subst hd0
              have hle : ∀ k ∈ (Finset.univ : Finset (Fin n)), x k ≤ y k := fun k _ => by
                have := (Finset.sum_eq_zero_iff.1 hd) k (Finset.mem_univ k); omega
              have heq := (Finset.sum_eq_sum_iff_of_le hle).1 (by rw [hxs, hys])
              have : x = y := funext fun k => heq k (Finset.mem_univ k)
              rw [← this]; exact hxM
            · obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero
                (show ∑ k, (x k - y k) ≠ 0 by rw [hd]; exact hd0)
              have hj' : y j < x j := by omega
              have : ∃ i, x i < y i := by
                by_contra hcon
                push_neg at hcon
                have : ∑ k, y k < ∑ k, x k :=
                  Finset.sum_lt_sum (fun k _ => hcon k) ⟨j, Finset.mem_univ j, hj'⟩
                omega
              obtain ⟨i, hi⟩ := this
              have hij : i ≠ j := by intro h; subst h; omega
              obtain ⟨x', hx', hx'M, hx'eq⟩ := hreach i j (hc i j) x hx hxM (by omega)
              have hlt : ∑ k, (x' k - y k) < d := by
                rw [← hd]
                apply Finset.sum_lt_sum
                · intro k _
                  have := hx'eq k
                  by_cases hki : k = i
                  · subst hki; rw [if_neg hij, if_pos rfl] at this; omega
                  · by_cases hkj : k = j
                    · subst hkj; rw [if_pos rfl, if_neg hki] at this; omega
                    · rw [if_neg hkj, if_neg hki] at this; omega
                · refine ⟨j, Finset.mem_univ j, ?_⟩
                  have := hx'eq j
                  rw [if_pos rfl, if_neg (Ne.symm hij)] at this
                  omega
              exact ih _ hlt x' hx' hx'M y hy rfl
          have hall : ∀ y ∈ states n m, πt y = πt x0 := fun y hy => key _ x0 hx0S rfl y hy rfl
          -- counting
          have hupd1 : ∀ (x : Fin n → ℕ) (k : Fin n), 1 ≤ x k → ∀ l,
              Function.update x k (x k - 1) l + (if l = k then 1 else 0) = x l := by
            intro x k hk l
            by_cases hl : l = k
            · subst hl; simp; omega
            · simp [hl]
          have hupd2 : ∀ (y : Fin n → ℕ) (k : Fin n) l,
              y l + (if l = k then 1 else 0) = Function.update y k (y k + 1) l := by
            intro y k l
            by_cases hl : l = k
            · subst hl; simp
            · simp [hl]
          have hmapS : ∀ k, ∀ x ∈ (states n m).filter (fun x => 0 < x k),
              Function.update x k (x k - 1) ∈ states n (m - 1) := by
            intro k x hx
            rw [Finset.mem_filter] at hx
            rw [hmemN]
            have := hshift1 _ _ k (hupd1 x k hx.2)
            rw [(hmemN m x).1 hx.1] at this
            omega
          have hmapS' : ∀ k, ∀ y ∈ states n (m - 1),
              Function.update y k (y k + 1) ∈ (states n m).filter (fun x => 0 < x k) := by
            intro k y hy
            rw [Finset.mem_filter, hmemN]
            refine ⟨?_, by simp⟩
            have := hshift1 _ _ k (hupd2 y k)
            rw [(hmemN (m - 1) y).1 hy] at this
            omega
          have hinv1 : ∀ k, ∀ x ∈ (states n m).filter (fun x => 0 < x k),
              Function.update (Function.update x k (x k - 1)) k
                (Function.update x k (x k - 1) k + 1) = x := by
            intro k x hx
            rw [Finset.mem_filter] at hx
            funext l
            by_cases hl : l = k
            · subst hl; simp; omega
            · simp [hl]
          have hinv2 : ∀ k, ∀ y ∈ states n (m - 1),
              Function.update (Function.update y k (y k + 1)) k
                (Function.update y k (y k + 1) k - 1) = y := by
            intro k y _
            funext l
            by_cases hl : l = k
            · subst hl; simp
            · simp [hl]
          have hbij : ∀ k, ((states n m).filter (fun x => 0 < x k)).card = (states n (m - 1)).card := by
            intro k
            exact Finset.card_nbij' (fun x => Function.update x k (x k - 1))
              (fun y => Function.update y k (y k + 1)) (hmapS k) (hmapS' k) (hinv1 k) (hinv2 k)
          have hsumk : ∀ k, ∑ x ∈ states n m, x k = ∑ y ∈ states n (m - 1), (y k + 1) := by
            intro k
            rw [← Finset.sum_filter_of_ne (s := states n m) (f := fun x : Fin n → ℕ => x k)
              (p := fun x => 0 < x k) (fun x _ h => Nat.pos_of_ne_zero h)]
            apply Finset.sum_nbij' (fun x => Function.update x k (x k - 1))
              (fun y => Function.update y k (y k + 1)) (hmapS k) (hmapS' k) (hinv1 k) (hinv2 k)
            intro x hx
            rw [Finset.mem_filter] at hx
            simp; omega
          have hcnt : m * (states n m).card = (states n (m - 1)).card * (m - 1 + n) := by
            have h1 : ∑ x ∈ states n m, ∑ k, x k = m * (states n m).card := by
              rw [Finset.sum_congr rfl (fun x hx => (hmemN m x).1 hx)]; simp [mul_comm]
            have h2 : ∑ y ∈ states n (m - 1), ∑ k, (y k + 1) = (states n (m - 1)).card * (m - 1 + n) := by
              rw [Finset.sum_congr rfl (fun y hy => by rw [Finset.sum_add_distrib, (hmemN (m - 1) y).1 hy])]
              simp
            have h3 : ∑ x ∈ states n m, ∑ k, x k = ∑ y ∈ states n (m - 1), ∑ k, (y k + 1) := by
              rw [Finset.sum_comm, Finset.sum_comm (s := states n (m - 1))]
              exact Finset.sum_congr rfl (fun k _ => hsumk k)
            rw [← h1, ← h2, h3]
          have hpos : (0:ℝ) < m + n - 1 := by
            have : (1:ℝ) ≤ m := by exact_mod_cast hm
            have : (1:ℝ) ≤ n := by exact_mod_cast hn
            linarith
          have hMS : πt x0 * (states n m).card = 1 := by
            rw [← hπt1, Finset.sum_congr rfl (fun y hy => hall y hy)]; simp [mul_comm]
          have hMN : ∀ k, πt x0 * ((states n m).filter (fun x => 0 < x k)).card =
              (m : ℝ) / ((m : ℝ) + n - 1) := by
            intro k
            rw [eq_div_iff hpos.ne', hbij k]
            have hc' : ((m : ℝ)) * (states n m).card = (states n (m - 1)).card * ((m : ℝ) + n - 1) := by
              have := congrArg (fun t : ℕ => (t : ℝ)) hcnt
              simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hm, Nat.cast_one] at this
              rw [this]; ring
            calc πt x0 * (states n (m - 1)).card * ((m : ℝ) + n - 1)
                = πt x0 * ((m : ℝ) * (states n m).card) := by rw [hc']; ring
              _ = m * (πt x0 * (states n m).card) := by ring
              _ = m := by rw [hMS, mul_one]
          have hsv : ∀ i j, ∑ x ∈ states n m, πt x * serveProb (toMatch rt) x i j =
              (m : ℝ) / ((m : ℝ) + n - 1) := by
            intro i j
            have ha1 : ∑ k, (rt i k + if k = i then 1 - ∑ l, rt i l else 0) = 1 := by
              rw [Finset.sum_add_distrib, Finset.sum_ite_eq']; simp
            calc ∑ x ∈ states n m, πt x * serveProb (toMatch rt) x i j
                = ∑ x ∈ states n m, ∑ k, (if 0 < x k then
                    πt x0 * (rt i k + if k = i then 1 - ∑ l, rt i l else 0) else 0) := by
                  refine Finset.sum_congr rfl (fun x hx => ?_)
                  rw [hall x hx]
                  unfold serveProb assignProb toMatch
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl (fun k _ => ?_)
                  split_ifs <;> simp
              _ = ∑ k, ∑ x ∈ states n m, (if 0 < x k then
                    πt x0 * (rt i k + if k = i then 1 - ∑ l, rt i l else 0) else 0) := Finset.sum_comm
              _ = ∑ k, (rt i k + if k = i then 1 - ∑ l, rt i l else 0) *
                    (πt x0 * ((states n m).filter (fun x => 0 < x k)).card) := by
                  refine Finset.sum_congr rfl (fun k _ => ?_)
                  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; ring
              _ = ∑ k, (rt i k + if k = i then 1 - ∑ l, rt i l else 0) *
                    ((m : ℝ) / ((m : ℝ) + n - 1)) := by simp only [hMN]
              _ = (m : ℝ) / ((m : ℝ) + n - 1) := by rw [← Finset.sum_mul, ha1, one_mul]
          calc matchObj n m φ I (toQuote qt) (toMatch rt) πt
              = ∑ i, ∑ j, φ i j * rewardCurve I i j (qt i j) *
                  ∑ x ∈ states n m, πt x * serveProb (toMatch rt) x i j := by
                unfold matchObj toQuote
                simp only [Finset.mul_sum]
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl (fun i _ => ?_)
                rw [Finset.sum_comm]
                exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun x _ => by ring))
            _ = (m : ℝ) / ((m : ℝ) + n - 1) * elevObj φ I qt := by
                simp only [hsv]
                unfold elevObj
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl (fun i _ => ?_)
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl (fun j _ => by ring)
        have hc0 : 0 ≤ (m : ℝ) / ((m : ℝ) + n - 1) := by
          rcases Nat.eq_zero_or_pos m with h | h
          · simp [h]
          · apply div_nonneg (Nat.cast_nonneg _)
            have : (1:ℝ) ≤ m := by exact_mod_cast h
            have : (0:ℝ) ≤ n := Nat.cast_nonneg _
            linarith
        rcases hconn with hconn | hq0
        · rcases Nat.eq_zero_or_pos m with hm | hm
          · subst hm
            simp only [Nat.cast_zero, zero_div, zero_mul]
            apply le_of_eq
            symm
            unfold matchObj
            apply Finset.sum_eq_zero
            intro x hx
            have hx0 : ∀ k, x k = 0 := by
              rw [hmemN] at hx
              intro k
              have := Finset.single_le_sum (f := x) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
              omega
            simp [serveProb, hx0]
          · rcases Nat.eq_zero_or_pos n with hn | hn
            · subst hn; simp [matchObj]
            · rw [hBpart hm hn hconn]
              exact mul_le_mul_of_nonneg_left hA hc0
        · have h0 : matchObj n m φ I (toQuote qt) (toMatch rt) πt = 0 := by
            unfold matchObj; simp [toQuote, hq0, rewardCurve]
          have h1 : elevObj φ I qt = 0 := by
            unfold elevObj; simp [hq0, rewardCurve]
          rw [h0]
          calc (m : ℝ) / ((m : ℝ) + n - 1) * matchObj n m φ I q r π
              ≤ (m : ℝ) / ((m : ℝ) + n - 1) * elevObj φ I qt := mul_le_mul_of_nonneg_left hA hc0
            _ = 0 := by rw [h1, mul_zero]
