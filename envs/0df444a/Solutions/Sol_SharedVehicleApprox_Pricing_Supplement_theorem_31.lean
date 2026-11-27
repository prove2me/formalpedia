-- Prove2me | solution 1 for SharedVehicleApprox.Pricing.Supplement.theorem_31
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:07:50.23537+00:00
-- url     : https://prove2.me/submissions/ad82120d-2cc3-42f0-8837-5cef9cd6090d

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_SupplyRedirection
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_Algorithm3
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_NoPricing

open Finset QueueingFundamentals.Networks

open SharedVehicleApprox
open SharedVehicleApprox.Pricing
open SharedVehicleApprox.Pricing.Supplement

/-- Theorem 31, p. 39 (corrected: the routing of `r̃` is strongly connected unless `q̃ = 0`, and
`q̃ ≠ 0` unless the total reward rate at each origin is nonnegative): without prices, the redirection probabilities returned
by Algorithm 8 earn at least `m/(m+n−1)` times the objective of every state-dependent redirection
policy under every stationary law of it. The title says demand redirection; the algorithm and the
proof are supply redirection. -/
theorem solution {n m : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (I c : Fin n → Fin n → ℝ) (qt : Fin n → ℝ) (zt rt : Fin n → Fin n → ℝ)
    (hopt : IsAlg8Optimal φ I c qt zt) (hrt : rt = noPriceRedirectProb φ qt zt)
    (hconn : SupportConnected (inducedDemand φ (fun _ _ => 1) rt) (fun _ _ => 1) ∨ qt = 0)
    (hsign : qt ≠ 0 ∨ ∀ i, 0 ≤ ∑ j, φ i j * I i j)
    (πt : (Fin n → ℕ) → ℝ) (hπt : IsRedirectStationary n m φ serveAll (toRedirect rt) πt)
    (r : (Fin n → ℕ) → Fin n → Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ)
    (hr : IsRedirectPolicy n m serveAll r) (hπ : IsRedirectStationary n m φ serveAll r π) :
    (m : ℝ) / ((m : ℝ) + n - 1) * redirectObj n m φ (constReward I) c serveAll r π ≤
      redirectObj n m φ (constReward I) c serveAll (toRedirect rt) πt := by
        classical
        have hmemS : ∀ M (y : Fin n → ℕ), ∑ l, y l = M → y ∈ states n M := by
          intro M y hy
          simp only [states, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
          refine ⟨fun l => ?_, hy⟩
          have := Finset.single_le_sum (f := y) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
          omega
        have hsumS : ∀ M (y : Fin n → ℕ), y ∈ states n M → ∑ l, y l = M := by
          intro M y hy
          simp only [states, Finset.mem_filter] at hy
          exact hy.2
        have hshift_sum : ∀ (x y : Fin n → ℕ) (a b : Fin n),
            (∀ l, y l + (if l = b then 1 else 0) = x l + (if l = a then 1 else 0)) →
            ∑ l, y l = ∑ l, x l := by
          intro x y a b h
          have := Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => h l)
          simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
          omega
        have hmem : ∀ x ∈ states n m, ∀ (y : Fin n → ℕ) (a b : Fin n),
            (∀ l, y l + (if l = b then 1 else 0) = x l + (if l = a then 1 else 0)) → y ∈ states n m := by
          intro x hx y a b h
          exact hmemS m y ((hshift_sum x y a b h).trans (hsumS m x hx))
        have hms : ∀ (x : Fin n → ℕ) (a b : Fin n), a ≠ b → 1 ≤ x b →
            ∀ l, moveState x a b l + (if l = b then 1 else 0) = x l + (if l = a then 1 else 0) := by
          intro x a b hab hb l
          simp only [moveState, Function.update_apply]
          split_ifs <;> subst_vars <;> first | omega | (exfalso; exact hab rfl)
        have hmsu : ∀ (x y : Fin n → ℕ) (a b : Fin n),
            (∀ l, y l + (if l = b then 1 else 0) = x l + (if l = a then 1 else 0)) → a ≠ b →
            y = moveState x a b := by
          intro x y a b h hab
          funext l
          have := h l
          simp only [moveState, Function.update_apply]
          split_ifs at this ⊢ <;> subst_vars <;> first | omega | (exfalso; exact hab rfl)
        have hA : ∀ k j : Fin n, k ≠ j → ∀ F : (Fin n → ℕ) → (Fin n → ℕ) → ℝ,
            ∑ x ∈ states n m, (if 1 ≤ x j then F (moveState x k j) x else 0) =
            ∑ y ∈ states n m, (if 1 ≤ y k then F y (moveState y j k) else 0) := by
          intro k j hkj F
          rw [← Finset.sum_filter, ← Finset.sum_filter]
          have hinv : ∀ x : Fin n → ℕ, 1 ≤ x j → moveState (moveState x k j) j k = x := by
            intro x hx
            symm
            apply hmsu _ _ _ _ _ (Ne.symm hkj)
            intro l
            have := hms x k j hkj hx l
            omega
          have hinv' : ∀ y : Fin n → ℕ, 1 ≤ y k → moveState (moveState y j k) k j = y := by
            intro y hy
            symm
            apply hmsu _ _ _ _ _ hkj
            intro l
            have := hms y j k (Ne.symm hkj) hy l
            omega
          refine Finset.sum_nbij' (fun x => moveState x k j) (fun y => moveState y j k) ?_ ?_ ?_ ?_ ?_
          · intro x hx
            simp only [Finset.mem_filter] at hx ⊢
            refine ⟨hmem x hx.1 _ k j (hms x k j hkj hx.2), ?_⟩
            have := hms x k j hkj hx.2 k
            simp only [if_true, if_neg hkj] at this
            omega
          · intro y hy
            simp only [Finset.mem_filter] at hy ⊢
            refine ⟨hmem y hy.1 _ j k (hms y j k (Ne.symm hkj) hy.2), ?_⟩
            have := hms y j k (Ne.symm hkj) hy.2 j
            simp only [if_true, if_neg (Ne.symm hkj)] at this
            omega
          · intro x hx
            simp only [Finset.mem_filter] at hx
            exact hinv x hx.2
          · intro y hy
            simp only [Finset.mem_filter] at hy
            exact hinv' y hy.2
          · intro x hx
            simp only [Finset.mem_filter] at hx
            simp only [hinv x hx.2]
        have hupd : ∀ (y : Fin n → ℕ) (i l : Fin n),
            Function.update y i (y i + 1) l = y l + (if l = i then 1 else 0) := by
          intro y i l
          simp only [Function.update_apply]
          split_ifs <;> subst_vars <;> simp
        have hA' : ∀ M : ℕ, ∀ i : Fin n, ∀ F : (Fin n → ℕ) → ℝ,
            ∑ x ∈ states n (M+1), (if 1 ≤ x i then F x else 0) =
            ∑ y ∈ states n M, F (Function.update y i (y i + 1)) := by
          intro M i F
          rw [← Finset.sum_filter]
          have hdown : ∀ (x : Fin n → ℕ) l, 1 ≤ x i →
              Function.update x i (x i - 1) l + (if l = i then 1 else 0) = x l := by
            intro x l hx
            simp only [Function.update_apply]
            split_ifs <;> subst_vars <;> omega
          refine Finset.sum_nbij' (fun x => Function.update x i (x i - 1))
            (fun y => Function.update y i (y i + 1)) ?_ ?_ ?_ ?_ ?_
          · intro x hx
            simp only [Finset.mem_filter] at hx ⊢
            apply hmemS
            have h1 := hsumS _ _ hx.1
            have := Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hdown x l hx.2)
            rw [Finset.sum_add_distrib, Finset.sum_ite_eq'] at this
            simp only [Finset.mem_univ, if_true] at this
            show ∑ l, Function.update x i (x i - 1) l = M
            have h2 : (univ.sum x) = ∑ l, x l := rfl
            omega
          · intro y hy
            simp only [Finset.mem_filter] at hy ⊢
            refine ⟨hmemS _ _ ?_, ?_⟩
            · have h1 := hsumS _ _ hy
              simp only [hupd, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
              omega
            · simp [hupd]
          · intro x hx
            simp only [Finset.mem_filter] at hx
            funext l
            rw [hupd]
            exact hdown x l hx.2
          · intro y hy
            funext l
            simp only [Function.update_apply]
            split_ifs <;> subst_vars <;> simp
          · intro x hx
            simp only [Finset.mem_filter] at hx
            congr 1
            funext l
            rw [hupd]
            exact (hdown x l hx.2).symm
        have hB : ∀ (lam : (Fin n → ℕ) → Fin n → Fin n → ℝ) (p : (Fin n → ℕ) → ℝ),
            IsStationary n m (fun _ _ => 1) lam p →
            (∀ x ∈ states n m, ∀ k j, x k = 0 → lam x k j = 0) →
            ∀ i, ∑ x ∈ states n m, p x * ∑ k, lam x k i =
              ∑ x ∈ states n m, p x * ∑ j, lam x i j := by
          intro lam p hst hz i
          obtain ⟨-, -, -, hbal⟩ := hst
          have key : ∀ k j, ∑ x ∈ states n m, (x i : ℝ) * inflowTerm (fun _ _ => 1) lam p x k j =
              ∑ y ∈ states n m, ((y i : ℝ) + ((if i = j then 1 else 0) - (if i = k then 1 else 0))) *
                (p y * lam y k j) := by
            intro k j
            by_cases hkj : k = j
            · subst hkj
              refine Finset.sum_congr rfl (fun x _ => ?_)
              simp [inflowTerm]
            · have e1 : ∀ x, (x i : ℝ) * inflowTerm (fun _ _ => 1) lam p x k j =
                  if 1 ≤ x j then (fun y x => (x i : ℝ) * (p y * lam y k j)) (moveState x k j) x
                  else 0 := by
                intro x
                simp only [inflowTerm, if_neg hkj]
                split_ifs <;> ring
              rw [Finset.sum_congr rfl (fun x _ => e1 x), hA k j hkj (fun y x => (x i : ℝ) * (p y * lam y k j))]
              refine Finset.sum_congr rfl (fun y hy => ?_)
              by_cases hyk : 1 ≤ y k
              · rw [if_pos hyk]
                have h0 := hms y j k (Ne.symm hkj) hyk i
                have h' : ((moveState y j k i : ℕ) : ℝ) =
                    (y i : ℝ) + ((if i = j then 1 else 0) - (if i = k then 1 else 0)) := by
                  have h00 := congrArg (fun t : ℕ => (t : ℝ)) h0
                  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at h00
                  split_ifs at h00 ⊢ <;> linarith
                simp only [h']
              · rw [if_neg hyk]
                have : y k = 0 := by omega
                rw [hz y hy k j this]; ring
          have h1 : ∑ x ∈ states n m, (x i : ℝ) * (p x * ∑ k, ∑ j, 1 * lam x k j) =
              ∑ x ∈ states n m, (x i : ℝ) * ∑ k, ∑ j, inflowTerm (fun _ _ => 1) lam p x k j :=
            Finset.sum_congr rfl (fun x hx => by rw [hbal x hx])
          have h2 : ∑ x ∈ states n m, (x i : ℝ) * ∑ k, ∑ j, inflowTerm (fun _ _ => 1) lam p x k j =
              ∑ k, ∑ j, ∑ x ∈ states n m, (x i : ℝ) * inflowTerm (fun _ _ => 1) lam p x k j := by
            simp only [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [Finset.sum_comm]
          simp only [key] at h2
          have hy : ∀ y, ∑ k, ∑ j, ((y i : ℝ) + ((if i = j then 1 else 0) - (if i = k then 1 else 0))) *
              (p y * lam y k j) = (y i : ℝ) * (p y * ∑ k, ∑ j, 1 * lam y k j) +
                (p y * ∑ k, lam y k i - p y * ∑ j, lam y i j) := by
            intro y
            have ea : ∑ k, ∑ j, (if i = j then (1:ℝ) else 0) * (p y * lam y k j) = p y * ∑ k, lam y k i := by
              simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
                Finset.mul_sum]
            have eb : ∑ k, ∑ j, (if i = k then (1:ℝ) else 0) * (p y * lam y k j) = p y * ∑ j, lam y i j := by
              simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
                Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
            have ec : ∑ k, ∑ j, (y i : ℝ) * (p y * lam y k j) = (y i : ℝ) * (p y * ∑ k, ∑ j, 1 * lam y k j) := by
              simp only [one_mul, Finset.mul_sum]
            rw [← ea, ← eb, ← ec, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            ring
          have h3 : ∑ k, ∑ j, ∑ y ∈ states n m, ((y i : ℝ) + ((if i = j then 1 else 0) -
              (if i = k then 1 else 0))) * (p y * lam y k j) =
              ∑ y ∈ states n m, ∑ k, ∑ j, ((y i : ℝ) + ((if i = j then 1 else 0) -
              (if i = k then 1 else 0))) * (p y * lam y k j) := by
            calc _ = ∑ k, ∑ y ∈ states n m, ∑ j, ((y i : ℝ) + ((if i = j then 1 else 0) -
                  (if i = k then 1 else 0))) * (p y * lam y k j) :=
                  Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
              _ = _ := Finset.sum_comm
          rw [h3] at h2
          simp only [hy, Finset.sum_add_distrib, Finset.sum_sub_distrib] at h2
          linarith
        obtain ⟨hfeas, hmax⟩ := hopt
        have hsa : ∀ (x : Fin n → ℕ) k i, serveAll x k i = if 0 < x k then (1:ℝ) else 0 := by
          intro x k i; rfl
        have hUB : redirectObj n m φ (constReward I) c serveAll r π ≤ alg8Obj φ I c qt zt := by
          have hπ' := hπ
          obtain ⟨hπnn, hπoff, hπsum, -⟩ := hπ'
          set s : (Fin n → ℕ) → Fin n → ℝ := fun x k => if 0 < x k then 1 else 0 with hs
          have hs01 : ∀ x k, 0 ≤ s x k ∧ s x k ≤ 1 := by
            intro x k; simp only [hs]; split_ifs <;> norm_num
          have hrn : ∀ x ∈ states n m, ∀ k i j, 0 ≤ r x k i j := fun x hx k i j => (hr.2 x hx k i).1 j
          have hrs : ∀ x ∈ states n m, ∀ k i, ∑ j, r x k i j ≤ 1 := fun x hx k i => (hr.2 x hx k i).2
          set q' : Fin n → ℝ := fun k => ∑ x ∈ states n m, π x * s x k with hq'
          set z' : Fin n → Fin n → ℝ := fun i j =>
            ∑ x ∈ states n m, π x * ∑ k, φ k i * s x k * r x k i j with hz'
          have hlam : ∀ x k j, redirectRate φ serveAll r x k j =
              φ k j * s x k * (1 - ∑ l, r x k j l) + ∑ a, φ k a * s x k * r x k a j := by
            intro x k j; simp only [redirectRate, hsa, hs]
          have hin : ∀ i, ∑ x ∈ states n m, π x * ∑ k, redirectRate φ serveAll r x k i =
              ∑ k, φ k i * q' k - ∑ l, z' i l + ∑ a, z' a i := by
            intro i
            have e : ∀ x, π x * ∑ k, redirectRate φ serveAll r x k i =
                ∑ k, φ k i * (π x * s x k) - ∑ l, π x * ∑ k, φ k i * s x k * r x k i l +
                  ∑ a, π x * ∑ k, φ k a * s x k * r x k a i := by
              intro x
              have e2 : ∑ l, π x * ∑ k, φ k i * s x k * r x k i l =
                  π x * ∑ k, φ k i * s x k * ∑ l, r x k i l := by
                rw [← Finset.mul_sum, Finset.sum_comm]
                simp only [Finset.mul_sum]
              have e3 : ∑ a, π x * ∑ k, φ k a * s x k * r x k a i =
                  π x * ∑ k, ∑ a, φ k a * s x k * r x k a i := by
                rw [← Finset.mul_sum, Finset.sum_comm]
              rw [e2, e3]
              simp only [hlam, mul_sub, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib,
                Finset.mul_sum, mul_add]
              ring_nf
            rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_add_distrib, Finset.sum_sub_distrib]
            congr 1
            congr 1
            · simp only [hq', Finset.mul_sum]
              exact Finset.sum_comm
            · simp only [hz']
              exact Finset.sum_comm
            · simp only [hz']
              exact Finset.sum_comm
          have hout : ∀ i, ∑ x ∈ states n m, π x * ∑ j, redirectRate φ serveAll r x i j =
              q' i * ∑ j, φ i j := by
            intro i
            have e : ∀ x, ∑ j, redirectRate φ serveAll r x i j = s x i * ∑ j, φ i j := by
              intro x
              simp only [hlam, mul_sub, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib]
              have e4 : ∑ j, ∑ a, φ i a * s x i * r x i a j = ∑ j, φ i j * s x i * ∑ l, r x i j l := by
                rw [Finset.sum_comm]
                simp only [Finset.mul_sum]
              rw [e4, sub_add_cancel, Finset.mul_sum]
              exact Finset.sum_congr rfl (fun j _ => by ring)
            simp only [e, hq', Finset.sum_mul]
            refine Finset.sum_congr rfl (fun x _ => by ring)
          have hfe : IsAlg8Feasible φ q' z' := by
            refine ⟨fun i _ => ⟨?_, ?_⟩, fun i j => ?_, fun i => ?_, fun i => ?_⟩
            · exact Finset.sum_nonneg (fun x _ => mul_nonneg (hπnn x) (hs01 x i).1)
            · rw [← hπsum]
              exact Finset.sum_le_sum (fun x _ => mul_le_of_le_one_right (hπnn x) (hs01 x i).2)
            · exact Finset.sum_nonneg (fun x hx => mul_nonneg (hπnn x) (Finset.sum_nonneg
                (fun k _ => mul_nonneg (mul_nonneg (hφ k i) (hs01 x k).1) (hrn x hx k i j))))
            · have h1 := hB _ π hπ (fun x hx k j hk => by
                rw [hlam]; simp [hs, hk]) i
              rw [hin, hout] at h1
              beta_reduce
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
              linarith [h1, mul_comm (q' i) (∑ j, φ i j)]
            · calc ∑ l, z' i l = ∑ x ∈ states n m, π x * ∑ k, φ k i * s x k * ∑ l, r x k i l := by
                    simp only [hz']
                    rw [Finset.sum_comm]
                    refine Finset.sum_congr rfl (fun x _ => ?_)
                    rw [← Finset.mul_sum, Finset.sum_comm]
                    simp only [Finset.mul_sum]
                _ ≤ ∑ x ∈ states n m, π x * ∑ k, φ k i * s x k := by
                    refine Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left
                      (Finset.sum_le_sum (fun k _ => ?_)) (hπnn x))
                    exact mul_le_of_le_one_right (mul_nonneg (hφ k i) (hs01 x k).1) (hrs x hx k i)
                _ = ∑ j, φ j i * q' j := by
                    simp only [hq', Finset.mul_sum]
                    rw [Finset.sum_comm]
                    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun x _ => by ring))
          have hobj : redirectObj n m φ (constReward I) c serveAll r π = alg8Obj φ I c q' z' := by
            have hsa' : ∀ x k i, serveAll x k i = s x k := fun _ _ _ => rfl
            have T1 : ∑ i, ∑ j, φ i j * q' i * I i j =
                ∑ x ∈ states n m, π x * ∑ k, ∑ i, φ k i * (s x k * I k i) := by
              simp only [hq', Finset.mul_sum, Finset.sum_mul]
              calc _ = ∑ i, ∑ x ∈ states n m, ∑ j, φ i j * (π x * s x i) * I i j :=
                    Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
                _ = _ := by
                    rw [Finset.sum_comm]
                    exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl
                      (fun k _ => Finset.sum_congr rfl (fun i _ => by ring)))
            have T2 : ∑ i, ∑ j, c i j * z' i j =
                ∑ x ∈ states n m, π x * ∑ k, ∑ i, φ k i * (s x k * ∑ j, r x k i j * c i j) := by
              simp only [hz', Finset.mul_sum]
              calc _ = ∑ i, ∑ x ∈ states n m, ∑ j, ∑ k, c i j * (π x * (φ k i * s x k * r x k i j)) :=
                    Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
                _ = ∑ x ∈ states n m, ∑ i, ∑ j, ∑ k, c i j * (π x * (φ k i * s x k * r x k i j)) :=
                    Finset.sum_comm
                _ = ∑ x ∈ states n m, ∑ i, ∑ k, ∑ j, c i j * (π x * (φ k i * s x k * r x k i j)) :=
                    Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
                _ = ∑ x ∈ states n m, ∑ k, ∑ i, ∑ j, c i j * (π x * (φ k i * s x k * r x k i j)) :=
                    Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
                _ = _ := Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl
                      (fun k _ => Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
                        (fun j _ => by ring))))
            have hR : alg8Obj φ I c q' z' = ∑ i, ∑ j, φ i j * q' i * I i j - ∑ i, ∑ j, c i j * z' i j := by
              simp only [alg8Obj, Finset.sum_sub_distrib]
            rw [hR, T1, T2, ← Finset.sum_sub_distrib]
            simp only [redirectObj, rewardCurve, constReward, hsa']
            refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [← mul_sub, ← Finset.sum_sub_distrib]
            congr 1
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            ring
          rw [hobj]
          exact hmax q' z' hfe
        obtain ⟨hq, hz, hcirc, hzle⟩ := hfeas
        have hq0 : ∀ i, 0 ≤ qt i := fun i => (hq i i).1
        have hq1 : ∀ i, qt i ≤ 1 := fun i => (hq i i).2
        have hV0 : 0 ≤ alg8Obj φ I c qt zt := by
          have h0 : IsAlg8Feasible φ (fun _ => 0) (fun _ _ => 0) := by
            refine ⟨fun i j => ⟨le_refl _, zero_le_one⟩, fun _ _ => le_refl _, fun i => ?_, fun i => ?_⟩
            · simp
            · simp
          have := hmax _ _ h0
          simpa [alg8Obj] using this
        have hcoef : 0 ≤ (m:ℝ) / ((m:ℝ) + n - 1) := by
          rcases Nat.eq_zero_or_pos m with h | h
          · subst h; simp
          · apply div_nonneg (by positivity)
            have : (1:ℝ) ≤ m := by exact_mod_cast h
            have : (0:ℝ) ≤ n := by positivity
            linarith
        have hLHS : (m:ℝ) / ((m:ℝ) + n - 1) * redirectObj n m φ (constReward I) c serveAll r π ≤
            (m:ℝ) / ((m:ℝ) + n - 1) * alg8Obj φ I c qt zt := mul_le_mul_of_nonneg_left hUB hcoef
        refine le_trans hLHS ?_
        -- the reward vector B
        set D : Fin n → ℝ := fun i => ∑ k, φ k i * qt k with hD
        have hDnn : ∀ i, 0 ≤ D i := fun i =>
          Finset.sum_nonneg (fun k _ => mul_nonneg (hφ k i) (hq0 k))
        have hrtD : ∀ i l, rt i l * D i = zt i l := by
          intro i l
          by_cases h0 : D i = 0
          · have h1 : zt i l ≤ ∑ k, zt i k :=
              Finset.single_le_sum (fun k _ => hz i k) (Finset.mem_univ l)
            have h2 := hzle i
            have : zt i l = 0 := le_antisymm (by simp only [hD] at h0; linarith) (hz i l)
            rw [h0, this, mul_zero]
          · rw [hrt]
            show zt i l / D i * D i = zt i l
            exact div_mul_cancel₀ _ h0
        have hrtnn : ∀ i l, 0 ≤ rt i l := by
          intro i l; rw [hrt]; exact div_nonneg (hz i l) (hDnn i)
        have hrtle : ∀ i, ∑ l, rt i l ≤ 1 := by
          intro i
          rw [hrt]
          show ∑ l, zt i l / D i ≤ 1
          rw [← Finset.sum_div]
          exact div_le_one_of_le₀ (hzle i) (hDnn i)
        set B : Fin n → ℝ := fun k => ∑ i, φ k i * (I k i - ∑ j, rt i j * c i j) with hB'
        have hVB : alg8Obj φ I c qt zt = ∑ k, qt k * B k := by
          simp only [alg8Obj, hB', Finset.sum_sub_distrib, mul_sub, Finset.mul_sum]
          congr 1
          · exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
          · calc ∑ i, ∑ j, c i j * zt i j = ∑ i, ∑ j, c i j * (rt i j * D i) := by
                  simp only [hrtD]
              _ = ∑ i, ∑ j, ∑ k, qt k * (φ k i * (rt i j * c i j)) := by
                  simp only [hD, Finset.mul_sum]
                  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
                    Finset.sum_congr rfl (fun k _ => by ring)))
              _ = ∑ i, ∑ k, ∑ j, qt k * (φ k i * (rt i j * c i j)) :=
                  Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
              _ = _ := Finset.sum_comm
        have hRHS : redirectObj n m φ (constReward I) c serveAll (toRedirect rt) πt =
            ∑ x ∈ states n m, πt x * ∑ k, (if 0 < x k then (1:ℝ) else 0) * B k := by
          simp only [redirectObj, rewardCurve, constReward, hsa, toRedirect, hB']
          refine Finset.sum_congr rfl (fun x _ => ?_)
          congr 1
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          split_ifs <;> simp
        rw [hRHS]
        obtain ⟨hπtnn, hπtoff, hπtsum, hπtbal⟩ := hπt
        by_cases hqt0 : qt = 0
        · -- degenerate case
          have hI := hsign.resolve_left (not_not.mpr hqt0)
          have hVz : alg8Obj φ I c qt zt = 0 := by
            rw [hVB, hqt0]; simp
          have hrt0 : ∀ i j, rt i j = 0 := by
            intro i j; rw [hrt]
            show zt i j / D i = 0
            have : D i = 0 := by simp [hD, hqt0]
            rw [this, div_zero]
          rw [hVz, mul_zero]
          refine Finset.sum_nonneg (fun x _ => mul_nonneg (hπtnn x) (Finset.sum_nonneg (fun k _ => ?_)))
          apply mul_nonneg (by split_ifs <;> norm_num)
          simp only [hB', hrt0, zero_mul, Finset.sum_const_zero, sub_zero]
          exact hI k
        have hconn' := hconn.resolve_right hqt0
        have hn : 0 < n := by
          rcases Nat.eq_zero_or_pos n with h | h
          · subst h; exact absurd (funext (fun i => i.elim0)) hqt0
          · exact h
        set Φ := inducedDemand φ (fun _ _ => 1) rt with hΦ
        have hΦnn : ∀ i j, 0 ≤ Φ i j := by
          intro i j
          show 0 ≤ φ i j * 1 * (1 - ∑ k, rt j k) + ∑ k, φ i k * 1 * rt k j
          have := hrtle j
          apply add_nonneg
          · exact mul_nonneg (by simpa using hφ i j) (by linarith)
          · exact Finset.sum_nonneg (fun k _ => mul_nonneg (by simpa using hφ i k) (hrtnn k j))
        have hΦout : ∀ i, ∑ j, Φ i j = ∑ j, φ i j := by
          intro i
          simp only [hΦ, inducedDemand, mul_one, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum]
          rw [Finset.sum_comm (f := fun j k => φ i k * rt k j)]
          ring
        have hTr : ∀ j, ∑ k, qt k * Φ k j = qt j * ∑ l, Φ j l := by
          intro j
          rw [hΦout]
          have e : ∑ k, qt k * Φ k j = D j * (1 - ∑ l, rt j l) + ∑ l, rt l j * D l := by
            simp only [hΦ, inducedDemand, mul_one, mul_add, Finset.sum_add_distrib, hD]
            congr 1
            · rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun k _ => by ring)
            · simp only [Finset.mul_sum]; rw [Finset.sum_comm]
              exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => by ring))
          rw [e]
          have hc := hcirc j
          beta_reduce at hc
          simp only [Finset.sum_add_distrib] at hc
          have e2 : ∑ l, rt l j * D l = ∑ k, zt k j := Finset.sum_congr rfl (fun l _ => hrtD l j)
          have e3 : D j * ∑ l, rt j l = ∑ l, zt j l := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun l _ => by rw [mul_comm]; exact hrtD j l)
          rw [mul_sub, mul_one, e2, e3, Finset.mul_sum]
          have e4 : ∑ l, φ j l * qt j = ∑ l, qt j * φ j l := Finset.sum_congr rfl (fun l _ => mul_comm _ _)
          have e5 : D j = ∑ k, φ k j * qt k := rfl
          linarith
        obtain ⟨a0, ha0⟩ : ∃ a, 0 < qt a := by
          by_contra h; push_neg at h
          exact hqt0 (funext (fun i => le_antisymm (h i) (hq0 i)))
        have hpos : ∀ b, 0 < qt b := by
          intro b
          have hp := hconn' a0 b
          induction hp with
          | refl => exact ha0
          | @tail b' c' _ hbc ih =>
            have h1 := hTr c'
            have h2 : qt b' * Φ b' c' ≤ ∑ k, qt k * Φ k c' :=
              Finset.single_le_sum (fun k _ => mul_nonneg (hq0 k) (hΦnn k c')) (Finset.mem_univ b')
            have h3 : 0 < qt b' * Φ b' c' := mul_pos ih (by simpa using hbc.2)
            by_contra hc
            have : qt c' = 0 := le_antisymm (not_lt.mp hc) (hq0 c')
            rw [this, zero_mul] at h1
            linarith
        have hlamt : ∀ x k j, redirectRate φ serveAll (toRedirect rt) x k j =
            if 0 < x k then Φ k j else 0 := by
          intro x k j
          simp only [redirectRate, hsa, toRedirect, hΦ, inducedDemand]
          split_ifs <;> simp
        set lamt := redirectRate φ serveAll (toRedirect rt) with hlamt_def
        have hlamtnn : ∀ x k j, 0 ≤ lamt x k j := by
          intro x k j; rw [hlamt]; split_ifs
          · exact hΦnn k j
          · exact le_refl _
        set w : (Fin n → ℕ) → ℝ := fun x => ∏ l, qt l ^ x l with hw
        have hwpos : ∀ x, 0 < w x := fun x => Finset.prod_pos (fun l _ => pow_pos (hpos l) _)
        have hprod1 : ∀ b : Fin n, ∏ l, qt l ^ (if l = b then 1 else 0) = qt b := by
          intro b
          rw [Finset.prod_congr rfl (fun l _ => (show qt l ^ (if l = b then 1 else 0) =
            if l = b then qt l else 1 by split_ifs <;> simp))]
          simp
        have hwshift : ∀ (x y : Fin n → ℕ) (a b : Fin n),
            (∀ l, y l + (if l = b then 1 else 0) = x l + (if l = a then 1 else 0)) →
            w y * qt b = w x * qt a := by
          intro x y a b h
          rw [← hprod1 b, ← hprod1 a]
          simp only [hw, ← Finset.prod_mul_distrib, ← pow_add, h]
        have hwup : ∀ (y : Fin n → ℕ) (i : Fin n), w (Function.update y i (y i + 1)) = qt i * w y := by
          intro y i
          rw [← hprod1 i]; simp only [hw, hupd, pow_add, Finset.prod_mul_distrib]; ring
        have hwbal : ∀ x ∈ states n m, w x * (∑ a, ∑ b, 1 * lamt x a b) =
            ∑ a, ∑ b, inflowTerm (fun _ _ => 1) lamt w x a b := by
          intro x hx
          rw [Finset.sum_comm (f := fun a b => inflowTerm (fun _ _ => 1) lamt w x a b)]
          have hcol : ∀ b, ∑ a, inflowTerm (fun _ _ => 1) lamt w x a b =
              if 1 ≤ x b then w x * ∑ l, Φ b l else 0 := by
            intro b
            by_cases hxb : 1 ≤ x b
            · rw [if_pos hxb]
              have ht : ∀ a, inflowTerm (fun _ _ => 1) lamt w x a b = w x / qt b * (qt a * Φ a b) := by
                intro a
                have hqb := hpos b
                by_cases hab : a = b
                · subst hab
                  simp only [inflowTerm, if_true, hlamt, if_pos (show 0 < x a by omega)]
                  field_simp
                · simp only [inflowTerm, if_neg hab, if_pos hxb, hlamt]
                  have h1 := hms x a b hab hxb
                  have hpa : 0 < moveState x a b a := by
                    have := h1 a; simp only [if_neg hab, if_true] at this; omega
                  rw [if_pos hpa]
                  have h2 := hwshift x _ a b h1
                  have hw' : w (moveState x a b) = w x * qt a / qt b := by
                    rw [eq_div_iff hqb.ne']; exact h2
                  rw [hw']; ring
              rw [Finset.sum_congr rfl (fun a _ => ht a), ← Finset.mul_sum, hTr b]
              field_simp [(hpos b).ne']
            · rw [if_neg hxb]
              refine Finset.sum_eq_zero (fun a _ => ?_)
              by_cases hab : a = b
              · subst hab; simp only [inflowTerm, if_true, hlamt, if_neg (show ¬ 0 < x a by omega)]; ring
              · simp only [inflowTerm, if_neg hab, if_neg hxb]
          rw [Finset.sum_congr rfl (fun b _ => hcol b), Finset.mul_sum]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          simp only [hlamt, one_mul]
          by_cases h1 : 0 < x a
          · rw [if_pos (show 1 ≤ x a by omega)]; simp only [if_pos h1]
          · rw [if_neg (show ¬ 1 ≤ x a by omega)]; simp only [if_neg h1]; simp
        have hSne : (states n m).Nonempty := by
          by_contra h
          rw [Finset.not_nonempty_iff_eq_empty] at h
          rw [h, Finset.sum_empty] at hπtsum
          exact zero_ne_one hπtsum
        obtain ⟨x0, hx0, hmin⟩ := Finset.exists_min_image (states n m) (fun x => πt x / w x) hSne
        set t := πt x0 / w x0 with ht
        set ν : (Fin n → ℕ) → ℝ := fun x => πt x - t * w x with hν
        have hνnn : ∀ x ∈ states n m, 0 ≤ ν x := by
          intro x hx
          have := hmin x hx
          simp only [hν]
          rw [le_div_iff₀ (hwpos x)] at this
          linarith
        have hν0 : ν x0 = 0 := by
          simp only [hν, ht]
          field_simp [(hwpos x0).ne']
          ring
        have hinfl : ∀ x a b, inflowTerm (fun _ _ => 1) lamt ν x a b =
            inflowTerm (fun _ _ => 1) lamt πt x a b - t * inflowTerm (fun _ _ => 1) lamt w x a b := by
          intro x a b; simp only [inflowTerm, hν]; split_ifs <;> ring
        have hνbal : ∀ x ∈ states n m, ν x * (∑ a, ∑ b, 1 * lamt x a b) =
            ∑ a, ∑ b, inflowTerm (fun _ _ => 1) lamt ν x a b := by
          intro x hx
          have h1 := hπtbal x hx
          have h2 := hwbal x hx
          beta_reduce at h1
          have h3 : ∑ a, ∑ b, inflowTerm (fun _ _ => 1) lamt ν x a b =
              ∑ a, ∑ b, inflowTerm (fun _ _ => 1) lamt πt x a b -
                t * ∑ a, ∑ b, inflowTerm (fun _ _ => 1) lamt w x a b := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl (fun b _ => hinfl x a b)
          rw [h3, ← h1, ← h2]
          simp only [hν]
          ring
        have hstep : ∀ x ∈ states n m, ν x = 0 → ∀ k j, k ≠ j → 0 < Φ k j → ∀ y : Fin n → ℕ,
            (∀ l, y l + (if l = j then 1 else 0) = x l + (if l = k then 1 else 0)) → ν y = 0 := by
          intro x hx hνx k j hkj hΦkj y hy
          have hxj : 1 ≤ x j := by have := hy j; simp only [if_true, if_neg (Ne.symm hkj)] at this; omega
          have hyk : 0 < y k := by have := hy k; simp only [if_true, if_neg hkj] at this; omega
          have hyeq := hmsu x y k j hy hkj
          have hbal := hνbal x hx
          rw [hνx, zero_mul] at hbal
          have hterm : ∀ a b, 0 ≤ inflowTerm (fun _ _ => 1) lamt ν x a b := by
            intro a b
            simp only [inflowTerm]
            split_ifs with hab hb
            · rw [hνx]; simp
            · have hmS := hmem x hx _ a b (hms x a b hab hb)
              exact mul_nonneg (mul_nonneg (hνnn _ hmS) zero_le_one) (hlamtnn _ _ _)
            · exact le_refl _
          have hz1 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
            Finset.sum_nonneg (fun b _ => hterm a b))).mp hbal.symm k (Finset.mem_univ k)
          have hz2 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hterm k b)).mp hz1 j
            (Finset.mem_univ j)
          simp only [inflowTerm, if_neg hkj, if_pos hxj, ← hyeq, hlamt, if_pos hyk, mul_one] at hz2
          rcases mul_eq_zero.mp hz2 with h | h
          · exact h
          · exact absurd h hΦkj.ne'
        have hpath : ∀ b a, Relation.ReflTransGen (fun a b => a ≠ b ∧ 0 < Φ a b * (fun _ _ => (1:ℝ)) a b) a b →
            ∀ x ∈ states n m, 1 ≤ x b → ν x = 0 → ∀ y : Fin n → ℕ,
            (∀ l, y l + (if l = b then 1 else 0) = x l + (if l = a then 1 else 0)) → ν y = 0 := by
          intro b a hab
          induction hab using Relation.ReflTransGen.head_induction_on with
          | refl =>
            intro x hx hxb hνx y hy
            have : y = x := funext (fun l => by have := hy l; omega)
            rw [this]; exact hνx
          | @head a c hac hcb ih =>
            intro x hx hxb hνx y hy
            set y' : Fin n → ℕ := fun l => x l + (if l = c then 1 else 0) - (if l = b then 1 else 0)
              with hy'
            have hy'e : ∀ l, y' l + (if l = b then 1 else 0) = x l + (if l = c then 1 else 0) := by
              intro l; simp only [hy']; split_ifs <;> subst_vars <;> omega
            have hν' := ih x hx hxb hνx y' hy'e
            have hy'S := hmem x hx y' c b hy'e
            apply hstep y' hy'S hν' a c hac.1 (by simpa using hac.2) y
            intro l
            have h1 := hy l
            have h2 := hy'e l
            omega
        have hall : ∀ y ∈ states n m, ν y = 0 := by
          intro y hy
          have key : ∀ d : ℕ, ∀ x ∈ states n m, ν x = 0 → ∑ l, (x l - y l) = d → ν y = 0 := by
            intro d
            induction d with
            | zero =>
              intro x hx hνx hd
              have hle : ∀ l ∈ Finset.univ, x l ≤ y l := by
                intro l _
                have := (Finset.sum_eq_zero_iff.mp hd) l (Finset.mem_univ l)
                omega
              have heq := (Finset.sum_eq_sum_iff_of_le hle).mp
                ((hsumS m x hx).trans (hsumS m y hy).symm)
              have : x = y := funext (fun l => heq l (Finset.mem_univ l))
              rw [← this]; exact hνx
            | succ d ih =>
              intro x hx hνx hd
              obtain ⟨b, hb⟩ : ∃ b, y b < x b := by
                by_contra h
                push_neg at h
                have : ∑ l, (x l - y l) = 0 :=
                  Finset.sum_eq_zero (fun l _ => by have := h l; omega)
                omega
              obtain ⟨a, ha⟩ : ∃ a, x a < y a := by
                by_contra h
                push_neg at h
                have heq := (Finset.sum_eq_sum_iff_of_le (fun l (_ : l ∈ Finset.univ) => h l)).mp
                  ((hsumS m y hy).trans (hsumS m x hx).symm)
                have := heq b (Finset.mem_univ b)
                omega
              have hab : a ≠ b := by rintro rfl; omega
              set x' : Fin n → ℕ := fun l => x l + (if l = a then 1 else 0) - (if l = b then 1 else 0)
                with hx'
              have hx'e : ∀ l, x' l + (if l = b then 1 else 0) = x l + (if l = a then 1 else 0) := by
                intro l; simp only [hx']; split_ifs <;> subst_vars <;> omega
              have hν' := hpath b a (hconn' a b) x hx (by omega) hνx x' hx'e
              have hx'S := hmem x hx x' a b hx'e
              apply ih x' hx'S hν'
              have hl : ∀ l, (x' l - y l) + (if l = b then 1 else 0) = x l - y l := by
                intro l
                simp only [hx']
                split_ifs <;> subst_vars <;> omega
              have := Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hl l)
              rw [Finset.sum_add_distrib, Finset.sum_ite_eq'] at this
              simp only [Finset.mem_univ, if_true] at this
              omega
          exact key _ x0 hx0 hν0 rfl
        have hπw : ∀ x ∈ states n m, πt x = t * w x := by
          intro x hx; have := hall x hx; simp only [hν] at this; linarith
        have ht0 : 0 ≤ t := div_nonneg (hπtnn x0) (hwpos x0).le
        rcases Nat.eq_zero_or_pos m with hm | hm
        · rw [hm]
          simp only [Nat.cast_zero, zero_div, zero_mul]
          apply le_of_eq
          symm
          refine Finset.sum_eq_zero (fun x hx => ?_)
          have h0 := hsumS 0 x hx
          have : ∀ k, x k = 0 := fun k => (Finset.sum_eq_zero_iff.mp h0) k (Finset.mem_univ k)
          simp [this]
        obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
        set Gm := ∑ x ∈ states n (M+1), w x with hGm
        set Gm1 := ∑ y ∈ states n M, w y with hGm1
        have htG : t * Gm = 1 := by
          rw [← hπtsum, hGm, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun x hx => (hπw x hx).symm)
        have hAk : ∀ k, ∑ x ∈ states n (M+1), πt x * (if 0 < x k then (1:ℝ) else 0) =
            t * qt k * Gm1 := by
          intro k
          have e : ∀ x ∈ states n (M+1), πt x * (if 0 < x k then (1:ℝ) else 0) =
              t * (if 1 ≤ x k then w x else 0) := by
            intro x hx
            rw [hπw x hx]
            by_cases h : 0 < x k
            · rw [if_pos h, if_pos (by omega)]; ring
            · rw [if_neg h, if_neg (by omega)]; ring
          rw [Finset.sum_congr rfl e, ← Finset.mul_sum, hA' M k w]
          simp only [hwup, hGm1, ← Finset.mul_sum]
          ring
        have hGN : ((M:ℝ) + 1) * Gm ≤ ((M:ℝ) + n) * Gm1 := by
          have e1 : ((M:ℝ) + 1) * Gm =
              ∑ i, ∑ x ∈ states n (M+1), (if 1 ≤ x i then (x i : ℝ) * w x else 0) := by
            rw [Finset.sum_comm, hGm, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun x hx => ?_)
            have hs : ∑ i, (x i : ℝ) = (M:ℝ) + 1 := by exact_mod_cast hsumS (M+1) x hx
            rw [← hs, Finset.sum_mul]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            split_ifs with h
            · rfl
            · have : x i = 0 := by omega
              simp [this]
          have e2 : ∀ i, ∑ x ∈ states n (M+1), (if 1 ≤ x i then (x i : ℝ) * w x else 0) =
              ∑ y ∈ states n M, ((y i : ℝ) + 1) * (qt i * w y) := by
            intro i
            rw [hA' M i (fun x => (x i : ℝ) * w x)]
            refine Finset.sum_congr rfl (fun y _ => ?_)
            simp only [hwup, hupd, if_true]
            push_cast
            ring
          have e3 : ∑ i, ∑ y ∈ states n M, ((y i : ℝ) + 1) * w y = ((M:ℝ) + n) * Gm1 := by
            rw [Finset.sum_comm, hGm1, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun y hy => ?_)
            have hs : ∑ i, (y i : ℝ) = (M:ℝ) := by exact_mod_cast hsumS M y hy
            rw [← Finset.sum_mul, Finset.sum_add_distrib, hs]
            simp
          rw [e1, ← e3]
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [e2 i]
          refine Finset.sum_le_sum (fun y _ => ?_)
          have : (0:ℝ) ≤ (y i : ℝ) + 1 := by positivity
          exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (hwpos y).le (hq1 i)) this
        have hR : ∑ x ∈ states n (M+1), πt x * ∑ k, (if 0 < x k then (1:ℝ) else 0) * B k =
            t * Gm1 * alg8Obj φ I c qt zt := by
          rw [hVB, Finset.mul_sum]
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          have := hAk k
          calc ∑ x ∈ states n (M+1), πt x * ((if 0 < x k then (1:ℝ) else 0) * B k) =
              (∑ x ∈ states n (M+1), πt x * (if 0 < x k then (1:ℝ) else 0)) * B k := by
                rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun x _ => by ring)
            _ = _ := by rw [this]; ring
        rw [hR]
        apply mul_le_mul_of_nonneg_right _ hV0
        have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
        have hM0 : (0:ℝ) ≤ M := by positivity
        have hden : (0:ℝ) < ((M+1 : ℕ):ℝ) + n - 1 := by push_cast; linarith
        rw [div_le_iff₀ hden]
        push_cast
        have h4 := mul_le_mul_of_nonneg_left hGN ht0
        have h5 : t * (((M:ℝ) + 1) * Gm) = (M:ℝ) + 1 := by
          rw [mul_left_comm, htG, mul_one]
        nlinarith [h4, h5]
