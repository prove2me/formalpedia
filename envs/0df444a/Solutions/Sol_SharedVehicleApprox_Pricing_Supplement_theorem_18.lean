-- Prove2me | solution 1 for SharedVehicleApprox.Pricing.Supplement.theorem_18
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:05:30.803597+00:00
-- url     : https://prove2.me/submissions/91058581-db49-4a72-b6ed-ca40dc2957d0

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_StationaryLaw
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_TravelTimes
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_Algorithm2

open Finset QueueingFundamentals.Networks

open SharedVehicleApprox
open SharedVehicleApprox.Pricing
open SharedVehicleApprox.Pricing.Supplement

/-- Theorem 18, p. 21 (corrected: the support graph of `q̃` is strongly connected, unless
`q̃ = 0`): with travel times and `m ≥ 100`, the output `q̃` of Algorithm 2 with
`ε_m = 2 √(ln m / m)` earns at least
`(1 − ε_m) (√(m ln m) / (√(m ln m) + n − 1) − 3 / √(m ln m))` times `Opt_m`. As the policy
`q ≡ 0` earns `0`, the bound is stated against `max (obj q π) 0`. -/
theorem solution {n m : ℕ} (hm : 100 ≤ m) (φ τ : Fin n → Fin n → ℝ)
    (hφ : ∀ i j, 0 ≤ φ i j) (hτ : ∀ i j, 0 < τ i j) (I : Fin n → Fin n → ℝ → ℝ)
    (hR : ∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (rewardCurve I i j))
    (q' qt : Fin n → Fin n → ℝ) (hopt : IsAlg2Optimal φ τ I m q')
    (hout : qt = alg2Output φ τ m (epsilon m) q')
    (hconn : SupportConnected φ qt ∨ qt = 0)
    (πt : TTState n → ℝ) (hπt : IsTTStationary n m φ τ (toTTPolicy qt) πt)
    (q : TTState n → Fin n → Fin n → ℝ) (π : TTState n → ℝ)
    (hq : IsTTPolicy n m q) (hπ : IsTTStationary n m φ τ q π) :
    delayFactor n m * max (ttObj n m φ I q π) 0 ≤ ttObj n m φ I (toTTPolicy qt) πt := by
      -- basic facts on ε
      have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm
      have hlog : Real.log m < m / 4 := by
        have h1 := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ m / 4 by positivity)
        rw [Real.log_lt_iff_lt_exp (by linarith)]
        have h2 : (m:ℝ) * 100 ≤ m * m := mul_le_mul_of_nonneg_left hmR (by linarith)
        linarith
      have hlogpos : 0 < Real.log m := Real.log_pos (by linarith)
      have hε0 : 0 < epsilon m := by
        unfold epsilon; have : 0 < Real.log m / m := by positivity
        positivity
      have hε1 : epsilon m < 1 := by
        unfold epsilon
        have h2 : Real.log m / m < 1 / 4 := by rw [div_lt_iff₀ (by positivity)]; linarith
        have h3 : Real.sqrt (Real.log m / m) < 1 / 2 := by
          rw [show (1:ℝ)/2 = Real.sqrt (1/4) by
            rw [show (1:ℝ)/4 = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
          exact Real.sqrt_lt_sqrt (by positivity) h2
        linarith
      set ε := epsilon m with hεdef
      -- R(0) = 0
      have hR0 : ∀ i j, rewardCurve I i j 0 = 0 := fun i j => by simp [rewardCurve]
      obtain ⟨⟨hq'01, hq'bal⟩, hq'tau⟩ := hopt.1
      -- elevObj q' ≥ 0
      have hE'0 : 0 ≤ elevObj φ I q' := by
        have h0 : IsAlg2Feasible φ τ m (fun _ _ => 0) := by
          refine ⟨⟨fun i j => ⟨le_refl _, zero_le_one⟩, fun i => by simp only [mul_zero]⟩, ?_⟩
          simp only [mul_zero, Finset.sum_const_zero]; exact Nat.cast_nonneg m
        have h1 := hopt.2 _ h0
        have h2 : elevObj φ I (fun _ _ => 0) = 0 := by
          simp only [elevObj, hR0, mul_zero, Finset.sum_const_zero]
        rw [h2] at h1; exact h1
      -- properties of qt
      have hqt : (∀ i j, 0 ≤ qt i j ∧ qt i j ≤ 1) ∧ IsBalanced φ qt ∧
          (∑ i, ∑ j, φ i j * τ i j * qt i j ≤ m * (1 - ε)) ∧
          (1 - ε) * elevObj φ I q' ≤ elevObj φ I qt ∧ (qt = 0 → q' = 0) := by
        rw [hout]; unfold alg2Output
        split_ifs with hc
        · refine ⟨fun i j => ⟨mul_nonneg (hq'01 i j).1 (by linarith),
              mul_le_one₀ (hq'01 i j).2 (by linarith) (by linarith)⟩, ?_, ?_, ?_, ?_⟩
          · intro i
            have := hq'bal i
            simp only [← mul_assoc, ← Finset.sum_mul]
            rw [this]
          · have : ∑ i, ∑ j, φ i j * τ i j * (q' i j * (1 - ε)) =
                (∑ i, ∑ j, φ i j * τ i j * q' i j) * (1 - ε) := by
              simp only [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun j _ => ?_; ring
            rw [this]; exact mul_le_mul_of_nonneg_right hq'tau (by linarith)
          · unfold elevObj
            rw [Finset.mul_sum]; refine Finset.sum_le_sum fun i _ => ?_
            rw [Finset.mul_sum]; refine Finset.sum_le_sum fun j _ => ?_
            have hc' := (hR i j).2 (show (0:ℝ) ∈ Set.Icc 0 1 by simp)
              (show q' i j ∈ Set.Icc 0 1 from ⟨(hq'01 i j).1, (hq'01 i j).2⟩)
              (show (0:ℝ) ≤ ε from hε0.le) (show (0:ℝ) ≤ 1 - ε by linarith) (by ring)
            simp only [smul_eq_mul, mul_zero, zero_add, hR0] at hc'
            show (1 - ε) * (φ i j * rewardCurve I i j (q' i j)) ≤ φ i j * rewardCurve I i j (q' i j * (1 - ε))
            rw [show q' i j * (1 - ε) = (1 - ε) * q' i j by ring]
            have h3 := mul_le_mul_of_nonneg_left hc' (hφ i j)
            calc (1 - ε) * (φ i j * rewardCurve I i j (q' i j))
                = φ i j * ((1 - ε) * rewardCurve I i j (q' i j)) := by ring
              _ ≤ _ := h3
          · intro h0; funext i j
            have := congrFun (congrFun h0 i) j
            simp only [Pi.zero_apply] at this
            rcases mul_eq_zero.1 this with h | h
            · exact h
            · exact absurd h (by linarith)
        · refine ⟨hq'01, hq'bal, by push Not at hc; linarith,
            by have := mul_nonneg hε0.le hE'0; linarith, fun h => h⟩
      obtain ⟨hqt01, hqtbal, hqtW, hqtE, hqt0⟩ := hqt
      have hEqt0 : 0 ≤ elevObj φ I qt := by
        have := mul_nonneg (show (0:ℝ) ≤ 1 - ε by linarith) hE'0; linarith
      -- membership from the sum condition
      have hmem : ∀ t : TTState n, (∑ i, t.1 i) + (∑ i, ∑ j, t.2 i j) = m → t ∈ (ttStates n m) := by
        intro t ht
        simp only [ttStates, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset,
          Finset.mem_range]
        refine ⟨⟨fun i => ?_, fun i j => ?_⟩, ht⟩
        · have := Finset.single_le_sum (f := t.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          omega
        · have h1 := Finset.single_le_sum (f := t.2 i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
          have h2 := Finset.single_le_sum (f := fun i => ∑ j, t.2 i j) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ i)
          omega
      have hsumSt : ∀ s ∈ (ttStates n m), (∑ i, s.1 i) + (∑ i, ∑ j, s.2 i j) = m := fun s hs =>
        (Finset.mem_filter.1 hs).2
      have hLU : ∀ i j : Fin n, (∑ a, ∑ b, linkUnit i j a b) = 1 := by
        intro i j
        simp [linkUnit, ite_and]
      have hdep : ∀ s ∈ (ttStates n m), ∀ i j, 0 < s.1 i → (s.1 - Pi.single i 1, s.2 + linkUnit i j) ∈ (ttStates n m) := by
        intro s hs i j hi
        apply hmem
        have h1 : (∑ k, s.1 k) = (∑ k, ((s.1 - Pi.single i 1 : Fin n → ℕ)) k) + 1 := by
          have : ∀ k, s.1 k = (s.1 - Pi.single i 1 : Fin n → ℕ) k + (Pi.single i 1 : Fin n → ℕ) k := by
            intro k; by_cases hk : k = i
            · subst hk; simp; omega
            · simp [hk]
          rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_add_distrib]; simp
        have h2 : (∑ a, ∑ b, (s.2 + linkUnit i j) a b) = (∑ a, ∑ b, s.2 a b) + 1 := by
          simp only [Pi.add_apply, Finset.sum_add_distrib, hLU]
        simp only; rw [h2]; have := hsumSt s hs; omega
      have harr : ∀ s ∈ (ttStates n m), ∀ i j, 0 < s.2 i j → (s.1 + Pi.single j 1, s.2 - linkUnit i j) ∈ (ttStates n m) := by
        intro s hs i j hij
        apply hmem
        have h1 : (∑ k, ((s.1 + Pi.single j 1 : Fin n → ℕ)) k) = (∑ k, s.1 k) + 1 := by
          simp only [Pi.add_apply, Finset.sum_add_distrib]; simp
        have h2 : (∑ a, ∑ b, s.2 a b) = (∑ a, ∑ b, (s.2 - linkUnit i j) a b) + 1 := by
          have : ∀ a b, s.2 a b = (s.2 - linkUnit i j) a b + linkUnit i j a b := by
            intro a b; simp only [Pi.sub_apply, linkUnit]
            split_ifs with h
            · obtain ⟨rfl, rfl⟩ := h; omega
            · omega
          rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => this a b))]
          simp only [Finset.sum_add_distrib, hLU]
        simp only; rw [h1]; have := hsumSt s hs; omega
      -- generator applied to g
      have hgenG : ∀ (Q : TTState n → Fin n → Fin n → ℝ) (g : TTState n → ℝ), ∀ s ∈ (ttStates n m),
          (∑ t ∈ (ttStates n m), ttRate φ τ Q s t * (g t - g s)) =
            ∑ i, ∑ j, ((if 0 < s.1 i then φ i j * Q s i j *
                (g (s.1 - Pi.single i 1, s.2 + linkUnit i j) - g s) else 0) +
              (if 0 < s.2 i j then (s.2 i j : ℝ) / τ i j *
                (g (s.1 + Pi.single j 1, s.2 - linkUnit i j) - g s) else 0)) := by
        intro Q g s hs
        simp only [ttRate, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [add_mul]
        rw [Finset.sum_add_distrib]
        congr 1
        · by_cases hi : 0 < s.1 i
          · simp only [hi, true_and, if_true, ite_mul, zero_mul]
            rw [Finset.sum_ite_eq' (ttStates n m)]; simp [hdep s hs i j hi]
          · simp [hi]
        · by_cases hi : 0 < s.2 i j
          · simp only [hi, true_and, if_true, ite_mul, zero_mul]
            rw [Finset.sum_ite_eq' (ttStates n m)]; simp [harr s hs i j hi]
          · simp [hi]
      -- the test-function identity
      have htestG : ∀ (Q : TTState n → Fin n → Fin n → ℝ) (πt : TTState n → ℝ),
          IsTTStationary n m φ τ Q πt → ∀ (g : TTState n → ℝ),
          (∑ s ∈ (ttStates n m), πt s * ∑ t ∈ (ttStates n m), ttRate φ τ Q s t * (g t - g s)) = 0 := by
        intro Q πt hπt g
        have hbalance := hπt.2.2.2
        have hb : ∀ s ∈ (ttStates n m), πt s * (∑ t ∈ (ttStates n m), ttRate φ τ Q s t) =
            ∑ t ∈ (ttStates n m), πt t * ttRate φ τ Q t s := by
          intro s hs
          have := hbalance ⟨s, hs⟩
          simp only [tsum_fintype] at this
          rw [← Finset.sum_coe_sort (ttStates n m) (fun t => ttRate φ τ Q s t),
            ← Finset.sum_coe_sort (ttStates n m) (fun t => πt t * ttRate φ τ Q t s)]
          exact this
        have e1 : (∑ s ∈ (ttStates n m), πt s * ∑ t ∈ (ttStates n m), ttRate φ τ Q s t * (g t - g s)) =
            (∑ s ∈ (ttStates n m), ∑ t ∈ (ttStates n m), πt s * ttRate φ τ Q s t * g t) -
              ∑ s ∈ (ttStates n m), g s * (πt s * ∑ t ∈ (ttStates n m), ttRate φ τ Q s t) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun t _ => ?_; ring
        have e2 : (∑ s ∈ (ttStates n m), g s * (πt s * ∑ t ∈ (ttStates n m), ttRate φ τ Q s t)) =
            ∑ s ∈ (ttStates n m), ∑ t ∈ (ttStates n m), πt s * ttRate φ τ Q s t * g t := by
          rw [Finset.sum_congr rfl (fun s hs => by rw [hb s hs])]
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_; ring
        rw [e1, e2, sub_self]

      have hmemIff : ∀ t : TTState n, t ∈ ttStates n m ↔ (∑ i, t.1 i) + (∑ i, ∑ j, t.2 i j) = m :=
        fun t => ⟨fun h => hsumSt t h, hmem t⟩
      have hA : ttObj n m φ I q π ≤ elevObj φ I q' := by
        clear * - hφ hτ hR hopt hq hπ hmemIff htestG hgenG
        have hmem := hmemIff
        have htest := htestG q π hπ
        have hgen := hgenG q
        unfold IsTTStationary IsStationaryLaw at hπ
        obtain ⟨hπ0, hπout, hπ1, hπB⟩ := hπ
        have hq0 : ∀ s ∈ ttStates n m, ∀ a b, (if 0 < s.1 a then φ a b * q s a b else 0) = φ a b * q s a b := by
          intro s hs a b
          split_ifs with h
          · rfl
          · rw [(hq s hs a b).2.2 (by omega)]; ring
        have hy0 : ∀ (s : TTState n) (a b : Fin n) (c : ℝ),
            (if 0 < s.2 a b then (s.2 a b : ℝ) / τ a b * c else 0) = (s.2 a b : ℝ) / τ a b * c := by
          intro s a b c
          split_ifs with h
          · rfl
          · have : s.2 a b = 0 := by omega
            simp [this]
        have F1 : ∀ a b, ∑ s ∈ ttStates n m, π s * (φ a b * q s a b) =
            ∑ s ∈ ttStates n m, π s * ((s.2 a b : ℝ) / τ a b) := by
          intro a b
          have h := htest (fun t => (t.2 a b : ℝ))
          rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← h]
          refine Finset.sum_congr rfl fun s hs => ?_
          rw [hgen _ s hs, ← mul_sub]
          congr 1
          have hterm : ∀ i j, ((if 0 < s.1 i then φ i j * q s i j *
                  (((s.2 + linkUnit i j) a b : ℕ) - (s.2 a b : ℝ)) else 0) +
                (if 0 < s.2 i j then (s.2 i j : ℝ) / τ i j *
                  (((s.2 - linkUnit i j) a b : ℕ) - (s.2 a b : ℝ)) else 0)) =
                if i = a then (if j = b then φ a b * q s a b - (s.2 a b : ℝ) / τ a b else 0) else 0 := by
            intro i j
            by_cases hi : i = a
            · subst hi
              by_cases hj : j = b
              · subst hj
                have e1 : (((s.2 + linkUnit i j) i j : ℕ) : ℝ) - (s.2 i j : ℝ) = 1 := by
                  simp [linkUnit]
                rw [e1, mul_one, hq0 s hs]
                by_cases hy : 0 < s.2 i j
                · have e2 : (((s.2 - linkUnit i j) i j : ℕ) : ℝ) - (s.2 i j : ℝ) = -1 := by
                    simp only [Pi.sub_apply, linkUnit, and_self, if_true]
                    rw [Nat.cast_sub (by omega)]; simp
                  rw [e2, if_pos hy]; simp; ring
                · have : s.2 i j = 0 := by omega
                  simp [this]
              · have e1 : linkUnit i j i b = 0 := by simp [linkUnit, Ne.symm hj]
                simp [e1, hj]
            · have e1 : linkUnit i j a b = 0 := by simp [linkUnit, Ne.symm hi]
              simp [e1, hi]
          simp only at hterm ⊢
          rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j]
          simp
        have F2 : ∀ a, ∑ s ∈ ttStates n m, π s * ∑ j, φ a j * q s a j =
            ∑ s ∈ ttStates n m, π s * ∑ k, (s.2 k a : ℝ) / τ k a := by
          intro a
          have h := htest (fun t => (t.1 a : ℝ))
          rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← neg_eq_zero, ← Finset.sum_neg_distrib, ← h]
          refine Finset.sum_congr rfl fun s hs => ?_
          rw [hgen _ s hs, ← mul_sub, ← mul_neg]
          congr 1
          have hterm : ∀ i j, ((if 0 < s.1 i then φ i j * q s i j *
                  (((s.1 - Pi.single i 1 : Fin n → ℕ) a : ℕ) - (s.1 a : ℝ)) else 0) +
                (if 0 < s.2 i j then (s.2 i j : ℝ) / τ i j *
                  (((s.1 + Pi.single j 1 : Fin n → ℕ) a : ℕ) - (s.1 a : ℝ)) else 0)) =
                (if i = a then -(φ a j * q s a j) else 0) + (if j = a then (s.2 i a : ℝ) / τ i a else 0) := by
            intro i j
            congr 1
            · by_cases hi : i = a
              · subst hi
                rw [if_pos rfl]
                by_cases hx : 0 < s.1 i
                · rw [if_pos hx]
                  have e : (((s.1 - Pi.single i 1 : Fin n → ℕ) i : ℕ) : ℝ) - (s.1 i : ℝ) = -1 := by
                    simp only [Pi.sub_apply, Pi.single_eq_same]
                    rw [Nat.cast_sub (by omega)]; simp
                  rw [e]; ring
                · rw [if_neg hx, (hq s hs i j).2.2 (by omega)]; ring
              · have e : (((s.1 - Pi.single i 1 : Fin n → ℕ) a : ℕ) : ℝ) - (s.1 a : ℝ) = 0 := by
                  simp [Pi.single_apply, Ne.symm hi]
                simp [e, hi]
            · by_cases hj : j = a
              · subst hj
                rw [if_pos rfl, hy0]
                simp
              · have e : (((s.1 + Pi.single j 1 : Fin n → ℕ) a : ℕ) : ℝ) - (s.1 a : ℝ) = 0 := by
                  simp [Pi.single_apply, Ne.symm hj]
                simp [e, hj]
          simp only at hterm ⊢
          rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j]
          simp [Finset.sum_add_distrib]
          ring
        set qb : Fin n → Fin n → ℝ := fun a b => ∑ s ∈ ttStates n m, π s * q s a b with hqb
        have hqb0 : ∀ a b, 0 ≤ qb a b := fun a b =>
          Finset.sum_nonneg fun s hs => mul_nonneg (hπ0 s) (hq s hs a b).1
        have hqb1 : ∀ a b, qb a b ≤ 1 := by
          intro a b
          rw [← hπ1]
          exact Finset.sum_le_sum fun s hs => mul_le_of_le_one_right (hπ0 s) (hq s hs a b).2.1
        have hflow : ∀ a b, φ a b * qb a b = ∑ s ∈ ttStates n m, π s * ((s.2 a b : ℝ) / τ a b) := by
          intro a b
          rw [← F1, hqb, Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          ring
        have hbalq : IsBalanced φ qb := by
          intro a
          calc ∑ k, φ k a * qb k a = ∑ k, ∑ s ∈ ttStates n m, π s * ((s.2 k a : ℝ) / τ k a) :=
                Finset.sum_congr rfl fun k _ => hflow k a
            _ = ∑ s ∈ ttStates n m, π s * ∑ k, (s.2 k a : ℝ) / τ k a := by
                rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
            _ = ∑ s ∈ ttStates n m, π s * ∑ j, φ a j * q s a j := (F2 a).symm
            _ = ∑ j, φ a j * qb a j := by
                simp_rw [hqb, Finset.mul_sum]; rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => ?_
                ring
        have hrate : ∑ i, ∑ j, φ i j * τ i j * qb i j ≤ m := by
          have e : ∀ i j, φ i j * τ i j * qb i j = ∑ s ∈ ttStates n m, π s * (s.2 i j : ℝ) := by
            intro i j
            have := hflow i j
            have hτ' := (hτ i j).ne'
            calc φ i j * τ i j * qb i j = τ i j * (φ i j * qb i j) := by ring
              _ = _ := by
                rw [this, Finset.mul_sum]
                refine Finset.sum_congr rfl fun s _ => ?_
                field_simp
          simp_rw [e]
          have e2 : ∑ i, ∑ j, ∑ s ∈ ttStates n m, π s * (s.2 i j : ℝ) =
              ∑ s ∈ ttStates n m, π s * ∑ i, ∑ j, (s.2 i j : ℝ) := by
            simp_rw [Finset.mul_sum]
            symm
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
          rw [e2]
          calc ∑ s ∈ ttStates n m, π s * ∑ i, ∑ j, (s.2 i j : ℝ)
              ≤ ∑ s ∈ ttStates n m, π s * (m : ℝ) := by
                refine Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_left ?_ (hπ0 s)
                have := (hmem s).1 hs
                have h2 : ∑ i, ∑ j, s.2 i j ≤ m := by omega
                exact_mod_cast h2
            _ = m := by rw [← Finset.sum_mul, hπ1, one_mul]
        have hfeas : IsAlg2Feasible φ τ m qb := ⟨⟨fun i j => ⟨hqb0 i j, hqb1 i j⟩, hbalq⟩, hrate⟩
        refine le_trans ?_ (hopt.2 qb hfeas)
        unfold ttObj elevObj
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_le_sum fun j _ => ?_
        have hJ := (hR i j).le_map_sum (t := ttStates n m) (w := π) (p := fun s => q s i j)
          (fun s _ => hπ0 s) hπ1 (fun s hs => ⟨(hq s hs i j).1, (hq s hs i j).2.1⟩)
        simp only [smul_eq_mul] at hJ
        calc ∑ s ∈ ttStates n m, π s * (φ i j * rewardCurve I i j (q s i j))
            = φ i j * ∑ s ∈ ttStates n m, π s * rewardCurve I i j (q s i j) := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => ?_; ring
          _ ≤ φ i j * rewardCurve I i j (qb i j) := mul_le_mul_of_nonneg_left hJ (hφ i j)
      have hP2gen : ∀ (w : Fin n → Fin n → ℝ) (hw : ∀ i j, 0 ≤ w i j)
          (hW : ∑ i, ∑ j, w i j ≤ m * (1 - epsilon m)) (i0 : Fin n),
          (Real.sqrt (m * Real.log m) / (Real.sqrt (m * Real.log m) + n - 1) -
            3 / Real.sqrt (m * Real.log m)) *
          (∑ t ∈ ttStates n m, ∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) ≤
        ∑ t ∈ (ttStates n m).filter (fun s => 0 < s.1 i0),
          ∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ) := by
        intro w hw hW i0
        clear * - hm hw hW
        have hSt : ∀ t : TTState n, t ∈ ttStates n m ↔ (∑ i, t.1 i) + ∑ i, ∑ j, t.2 i j = m := by
          intro t
          unfold ttStates
          rw [mem_filter, mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset]
          constructor
          · exact fun h => h.2
          · intro h
            refine ⟨⟨fun i => ?_, fun i => Fintype.mem_piFinset.2 fun j => ?_⟩, h⟩
            · rw [mem_range]; have := single_le_sum (fun i _ => Nat.zero_le (t.1 i)) (mem_univ i); omega
            · rw [mem_range]; have h1 := single_le_sum (fun j _ => Nat.zero_le (t.2 i j)) (mem_univ j)
              have h2 := single_le_sum (fun i _ => Nat.zero_le (∑ j, t.2 i j)) (mem_univ i); omega
        obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (m * Real.log m) := ⟨_, rfl⟩
        rw [← hs]
        have hm' : (100:ℝ) ≤ m := by exact_mod_cast hm
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
          obtain ⟨K, hK⟩ : ∃ K, K = ⌊(m:ℝ) - s⌋₊ + 1 := ⟨_, rfl⟩
          rw [← hK]
          have hs1 : 10 ≤ s := le_trans hsqm hs_ge
          have hms0 : 0 ≤ (m:ℝ) - s := by linarith only [h2s, hs1]
          have hKgt : (m:ℝ) - s < K := by rw [hK, Nat.cast_add, Nat.cast_one]; exact Nat.lt_floor_add_one _
          have hKle : (K:ℝ) ≤ m - s + 1 := by
            rw [hK, Nat.cast_add, Nat.cast_one]; linarith only [Nat.floor_le hms0]
          have hKm : K ≤ m := by
            have : (K:ℝ) ≤ m := by linarith only [hKle, hs1]
            exact_mod_cast this
          obtain ⟨J, hJ⟩ : ∃ J, J = ⌊s⌋₊ := ⟨_, rfl⟩
          have hJs : (J:ℝ) ≤ s := by rw [hJ]; exact Nat.floor_le (by linarith only [hs1])
          have hJs' : s < J + 1 := by rw [hJ]; exact Nat.lt_floor_add_one _
          have hJK : J ≤ K := by
            have : (J:ℝ) ≤ K := by linarith only [hJs, hKgt, h2s]
            exact_mod_cast this
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
            have hj' : (j:ℝ) + 1 ≤ J := by exact_mod_cast hj
            have hj0 : (0:ℝ) ≤ j := j.cast_nonneg
            have hA : 0 < (m:ℝ) - s - j := by linarith only [hj', hJs, h2s]
            have hx : 0 < ((m:ℝ) - s - j) / ((m:ℝ) - 2 * s) := div_pos hA hVpos
            have hlogx := Real.one_sub_inv_le_log_of_pos hx
            have e1 : 1 - (((m:ℝ) - s - j) / ((m:ℝ) - 2 * s))⁻¹ = (s - j) / (m - s - j) := by
              rw [inv_div, eq_div_iff hA.ne', sub_mul, div_mul_cancel₀ _ hA.ne']; ring
            have e2 : (s - j) / m ≤ (s - j) / (m - s - j) :=
              div_le_div_of_nonneg_left (by linarith only [hj', hJs]) hA (by linarith only [hs1, hj0])
            have e3 : Real.exp ((s - j) / m) ≤ ((m:ℝ) - s - j) / ((m:ℝ) - 2 * s) := by
              rw [← Real.exp_log hx]; exact Real.exp_le_exp.2 (by linarith only [hlogx, e1, e2])
            exact le_trans e3 (div_le_div_of_nonneg_right (by linarith only [hKgt]) hVpos.le)
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
            have hl' : (l:ℝ) + 1 ≤ L := by exact_mod_cast hl
            have hl0 : (0:ℝ) ≤ l := l.cast_nonneg
            have hlJ' : (l:ℝ) ≤ J := by exact_mod_cast hlJ
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

        have hstein : ∀ (a b : Fin n) (k : ℕ), 1 ≤ k →
            ∑ t ∈ (ttStates n m).filter (fun t => ∑ i, ∑ j, t.2 i j = k), (t.2 a b : ℝ) * (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) ≤
            w a b * ∑ t ∈ (ttStates n m).filter (fun t => ∑ i, ∑ j, t.2 i j = k - 1), (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) := by
          intro a b k hk
          set ν : TTState n → ℝ := fun t => ∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ) with hν
          have hν0 : ∀ t, 0 ≤ ν t := fun t => prod_nonneg fun i _ => prod_nonneg fun j _ =>
            div_nonneg (pow_nonneg (hw i j) _) (Nat.cast_nonneg _)
          set S1 := (ttStates n m).filter (fun t => ∑ i, ∑ j, t.2 i j = k) with hS1
          set S0 := (ttStates n m).filter (fun t => ∑ i, ∑ j, t.2 i j = k - 1) with hS0
          let g : TTState n → TTState n := fun t =>
            (fun c => t.1 c + if c = i0 then 1 else 0,
             fun c d => if c = a ∧ d = b then t.2 c d - 1 else t.2 c d)
          have hgY : ∀ t : TTState n, 1 ≤ t.2 a b →
              (∑ i, ∑ j, (g t).2 i j) + 1 = ∑ i, ∑ j, t.2 i j := by
            intro t ht
            have hpt : ∀ c d, t.2 c d = (g t).2 c d + (if c = a ∧ d = b then 1 else 0) := by
              intro c d
              show t.2 c d = (if c = a ∧ d = b then t.2 c d - 1 else t.2 c d) + (if c = a ∧ d = b then 1 else 0)
              split_ifs with h
              · obtain ⟨rfl, rfl⟩ := h; omega
              · rfl
            rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => hpt c d]
            simp only [sum_add_distrib]
            congr 1
            rw [sum_eq_single a (fun c _ hc => sum_eq_zero fun d _ => if_neg (fun h => hc h.1))
                (fun h => absurd (mem_univ a) h),
              sum_eq_single b (fun d _ hd => if_neg (fun h => hd h.2)) (fun h => absurd (mem_univ b) h),
              if_pos ⟨rfl, rfl⟩]
          have hgX : ∀ t : TTState n, ∑ i, (g t).1 i = (∑ i, t.1 i) + 1 := by
            intro t
            show ∑ i, (t.1 i + if i = i0 then 1 else 0) = _
            rw [sum_add_distrib, sum_ite_eq' univ i0, if_pos (mem_univ _)]
          have hgmem : ∀ t ∈ S1.filter (fun t => 1 ≤ t.2 a b), g t ∈ S0 := by
            intro t ht
            rw [mem_filter, hS1, mem_filter, hSt] at ht
            rw [hS0, mem_filter, hSt]
            have h1 := hgY t ht.2
            have h2 := hgX t
            constructor <;> omega
          have hginj : Set.InjOn g (S1.filter (fun t => 1 ≤ t.2 a b)) := by
            intro t ht t' ht' h
            rw [coe_filter] at ht ht'
            have h1 := congrArg Prod.fst h
            have h2 := congrArg Prod.snd h
            ext c
            · have := congrFun h1 c; simp only [g] at this; omega
            · rename_i d
              have := congrFun (congrFun h2 c) d; simp only [g] at this
              split_ifs at this with hcd
              · obtain ⟨rfl, rfl⟩ := hcd; have := ht.2; have := ht'.2; omega
              · exact this
          have hval : ∀ t : TTState n, 1 ≤ t.2 a b → (t.2 a b : ℝ) * ν t = w a b * ν (g t) := by
            intro t ht
            simp only [hν]
            rw [← Fintype.prod_prod_type' (fun i j => w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)),
              ← Fintype.prod_prod_type' (fun i j => w i j ^ ((g t).2 i j) / (((g t).2 i j).factorial : ℝ)),
              Fintype.prod_eq_mul_prod_compl (a, b), Fintype.prod_eq_mul_prod_compl (a, b)]
            have hrest : ∏ x ∈ ({(a, b)}ᶜ : Finset (Fin n × Fin n)),
                w x.1 x.2 ^ (t.2 x.1 x.2) / ((t.2 x.1 x.2).factorial : ℝ) =
                ∏ x ∈ ({(a, b)}ᶜ : Finset (Fin n × Fin n)),
                w x.1 x.2 ^ ((g t).2 x.1 x.2) / (((g t).2 x.1 x.2).factorial : ℝ) := by
              refine prod_congr rfl fun x hx => ?_
              have hx' : ¬ (x.1 = a ∧ x.2 = b) := by
                rintro ⟨h1, h2⟩; apply (mem_compl.1 hx); rw [mem_singleton]; exact Prod.ext h1 h2
              simp only [g, if_neg hx']
            rw [hrest, ← mul_assoc, ← mul_assoc]
            congr 1
            show (t.2 a b : ℝ) * (w a b ^ (t.2 a b) / ((t.2 a b).factorial : ℝ)) =
              w a b * (w a b ^ (if a = a ∧ b = b then t.2 a b - 1 else t.2 a b) /
                (((if a = a ∧ b = b then t.2 a b - 1 else t.2 a b)).factorial : ℝ))
            rw [if_pos ⟨rfl, rfl⟩]
            obtain ⟨r, hr⟩ : ∃ r, t.2 a b = r + 1 := ⟨t.2 a b - 1, by omega⟩
            rw [hr, Nat.add_sub_cancel, Nat.factorial_succ, pow_succ, Nat.cast_mul]
            have hr1 : ((r+1 : ℕ):ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero r)
            rw [mul_div_assoc', mul_div_mul_left _ _ hr1, mul_comm (w a b ^ r) (w a b), mul_div_assoc]
          calc ∑ t ∈ S1, (t.2 a b : ℝ) * ν t
              = ∑ t ∈ S1.filter (fun t => 1 ≤ t.2 a b), (t.2 a b : ℝ) * ν t := by
                refine (sum_filter_of_ne fun t _ h => ?_).symm
                by_contra h'; apply h; rw [show t.2 a b = 0 by omega, Nat.cast_zero, zero_mul]
            _ = ∑ t ∈ S1.filter (fun t => 1 ≤ t.2 a b), w a b * ν (g t) := by
                apply sum_congr rfl; intro t ht; exact hval t (mem_filter.1 ht).2
            _ = w a b * ∑ t ∈ (S1.filter (fun t => 1 ≤ t.2 a b)).image g, ν t := by
                rw [← mul_sum, sum_image hginj]
            _ ≤ w a b * ∑ t ∈ S0, ν t := by
                apply mul_le_mul_of_nonneg_left _ (hw a b)
                apply sum_le_sum_of_subset_of_nonneg
                · intro u hu; obtain ⟨t, ht, rfl⟩ := mem_image.1 hu; exact hgmem t ht
                · intro i _ _; exact hν0 i

        have hbij : ∀ j : Fin n, j ≠ i0 →
            ∑ t ∈ (ttStates n m).filter (fun t => ¬ 0 < t.1 i0), (t.1 j : ℝ) * (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) =
            ∑ t ∈ (ttStates n m).filter (fun t => 0 < t.1 i0), (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) := by
          intro j hj
          have hsum2 : ∀ f g : Fin n → ℕ, (∀ c, c ≠ i0 → c ≠ j → f c = g c) →
              f i0 + f j = g i0 + g j → ∑ c, f c = ∑ c, g c := by
            intro f g hfg h2
            have hjm : j ∈ univ.erase i0 := mem_erase.2 ⟨hj, mem_univ j⟩
            rw [← add_sum_erase univ f (mem_univ i0), ← add_sum_erase _ f hjm,
              ← add_sum_erase univ g (mem_univ i0), ← add_sum_erase _ g hjm]
            have : ∑ c ∈ (univ.erase i0).erase j, f c = ∑ c ∈ (univ.erase i0).erase j, g c :=
              sum_congr rfl fun c hc => hfg c (mem_erase.1 (mem_erase.1 hc).2).1 (mem_erase.1 hc).1
            omega
          set D := (ttStates n m).filter (fun t => ¬ 0 < t.1 i0) with hD
          set P := (ttStates n m).filter (fun t => 0 < t.1 i0) with hP
          have e1 : ∑ t ∈ D, (t.1 j : ℝ) * (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) = ∑ u ∈ D.sigma (fun t => range (t.1 j)), (∏ i, ∏ j, w i j ^ (u.1.2 i j) / ((u.1.2 i j).factorial : ℝ)) := by
            rw [sum_sigma]
            refine sum_congr rfl fun t _ => ?_
            show _ = ∑ s ∈ range (t.1 j), (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ))
            rw [sum_const, card_range, nsmul_eq_mul]
          rw [e1]
          refine sum_nbij'
            (fun u => ((fun a => if a = i0 then u.2 + 1 else if a = j then u.1.1 j - (u.2 + 1) else u.1.1 a),
              u.1.2))
            (fun v => ⟨((fun a => if a = i0 then 0 else if a = j then v.1 j + v.1 i0 else v.1 a), v.2),
              v.1 i0 - 1⟩) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
          · intro u hu
            rw [mem_sigma, hD, mem_filter, hSt, mem_range] at hu
            rw [hP, mem_filter, hSt]
            refine ⟨?_, by simp only [eq_self_iff_true, if_true]; exact Nat.succ_pos _⟩
            rw [← hu.1.1]; congr 1
            apply hsum2
            · intro c h1 h2; simp only [if_neg h1, if_neg h2]
            · simp only [if_neg hj, eq_self_iff_true, if_true]; omega
          · intro v hv
            rw [hP, mem_filter, hSt] at hv
            rw [mem_sigma, hD, mem_filter, hSt, mem_range]
            refine ⟨⟨?_, by simp only [eq_self_iff_true, if_true]; exact lt_irrefl 0⟩, by simp only [if_neg hj, eq_self_iff_true, if_true]; omega⟩
            rw [← hv.1]; congr 1
            apply hsum2
            · intro c h1 h2; simp only [if_neg h1, if_neg h2]
            · simp only [if_neg hj, eq_self_iff_true, if_true]; omega
          · intro u hu
            rw [mem_sigma, hD, mem_filter, mem_range] at hu
            obtain ⟨⟨x, y⟩, c⟩ := u
            simp only at hu ⊢
            rw [Sigma.mk.inj_iff]
            refine ⟨?_, heq_of_eq (by simp only [eq_self_iff_true, if_true, Nat.add_sub_cancel])⟩
            congr 1
            funext a
            by_cases h1 : a = i0
            · subst h1; simp only [eq_self_iff_true, if_true]; omega
            · by_cases h2 : a = j
              · subst h2; simp only [if_neg hj, if_neg (Ne.symm hj), eq_self_iff_true, if_true]; omega
              · simp only [if_neg h1, if_neg h2]
          · intro v hv
            rw [hP, mem_filter] at hv
            obtain ⟨x, y⟩ := v
            simp only at hv ⊢
            congr 1
            funext a
            by_cases h1 : a = i0
            · subst h1; simp only [eq_self_iff_true, if_true]; omega
            · by_cases h2 : a = j
              · subst h2; simp only [if_neg hj, if_neg (Ne.symm hj), eq_self_iff_true, if_true]; omega
              · simp only [if_neg h1, if_neg h2]

        have hn : 1 ≤ n := Fin.pos i0
        have hν0 : ∀ t : TTState n, 0 ≤ (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) := fun t => prod_nonneg fun i _ => prod_nonneg fun j _ =>
          div_nonneg (pow_nonneg (hw i j) _) (Nat.cast_nonneg _)
        obtain ⟨p, hp⟩ : ∃ p : ℕ → ℝ, ∀ k, p k =
            ∑ t ∈ (ttStates n m).filter (fun t => ∑ i, ∑ j, t.2 i j = k), (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) := ⟨_, fun k => rfl⟩
        have hp0 : ∀ k, 0 ≤ p k := fun k => by rw [hp]; exact sum_nonneg fun t _ => hν0 t
        have hZ : ∑ t ∈ ttStates n m, (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) = ∑ k ∈ range (m + 1), p k := by
          simp only [hp]
          refine (sum_fiberwise_of_maps_to (fun t ht => ?_) _).symm
          rw [hSt] at ht; rw [mem_range]; omega
        have hlog0 : 0 ≤ Real.log m := by linarith only [hlog1]
        have heps : (m:ℝ) * (1 - epsilon m) = m - 2 * s := by
          unfold epsilon
          have : s = m * Real.sqrt (Real.log m / m) := by
            rw [hs, show (m:ℝ) * Real.log m = (m * m) * (Real.log m / m) by field_simp,
              Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self hmpos.le]
          rw [this]; ring
        have hstp : ∀ k : ℕ, 1 ≤ k → (k:ℝ) * p k ≤ ((m:ℝ) - 2 * s) * p (k-1) := by
          intro k hk
          have e1 : (k:ℝ) * p k = ∑ a, ∑ b, ∑ t ∈ (ttStates n m).filter
              (fun t => ∑ i, ∑ j, t.2 i j = k), (t.2 a b : ℝ) * (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) := by
            rw [hp, mul_sum]
            have hh : ∀ t ∈ (ttStates n m).filter (fun t => ∑ i, ∑ j, t.2 i j = k),
                (k:ℝ) * (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) = ∑ a, ∑ b, (t.2 a b : ℝ) * (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) := by
              intro t ht
              have h := (mem_filter.1 ht).2
              have h' : ((∑ i, ∑ j, t.2 i j : ℕ) : ℝ) = k := by rw [h]
              simp only [Nat.cast_sum] at h'
              rw [← h', sum_mul]
              exact sum_congr rfl fun a _ => sum_mul _ _ _
            rw [sum_congr rfl hh, sum_comm]
            exact sum_congr rfl fun a _ => sum_comm
          have e2 : ∑ a, ∑ b, ∑ t ∈ (ttStates n m).filter
              (fun t => ∑ i, ∑ j, t.2 i j = k), (t.2 a b : ℝ) * (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) ≤
              ∑ a, ∑ b, w a b * p (k - 1) :=
            sum_le_sum fun a _ => sum_le_sum fun b _ => by rw [hp]; exact hstein a b k hk
          have e3 : ∑ a, ∑ b, w a b * p (k - 1) = (∑ a, ∑ b, w a b) * p (k-1) := by
            rw [sum_mul]; exact sum_congr rfl fun a _ => (sum_mul _ _ _).symm
          have e4 : (∑ a, ∑ b, w a b) * p (k-1) ≤ ((m:ℝ) - 2 * s) * p (k-1) :=
            mul_le_mul_of_nonneg_right (heps ▸ hW) (hp0 _)
          linarith only [e1, e2, e3, e4]
        have hS := hseq p hp0 hstp
        set K := ⌊(m:ℝ) - s⌋₊ + 1 with hK
        have hKm : K ≤ m := by
          have h1 : (K:ℝ) ≤ m - s + 1 := by
            rw [hK, Nat.cast_add, Nat.cast_one]; linarith only [Nat.floor_le hms0]
          have : (K:ℝ) ≤ m := by linarith only [h1, hs1]
          exact_mod_cast this
        have hcond : ∀ t ∈ ttStates n m,
            ((((∑ i, t.1 i : ℕ)) : ℝ) < s ↔ K ≤ ∑ i, ∑ j, t.2 i j) := by
          intro t ht
          rw [hSt] at ht
          have hc : ((∑ i, t.1 i : ℕ) : ℝ) = m - ((∑ i, ∑ j, t.2 i j : ℕ) : ℝ) := by
            rw [← ht, Nat.cast_add]; ring
          rw [hc, hK, Nat.add_one_le_iff, Nat.floor_lt hms0]
          constructor <;> intro h <;> linarith only [h]
        set Tm := ∑ t ∈ ttStates n m,
          (if (((∑ i, t.1 i : ℕ)) : ℝ) < s then (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) else 0) with hTm
        have hTm1 : Tm = ∑ k ∈ range (m + 1), (if K ≤ k then p k else 0) := by
          rw [hTm, ← sum_fiberwise_of_maps_to (g := fun t => ∑ i, ∑ j, t.2 i j) (t := range (m+1))
            (fun t ht => by rw [hSt] at ht; rw [mem_range]; omega)]
          refine sum_congr rfl fun k _ => ?_
          rw [hp]
          by_cases hKk : K ≤ k
          · rw [if_pos hKk]; refine sum_congr rfl fun t ht => ?_
            rw [mem_filter] at ht; rw [if_pos ((hcond t ht.1).2 (ht.2 ▸ hKk))]
          · rw [if_neg hKk]; refine sum_eq_zero fun t ht => ?_
            rw [mem_filter] at ht; rw [if_neg (fun h => hKk (ht.2 ▸ (hcond t ht.1).1 h))]
        have hgen : ∀ N, ∑ k ∈ range (K + N), (if K ≤ k then p k else 0) = ∑ i ∈ range N, p (K + i) := by
          intro N
          rw [sum_range_add, sum_eq_zero (fun k hk => if_neg (by rw [mem_range] at hk; omega)), zero_add]
          exact sum_congr rfl fun i _ => if_pos (by omega)
        have hTm2 := hgen (m + 1 - K)
        rw [Nat.add_sub_cancel' (by omega : K ≤ m + 1)] at hTm2
        have hsT : s * Tm ≤ 3 * ∑ t ∈ ttStates n m, (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) := by
          rw [hTm1, hTm2, hZ]; exact hS
        set SP := ∑ t ∈ (ttStates n m).filter (fun s => 0 < s.1 i0), (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) with hSP
        set SD := ∑ t ∈ (ttStates n m).filter (fun t => ¬ 0 < t.1 i0), (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) with hSD
        have hZsplit : ∑ t ∈ ttStates n m, (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) = SP + SD := (sum_filter_add_sum_filter_not _ _ _).symm
        have hEMD : ∑ t ∈ (ttStates n m).filter (fun t => ¬ 0 < t.1 i0),
            (((∑ c, t.1 c : ℕ)) : ℝ) * (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) = ((n:ℝ) - 1) * SP := by
          have h1 : ∀ t : TTState n, (((∑ c, t.1 c : ℕ)) : ℝ) * (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) = ∑ c, (t.1 c : ℝ) * (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) :=
            fun t => by rw [Nat.cast_sum, sum_mul]
          rw [sum_congr rfl fun t _ => h1 t, sum_comm, ← add_sum_erase univ _ (mem_univ i0)]
          have h0 : ∑ t ∈ (ttStates n m).filter (fun t => ¬ 0 < t.1 i0), (t.1 i0 : ℝ) * (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) = 0 :=
            sum_eq_zero fun t ht => by
              rw [mem_filter] at ht; rw [show t.1 i0 = 0 by omega, Nat.cast_zero, zero_mul]
          rw [h0, zero_add, sum_congr rfl fun j hj => hbij j (mem_erase.1 hj).1, sum_const,
            card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, nsmul_eq_mul,
            Nat.cast_sub hn, Nat.cast_one]
        have hpt : ∀ t : TTState n, s * (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) - s * (if (((∑ i, t.1 i : ℕ)) : ℝ) < s then (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) else 0) ≤
            (((∑ i, t.1 i : ℕ)) : ℝ) * (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) := by
          intro t
          have := hν0 t
          split_ifs with h
          · rw [sub_self]; exact mul_nonneg (Nat.cast_nonneg _) this
          · rw [mul_zero, sub_zero]; exact mul_le_mul_of_nonneg_right (le_of_not_gt h) this
        have hD1 : s * SD - s * ∑ t ∈ (ttStates n m).filter (fun t => ¬ 0 < t.1 i0),
            (if (((∑ i, t.1 i : ℕ)) : ℝ) < s then (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) else 0) ≤ ((n:ℝ) - 1) * SP := by
          rw [← hEMD, hSD, mul_sum, mul_sum, ← sum_sub_distrib]; exact sum_le_sum fun t _ => hpt t
        have hD2 : ∑ t ∈ (ttStates n m).filter (fun t => ¬ 0 < t.1 i0),
            (if (((∑ i, t.1 i : ℕ)) : ℝ) < s then (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) else 0) ≤ Tm :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun t _ _ => by
            split_ifs
            · exact hν0 t
            · exact le_rfl)
        have hD3 := mul_le_mul_of_nonneg_left hD2 hs0
        set Z := ∑ t ∈ ttStates n m, (∏ i, ∏ j, w i j ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) with hZdef
        have hZ0 : 0 ≤ Z := sum_nonneg fun t _ => hν0 t
        have hZs : s * Z = s * SP + s * SD := by rw [hZsplit]; ring
        have hspos : 0 < s := by linarith only [hs1]
        have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
        have hDd : 0 < s + (n:ℝ) - 1 := by linarith only [hspos, hn']
        have k1 : s * Z - 3 * Z ≤ (s + (n:ℝ) - 1) * SP := by linarith only [hD1, hD3, hsT, hZs]
        have k2 : s * Z / (s + (n:ℝ) - 1) - 3 * Z / (s + (n:ℝ) - 1) ≤ SP := by
          rw [← sub_div, div_le_iff₀ hDd]; linarith only [k1]
        have k3 : 3 * Z / (s + (n:ℝ) - 1) ≤ 3 * Z / s :=
          div_le_div_of_nonneg_left (by linarith only [hZ0]) hspos (by linarith only [hn'])
        have k4 : (s / (s + (n:ℝ) - 1) - 3 / s) * Z = s * Z / (s + (n:ℝ) - 1) - 3 * Z / s := by ring
        rw [k4]; linarith only [k2, k3]
      rcases hconn with hconn | hzero
      swap
      · -- qt = 0
        have hq'0 := hqt0 hzero
        have hE' : elevObj φ I q' = 0 := by simp [elevObj, hq'0, hR0]
        have hR' : ttObj n m φ I (toTTPolicy qt) πt = 0 := by
          simp [ttObj, hzero, toTTPolicy, toPolicy, hR0]
        rw [hR', max_eq_right (by linarith)]; simp
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        have hempty : ttStates 0 m = ∅ := by
          unfold ttStates; rw [Finset.filter_eq_empty_iff]; intro s _; simp; omega
        simp [ttObj, hempty]
      obtain ⟨i0, -⟩ : ∃ i0 : Fin n, True := ⟨⟨0, hn⟩, trivial⟩
      have hE : ttObj n m φ I (toTTPolicy qt) πt =
          (∑ s ∈ (ttStates n m).filter (fun s => 0 < s.1 i0), πt s) * elevObj φ I qt := by
        have hbal := hqtbal
        clear * - hφ hτ hqt01 hbal hconn hπt hgenG htestG
        set St := ttStates n m with hSt
        set Q := toTTPolicy qt with hQ
        have hgen := hgenG Q
        have htest := htestG Q πt hπt
        -- availabilities and mean link occupancies
        set A : Fin n → ℝ := fun a => ∑ s ∈ St, if 0 < s.1 a then πt s else 0 with hAdef
        set Ey : Fin n → Fin n → ℝ := fun a b => ∑ s ∈ St, πt s * (s.2 a b : ℝ) with hEy
        have hQ' : ∀ s i j, Q s i j = if 0 < s.1 i then qt i j else 0 := fun s i j => rfl
        have hcollapse : ∀ (a b : Fin n) (F : Fin n → Fin n → ℝ),
            (∑ i, ∑ j, F i j * (linkUnit i j a b : ℝ)) = F a b := by
          intro a b F
          rw [Finset.sum_eq_single a]
          · rw [Finset.sum_eq_single b]
            · simp [linkUnit]
            · intro j _ hj; simp [linkUnit, Ne.symm hj]
            · simp
          · intro i _ hi
            exact Finset.sum_eq_zero fun j _ => by simp [linkUnit, Ne.symm hi]
          · simp
        -- link identity
        have hlink : ∀ a b, φ a b * qt a b * A a = Ey a b / τ a b := by
          intro a b
          have h := htest (fun t => (t.2 a b : ℝ))
          have hs : ∀ s ∈ St, (∑ t ∈ St, ttRate φ τ Q s t * ((t.2 a b : ℝ) - (s.2 a b : ℝ))) =
              (if 0 < s.1 a then φ a b * qt a b else 0) - (s.2 a b : ℝ) / τ a b := by
            intro s hs
            rw [hgen _ s hs]
            have : ∀ i j, ((if 0 < s.1 i then φ i j * Q s i j *
                  (((s.2 + linkUnit i j) a b : ℕ) - (s.2 a b : ℝ)) else 0) +
                (if 0 < s.2 i j then (s.2 i j : ℝ) / τ i j *
                  (((s.2 - linkUnit i j) a b : ℕ) - (s.2 a b : ℝ)) else 0)) =
                ((if 0 < s.1 i then φ i j * qt i j else 0) - (s.2 i j : ℝ) / τ i j) *
                  (linkUnit i j a b : ℝ) := by
              intro i j
              have e1 : (((s.2 + linkUnit i j) a b : ℕ) : ℝ) - (s.2 a b : ℝ) = (linkUnit i j a b : ℝ) := by
                simp only [Pi.add_apply]; push_cast; ring
              rw [e1, hQ']
              by_cases hy : 0 < s.2 i j
              · have e2 : (((s.2 - linkUnit i j) a b : ℕ) : ℝ) - (s.2 a b : ℝ) =
                    -(linkUnit i j a b : ℝ) := by
                  simp only [Pi.sub_apply, linkUnit]
                  split_ifs with h
                  · obtain ⟨rfl, rfl⟩ := h
                    rw [Nat.cast_sub (by omega)]; push_cast; ring
                  · simp
                rw [e2]; by_cases hx : 0 < s.1 i <;> simp [hx, hy] <;> ring
              · have hy0 : s.2 i j = 0 := by omega
                by_cases hx : 0 < s.1 i <;> simp [hx, hy, hy0]
            simp only at this ⊢
            rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => this i j, hcollapse]
          rw [Finset.sum_congr rfl fun s hs' => by rw [hs s hs']] at h
          simp only [mul_sub, Finset.sum_sub_distrib] at h
          have h1 : (∑ s ∈ St, πt s * (if 0 < s.1 a then φ a b * qt a b else 0)) =
              φ a b * qt a b * A a := by
            rw [hAdef, Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_; split_ifs <;> ring
          have h2 : (∑ s ∈ St, πt s * ((s.2 a b : ℝ) / τ a b)) = Ey a b / τ a b := by
            rw [hEy, Finset.sum_div]
            refine Finset.sum_congr rfl fun s _ => ?_; ring
          linarith

        -- node identity
        have hnode : ∀ a, A a * (∑ j, φ a j * qt a j) = ∑ i, Ey i a / τ i a := by
          intro a
          have h := htest (fun t => (t.1 a : ℝ))
          have hs : ∀ s ∈ St, (∑ t ∈ St, ttRate φ τ Q s t * ((t.1 a : ℝ) - (s.1 a : ℝ))) =
              (∑ i, (s.2 i a : ℝ) / τ i a) - ∑ j, φ a j * Q s a j := by
            intro s hs
            rw [hgen _ s hs]
            have : ∀ i j, ((if 0 < s.1 i then φ i j * Q s i j *
                  (((s.1 - Pi.single i 1 : Fin n → ℕ) a : ℕ) - (s.1 a : ℝ)) else 0) +
                (if 0 < s.2 i j then (s.2 i j : ℝ) / τ i j *
                  (((s.1 + Pi.single j 1 : Fin n → ℕ) a : ℕ) - (s.1 a : ℝ)) else 0)) =
                (s.2 i j : ℝ) / τ i j * ((Pi.single j (1:ℝ) : Fin n → ℝ) a) -
                  φ i j * Q s i j * ((Pi.single i (1:ℝ) : Fin n → ℝ) a) := by
              intro i j
              have e1 : (((s.1 + Pi.single j 1 : Fin n → ℕ) a : ℕ) : ℝ) - (s.1 a : ℝ) =
                  (Pi.single j (1:ℝ) : Fin n → ℝ) a := by
                rw [Pi.add_apply, Nat.cast_add, add_sub_cancel_left, Pi.single_apply, Pi.single_apply]
                split_ifs <;> simp
              have hB : (if 0 < s.2 i j then (s.2 i j : ℝ) / τ i j *
                  (((s.1 + Pi.single j 1 : Fin n → ℕ) a : ℕ) - (s.1 a : ℝ)) else 0) =
                  (s.2 i j : ℝ) / τ i j * ((Pi.single j (1:ℝ) : Fin n → ℝ) a) := by
                rw [e1]
                by_cases hy : 0 < s.2 i j
                · rw [if_pos hy]
                · rw [if_neg hy, show s.2 i j = 0 by omega]; simp
              have hA' : (if 0 < s.1 i then φ i j * Q s i j *
                  (((s.1 - Pi.single i 1 : Fin n → ℕ) a : ℕ) - (s.1 a : ℝ)) else 0) =
                  -(φ i j * Q s i j * ((Pi.single i (1:ℝ) : Fin n → ℝ) a)) := by
                by_cases hx : 0 < s.1 i
                · rw [if_pos hx]
                  have e2 : (((s.1 - Pi.single i 1 : Fin n → ℕ) a : ℕ) : ℝ) - (s.1 a : ℝ) =
                      -((Pi.single i (1:ℝ) : Fin n → ℝ) a) := by
                    rw [Pi.sub_apply, Pi.single_apply, Pi.single_apply]
                    by_cases hia : a = i
                    · subst hia; rw [if_pos rfl, if_pos rfl, Nat.cast_sub (by omega)]; push_cast; ring
                    · rw [if_neg hia, if_neg hia]; simp
                  rw [e2]; ring
                · rw [if_neg hx, hQ', if_neg hx]; ring
              rw [hA', hB]; ring
            rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => this i j]
            simp only [Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero]
            congr 1
            · exact Finset.sum_congr rfl fun x _ => by
                rw [Finset.sum_ite_eq]; exact if_pos (Finset.mem_univ _)
            · rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun j _ => by
                rw [Finset.sum_ite_eq]; exact if_pos (Finset.mem_univ _)
          rw [Finset.sum_congr rfl fun s hs' => by rw [hs s hs']] at h
          simp only [mul_sub, Finset.sum_sub_distrib] at h
          have h1 : (∑ s ∈ St, πt s * ∑ j, φ a j * Q s a j) =
              A a * (∑ j, φ a j * qt a j) := by
            rw [hAdef, Finset.sum_mul]
            refine Finset.sum_congr rfl fun s _ => ?_
            simp only [hQ']
            split_ifs <;> simp
          have h2 : (∑ s ∈ St, πt s * ∑ i, (s.2 i a : ℝ) / τ i a) = ∑ i, Ey i a / τ i a := by
            simp only [hEy, Finset.sum_div, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => ?_; ring
          linarith
        have hflow : ∀ a, A a * (∑ k, φ k a * qt k a) = ∑ k, φ k a * qt k a * A k := by
          intro a
          rw [hbal a, hnode a]
          exact Finset.sum_congr rfl fun k _ => (hlink k a).symm
        have hlam : ∀ i j, 0 ≤ φ i j * qt i j := fun i j => mul_nonneg (hφ i j) (hqt01 i j).1
        -- max principle
        obtain ⟨b, -, hb⟩ := Finset.exists_max_image Finset.univ A ⟨i0, Finset.mem_univ _⟩
        have hclosed : ∀ c k, A c = A b → 0 < φ k c * qt k c → A k = A b := by
          intro c k hc hkc
          have hsum : (∑ k', φ k' c * qt k' c * (A b - A k')) = 0 := by
            have : (∑ k', φ k' c * qt k' c * (A b - A k')) =
                A b * (∑ k', φ k' c * qt k' c) - ∑ k', φ k' c * qt k' c * A k' := by
              rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl fun k' _ => by ring
            rw [this, ← hflow c, hc, sub_self]
          have hnn : ∀ k' ∈ Finset.univ, 0 ≤ φ k' c * qt k' c * (A b - A k') := fun k' _ =>
            mul_nonneg (hlam k' c) (sub_nonneg.2 (hb k' (Finset.mem_univ _)))
          have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum k (Finset.mem_univ _)
          rcases mul_eq_zero.1 this with h | h
          · exact absurd h hkc.ne'
          · linarith
        have hconst : ∀ a, A a = A b := by
          intro a
          have hp := hconn a b
          induction hp using Relation.ReflTransGen.head_induction_on with
          | refl => rfl
          | head hac _ ih => exact hclosed _ _ ih hac.2
        -- objective
        have hR0 : ∀ i j, rewardCurve I i j 0 = 0 := fun i j => by simp [rewardCurve]
        have hobj : ttObj n m φ I Q πt = ∑ i, A i * ∑ j, φ i j * rewardCurve I i j (qt i j) := by
          unfold ttObj
          have : ∀ s, πt s * ∑ i, ∑ j, φ i j * rewardCurve I i j (Q s i j) =
              ∑ i, (if 0 < s.1 i then πt s else 0) * ∑ j, φ i j * rewardCurve I i j (qt i j) := by
            intro s
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            by_cases hx : 0 < s.1 i
            · simp only [hQ', if_pos hx]
            · simp only [hQ', if_neg hx, hR0, mul_zero, Finset.sum_const_zero, zero_mul]
          rw [Finset.sum_congr rfl fun s _ => this s, Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_mul]
        have hA0 : A i0 = ∑ s ∈ St.filter (fun s => 0 < s.1 i0), πt s := by
          rw [hAdef, Finset.sum_filter]
        rw [hobj, ← hA0, elevObj, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hconst i, hconst i0]
      have hP1raw : ∀ s ∈ ttStates n m, πt s * (∑ t ∈ ttStates n m,
            ∏ i, ∏ j, (φ i j * τ i j * qt i j) ^ (t.2 i j) / ((t.2 i j).factorial : ℝ)) =
          ∏ i, ∏ j, (φ i j * τ i j * qt i j) ^ (s.2 i j) / ((s.2 i j).factorial : ℝ) := by
        have hbal := hqtbal
        clear * - hφ hτ hqt01 hbal hconn hπt hmemIff hmem hsumSt hLU hdep harr hgenG htestG
        have hSle : ∀ (x : Fin n → ℕ) (k : Fin n), 0 < x k → Pi.single k 1 ≤ x := by
          intro x k hk a
          by_cases ha : a = k
          · subst ha; rw [Pi.single_eq_same]; exact hk
          · rw [Pi.single_eq_of_ne ha]; exact Nat.zero_le _
        have hLUii : ∀ i j : Fin n, linkUnit i j i j = 1 := fun i j => if_pos ⟨rfl, rfl⟩
        have hLUle : ∀ (y : Fin n → Fin n → ℕ) (i j : Fin n), 0 < y i j → linkUnit i j ≤ y := by
          intro y i j h a b
          by_cases hab : a = i ∧ b = j
          · obtain ⟨rfl, rfl⟩ := hab; rw [hLUii]; exact h
          · rw [show linkUnit i j a b = 0 from if_neg hab]; exact Nat.zero_le _
        have hsy2 : ∀ (y : Fin n → Fin n → ℕ) (i j : Fin n), 0 < y i j →
            (∑ a, ∑ b, y a b) = (∑ a, ∑ b, (y - linkUnit i j) a b) + 1 := by
          intro y i j hij
          conv_lhs => rw [← tsub_add_cancel_of_le (hLUle y i j hij)]
          simp only [Pi.add_apply, Finset.sum_add_distrib, hLU]
        -- reachability of the all-at-i0 state
        have hreach : ∀ (P : TTState n → Prop), (∀ s, P s → s ∈ (ttStates n m)) →
            (∀ s, P s → ∀ i j, 0 < s.2 i j → 0 < φ i j * qt i j →
                P (s.1 + Pi.single i 1, s.2 - linkUnit i j)) →
            (∀ s, P s → ∀ i j, 0 < s.1 j → P (s.1 - Pi.single j 1, s.2 + linkUnit i j)) →
            ∀ i0 : Fin n, ∀ s, P s → (∀ i j, φ i j * qt i j = 0 → s.2 i j = 0) →
              P (Pi.single i0 m, 0) := by
          intro P hPSt hM1 hM2 i0
          have hpath : ∀ a b, Relation.ReflTransGen (fun a b => a ≠ b ∧ 0 < φ a b * qt a b) a b →
              ∀ s, P s → 0 < s.1 b → P (s.1 - Pi.single b 1 + Pi.single a 1, s.2) := by
            intro a b hab
            induction hab with
            | refl =>
              intro s hs hb
              rw [tsub_add_cancel_of_le (hSle _ _ hb)]; exact hs
            | @tail c b hac hcb ih =>
              intro s hs hb
              have h1 := hM2 s hs c b hb
              have h2 := hM1 _ h1 c b (show 0 < s.2 c b + linkUnit c b c b by
                rw [hLUii]; exact Nat.succ_pos _) hcb.2
              simp only [add_tsub_cancel_right] at h2
              have h3 := ih _ h2 (show 0 < (s.1 - Pi.single b 1 : Fin n → ℕ) c + (Pi.single c 1 : Fin n → ℕ) c by
                rw [Pi.single_eq_same]; exact Nat.succ_pos _)
              simp only [add_tsub_cancel_right] at h3
              exact h3
          have key : ∀ N, ∀ s, P s → (∀ i j, φ i j * qt i j = 0 → s.2 i j = 0) →
              (m - s.1 i0) + (∑ i, ∑ j, s.2 i j) = N → P (Pi.single i0 m, 0) := by
            intro N
            induction N using Nat.strong_induction_on with
            | _ N ih =>
            intro s hs hR hN
            have hsum := hsumSt s (hPSt s hs)
            by_cases hy : ∃ i j, 0 < s.2 i j
            · obtain ⟨i, j, hij⟩ := hy
              have hpos : 0 < φ i j * qt i j := lt_of_le_of_ne (mul_nonneg (hφ i j) (hqt01 i j).1)
                (fun h => absurd (hR i j h.symm) (Nat.pos_iff_ne_zero.1 hij))
              have h2 := hsy2 s.2 i j hij
              have hx : s.1 i0 ≤ (s.1 + Pi.single i 1 : Fin n → ℕ) i0 := Nat.le_add_right _ _
              refine ih _ ?_ _ (hM1 s hs i j hij hpos) ?_ rfl
              · show m - (s.1 + Pi.single i 1 : Fin n → ℕ) i0 + ∑ a, ∑ b, (s.2 - linkUnit i j) a b < N
                omega
              · intro a b hab
                show s.2 a b - linkUnit i j a b = 0
                rw [hR a b hab]; exact Nat.zero_sub _
            · push Not at hy
              have hy0 : ∀ i j, s.2 i j = 0 := fun i j => Nat.le_zero.1 (hy i j)
              by_cases hx : ∃ b, b ≠ i0 ∧ 0 < s.1 b
              · obtain ⟨b, hb, hb0⟩ := hx
                have h1 := hpath i0 b (hconn i0 b) s hs hb0
                have hle : s.1 i0 + s.1 b ≤ ∑ k, s.1 k := by
                  have := Finset.sum_le_sum_of_subset_of_nonneg (f := s.1)
                    (Finset.subset_univ {i0, b}) (fun _ _ _ => Nat.zero_le _)
                  rwa [Finset.sum_pair (Ne.symm hb)] at this
                have hx0 : (s.1 - Pi.single b 1 + Pi.single i0 1 : Fin n → ℕ) i0 = s.1 i0 + 1 := by
                  show s.1 i0 - (Pi.single b 1 : Fin n → ℕ) i0 + (Pi.single i0 1 : Fin n → ℕ) i0 = _
                  rw [Pi.single_eq_of_ne (Ne.symm hb), Pi.single_eq_same, Nat.sub_zero]
                refine ih _ ?_ _ h1 hR rfl
                show m - (s.1 - Pi.single b 1 + Pi.single i0 1 : Fin n → ℕ) i0 + ∑ a, ∑ b, s.2 a b < N
                rw [hx0]; omega
              · push Not at hx
                have hx0 : ∀ b, b ≠ i0 → s.1 b = 0 := fun b hb => Nat.le_zero.1 (hx b hb)
                have hs1 : ∑ k, s.1 k = s.1 i0 := Fintype.sum_eq_single i0 hx0
                have hs2 : (∑ i, ∑ j, s.2 i j) = 0 :=
                  Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => hy0 i j
                have : s = (Pi.single i0 m, 0) := by
                  refine Prod.ext (funext fun k => ?_) (funext fun a => funext fun b => hy0 a b)
                  by_cases hk : k = i0
                  · subst hk; show s.1 k = (Pi.single k m : Fin n → ℕ) k
                    rw [Pi.single_eq_same]; omega
                  · show s.1 k = (Pi.single i0 m : Fin n → ℕ) k
                    rw [Pi.single_eq_of_ne hk]; exact hx0 k hk
                rw [← this]; exact hs
          intro s hs hR
          exact key _ s hs hR rfl
        have hdepK : ∀ s ∈ (ttStates n m), ∀ k i j, 0 < s.1 k →
            (s.1 - Pi.single k 1, s.2 + linkUnit i j) ∈ (ttStates n m) := by
          intro s hs k i j hk
          have h := hsumSt _ (hdep s hs k i hk)
          apply hmem
          rw [← h]
          simp only [Pi.add_apply, Finset.sum_add_distrib, hLU]
        have harrK : ∀ s ∈ (ttStates n m), ∀ k i j, 0 < s.2 i j →
            (s.1 + Pi.single k 1, s.2 - linkUnit i j) ∈ (ttStates n m) := by
          intro s hs k i j hij
          have h := hsumSt _ (harr s hs i j hij)
          apply hmem
          rw [← h]
          simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
            if_true]
        have hQpos : ∀ (t : TTState n) i j, 0 < t.1 i → (toTTPolicy qt) t i j = qt i j := by
          intro t i j h; simp [toTTPolicy, toPolicy, h]
        -- generator applied to g
        have hgen : ∀ (g : TTState n → ℝ), ∀ s ∈ (ttStates n m),
            (∑ t ∈ (ttStates n m), ttRate φ τ (toTTPolicy qt) s t * g t) =
              ∑ i, ∑ j, ((if 0 < s.1 i then φ i j * (toTTPolicy qt) s i j *
                  g (s.1 - Pi.single i 1, s.2 + linkUnit i j) else 0) +
                (if 0 < s.2 i j then (s.2 i j : ℝ) / τ i j *
                  g (s.1 + Pi.single j 1, s.2 - linkUnit i j) else 0)) := by
          intro g s hs
          simp only [ttRate, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [add_mul]
          rw [Finset.sum_add_distrib]
          congr 1
          · by_cases hi : 0 < s.1 i
            · simp only [hi, true_and, if_true, ite_mul, zero_mul]
              rw [Finset.sum_ite_eq' (ttStates n m)]; simp [hdepK s hs i i j hi]
            · simp [hi]
          · by_cases hi : 0 < s.2 i j
            · simp only [hi, true_and, if_true, ite_mul, zero_mul]
              rw [Finset.sum_ite_eq' (ttStates n m)]; simp [harrK s hs j i j hi]
            · simp [hi]
        have hb : ∀ s ∈ (ttStates n m), πt s * (∑ t ∈ (ttStates n m), ttRate φ τ (toTTPolicy qt) s t) =
            ∑ t ∈ (ttStates n m), πt t * ttRate φ τ (toTTPolicy qt) t s := by
          intro s hs
          have := hπt.2.2.2 ⟨s, hs⟩
          simp only [tsum_fintype] at this
          rw [← Finset.sum_coe_sort (ttStates n m) (fun t => ttRate φ τ (toTTPolicy qt) s t),
            ← Finset.sum_coe_sort (ttStates n m) (fun t => πt t * ttRate φ τ (toTTPolicy qt) t s)]
          exact this
        -- predecessor formula
        have hpred : ∀ (F : TTState n → ℝ), ∀ s ∈ (ttStates n m),
            (∑ t ∈ (ttStates n m), F t * ttRate φ τ (toTTPolicy qt) t s) =
              ∑ i, ∑ j, ((if 0 < s.2 i j then F (s.1 + Pi.single i 1, s.2 - linkUnit i j) *
                  (φ i j * qt i j) else 0) +
                (if 0 < s.1 j then F (s.1 - Pi.single j 1, s.2 + linkUnit i j) *
                  (((s.2 i j : ℝ) + 1) / τ i j) else 0)) := by
          intro F s hs
          simp only [ttRate, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [mul_add]
          rw [Finset.sum_add_distrib]
          congr 1
          · have key : ∀ t : TTState n, (0 < t.1 i ∧ s = (t.1 - Pi.single i 1, t.2 + linkUnit i j)) ↔
                (0 < s.2 i j ∧ t = (s.1 + Pi.single i 1, s.2 - linkUnit i j)) := by
              intro t
              constructor
              · rintro ⟨h0, rfl⟩
                refine ⟨?_, Prod.ext (tsub_add_cancel_of_le (hSle _ _ h0)).symm
                  (add_tsub_cancel_right _ _).symm⟩
                show 0 < t.2 i j + linkUnit i j i j
                rw [hLUii]; exact Nat.succ_pos _
              · rintro ⟨h0, rfl⟩
                refine ⟨?_, Prod.ext (add_tsub_cancel_right _ _).symm
                  (tsub_add_cancel_of_le (hLUle _ _ _ h0)).symm⟩
                show 0 < s.1 i + (Pi.single i 1 : Fin n → ℕ) i
                rw [Pi.single_eq_same]; exact Nat.succ_pos _
            simp_rw [key]
            by_cases h1 : 0 < s.2 i j
            · simp only [h1, true_and, if_true, mul_ite, mul_zero]
              rw [Finset.sum_ite_eq' (ttStates n m), if_pos (harrK s hs i i j h1),
                hQpos _ i j (show 0 < s.1 i + (Pi.single i 1 : Fin n → ℕ) i by
                rw [Pi.single_eq_same]; exact Nat.succ_pos _)]
            · simp [h1]
          · have key : ∀ t : TTState n, (0 < t.2 i j ∧ s = (t.1 + Pi.single j 1, t.2 - linkUnit i j)) ↔
                (0 < s.1 j ∧ t = (s.1 - Pi.single j 1, s.2 + linkUnit i j)) := by
              intro t
              constructor
              · rintro ⟨h0, rfl⟩
                refine ⟨?_, Prod.ext (add_tsub_cancel_right _ _).symm
                  (tsub_add_cancel_of_le (hLUle _ _ _ h0)).symm⟩
                show 0 < t.1 j + (Pi.single j 1 : Fin n → ℕ) j
                rw [Pi.single_eq_same]; exact Nat.succ_pos _
              · rintro ⟨h0, rfl⟩
                refine ⟨?_, Prod.ext (tsub_add_cancel_of_le (hSle _ _ h0)).symm
                  (add_tsub_cancel_right _ _).symm⟩
                show 0 < s.2 i j + linkUnit i j i j
                rw [hLUii]; exact Nat.succ_pos _
            simp_rw [key]
            by_cases h1 : 0 < s.1 j
            · simp only [h1, true_and, if_true, mul_ite, mul_zero]
              rw [Finset.sum_ite_eq' (ttStates n m), if_pos (hdepK s hs j i j h1)]
              rw [show ((s.1 - Pi.single j 1, s.2 + linkUnit i j) : TTState n).2 i j = s.2 i j + 1 from
                congrArg (s.2 i j + ·) (hLUii i j), Nat.cast_succ]
            · simp [h1]
        -- (a) πt vanishes on states with a unit on a dead link
        have hoff : ∀ s ∈ (ttStates n m), ∀ a b, φ a b * qt a b = 0 → 0 < s.2 a b → πt s = 0 := by
          intro s0 hs0 a b hab hy0
          have hterm : ∀ s ∈ (ttStates n m), (∑ t ∈ (ttStates n m), ttRate φ τ (toTTPolicy qt) s t *
              ((fun t : TTState n => (t.2 a b : ℝ)) t - (fun t : TTState n => (t.2 a b : ℝ)) s)) =
              -((s.2 a b : ℝ) / τ a b) := by
            intro s hs
            rw [hgenG (toTTPolicy qt) _ s hs]
            have hz : ∀ i j, (if 0 < s.1 i then φ i j * (toTTPolicy qt) s i j *
                ((((s.2 + linkUnit i j) a b : ℕ) : ℝ) - s.2 a b) else 0) = 0 := by
              intro i j
              split_ifs with h
              · rw [Pi.add_apply, Pi.add_apply, Nat.cast_add, add_sub_cancel_left, hQpos s i j h]
                by_cases hij : a = i ∧ b = j
                · obtain ⟨rfl, rfl⟩ := hij; rw [hab, zero_mul]
                · rw [show linkUnit i j a b = 0 from if_neg hij, Nat.cast_zero, mul_zero]
              · rfl
            have hw : ∀ i j, (if 0 < s.2 i j then (s.2 i j : ℝ) / τ i j *
                ((((s.2 - linkUnit i j) a b : ℕ) : ℝ) - s.2 a b) else 0) =
                -(if a = i ∧ b = j then (s.2 a b : ℝ) / τ a b else 0) := by
              intro i j
              split_ifs with h hij hij
              · obtain ⟨rfl, rfl⟩ := hij
                rw [Pi.sub_apply, Pi.sub_apply, hLUii, Nat.cast_sub h, Nat.cast_one]; ring
              · rw [Pi.sub_apply, Pi.sub_apply, show linkUnit i j a b = 0 from if_neg hij, Nat.sub_zero,
                  sub_self, mul_zero, neg_zero]
              · obtain ⟨rfl, rfl⟩ := hij
                rw [show s.2 a b = 0 from Nat.eq_zero_of_not_pos h, Nat.cast_zero, zero_div, neg_zero]
              · rw [neg_zero]
            simp only [hz, hw, zero_add, Finset.sum_neg_distrib]
            congr 1
            rw [Fintype.sum_eq_single a (fun i hi => Finset.sum_eq_zero fun j _ =>
                if_neg fun h => hi h.1.symm),
              Fintype.sum_eq_single b (fun j hj => if_neg fun h => hj h.2.symm), if_pos ⟨rfl, rfl⟩]
          have h := htestG (toTTPolicy qt) πt hπt (fun t : TTState n => (t.2 a b : ℝ))
          rw [Finset.sum_congr rfl (fun s hs => by rw [hterm s hs])] at h
          have h2 : (∑ s ∈ (ttStates n m), πt s * ((s.2 a b : ℝ) / τ a b)) = 0 := by
            have : (∑ s ∈ (ttStates n m), πt s * -((s.2 a b : ℝ) / τ a b)) =
                -(∑ s ∈ (ttStates n m), πt s * ((s.2 a b : ℝ) / τ a b)) := by
              rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun s _ => ?_; ring
            linarith
          have hnn : ∀ s ∈ (ttStates n m), 0 ≤ πt s * ((s.2 a b : ℝ) / τ a b) := fun s _ =>
            mul_nonneg (hπt.1 s) (div_nonneg (Nat.cast_nonneg _) (hτ a b).le)
          have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h2 s0 hs0
          rcases mul_eq_zero.1 this with h3 | h3
          · exact h3
          · exfalso
            have : (0 : ℝ) < (s0.2 a b : ℝ) / τ a b := div_pos (by exact_mod_cast hy0) (hτ a b)
            linarith
        -- the product form
        obtain ⟨f, hfdef⟩ : ∃ f : (Fin n → Fin n → ℕ) → ℝ,
            f = fun y => ∏ i, ∏ j, (φ i j * τ i j * qt i j) ^ (y i j) / ((y i j).factorial : ℝ) :=
          ⟨_, rfl⟩
        have hWnn : ∀ i j, 0 ≤ φ i j * τ i j * qt i j := fun i j =>
          mul_nonneg (mul_nonneg (hφ i j) (hτ i j).le) (hqt01 i j).1
        have hfadd : ∀ (y : Fin n → Fin n → ℕ) (i j : Fin n),
            f (y + linkUnit i j) * ((y i j : ℝ) + 1) = f y * (φ i j * τ i j * qt i j) := by
          intro y i j
          have pt : ∀ a b, (φ a b * τ a b * qt a b) ^ ((y + linkUnit i j) a b) /
              (((y + linkUnit i j) a b).factorial : ℝ) =
              ((φ a b * τ a b * qt a b) ^ (y a b) / ((y a b).factorial : ℝ)) *
                (if a = i then (if b = j then (φ i j * τ i j * qt i j) / ((y i j : ℝ) + 1) else 1)
                  else 1) := by
            intro a b
            by_cases h : a = i ∧ b = j
            · obtain ⟨rfl, rfl⟩ := h
              simp only [Pi.add_apply, linkUnit, and_self, if_true, pow_succ, Nat.factorial_succ,
                Nat.cast_mul, Nat.cast_add, Nat.cast_one]
              rw [div_mul_div_comm, mul_comm ((y a b : ℝ) + 1)]
            · have h1 : linkUnit i j a b = 0 := by simp [linkUnit, h]
              simp only [Pi.add_apply, h1, add_zero]
              by_cases ha : a = i
              · subst ha; have hb : b ≠ j := fun hb => h ⟨rfl, hb⟩; simp [hb]
              · simp [ha]
          rw [hfdef]
          simp only []
          rw [Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun b _ => pt a b))]
          simp only [Finset.prod_mul_distrib]
          have hp : (∏ a, ∏ b, (if a = i then (if b = j then (φ i j * τ i j * qt i j) /
              ((y i j : ℝ) + 1) else 1) else 1)) = (φ i j * τ i j * qt i j) / ((y i j : ℝ) + 1) := by
            rw [Fintype.prod_eq_single i (fun a ha => by simp [ha])]; simp
          rw [hp]
          have : (0 : ℝ) < (y i j : ℝ) + 1 := by positivity
          rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt this)]
        have hfnn : ∀ y, 0 ≤ f y := by
          intro y; rw [hfdef]
          exact Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ =>
            div_nonneg (pow_nonneg (hWnn i j) _) (Nat.cast_nonneg _)
        have hfpos : ∀ y : Fin n → Fin n → ℕ, (∀ i j, φ i j * qt i j = 0 → y i j = 0) → 0 < f y := by
          intro y hy; rw [hfdef]
          refine Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => ?_
          have hf : (0 : ℝ) < ((y i j).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
          by_cases h : φ i j * qt i j = 0
          · rw [hy i j h]; simp
          · have h2 : 0 < φ i j * qt i j :=
              lt_of_le_of_ne (mul_nonneg (hφ i j) (hqt01 i j).1) (Ne.symm h)
            have h3 : 0 < φ i j * τ i j * qt i j := by
              rw [mul_right_comm]; exact mul_pos h2 (hτ i j)
            exact div_pos (pow_pos h3 _) hf
        have hfzero : ∀ (y : Fin n → Fin n → ℕ) a b, φ a b * qt a b = 0 → 0 < y a b → f y = 0 := by
          intro y a b hab hy; rw [hfdef]
          refine Finset.prod_eq_zero (Finset.mem_univ a) (Finset.prod_eq_zero (Finset.mem_univ b) ?_)
          have : φ a b * τ a b * qt a b = 0 := by rw [mul_right_comm, hab, zero_mul]
          rw [this, zero_pow (by omega), zero_div]
        -- ν balance
        have hνbal : ∀ s ∈ (ttStates n m), f s.2 * (∑ t ∈ (ttStates n m), ttRate φ τ (toTTPolicy qt) s t) =
            ∑ t ∈ (ttStates n m), f t.2 * ttRate φ τ (toTTPolicy qt) t s := by
          intro s hs
          have h1 := hgen (fun _ => 1) s hs
          simp only [mul_one] at h1
          rw [h1, hpred (fun t => f t.2) s hs]
          simp only []
          have hT1 : ∀ i j, (if 0 < s.2 i j then f (s.2 - linkUnit i j) * (φ i j * qt i j) else 0) =
              f s.2 * (if 0 < s.2 i j then (s.2 i j : ℝ) / τ i j else 0) := by
            intro i j
            by_cases h : 0 < s.2 i j
            · rw [if_pos h, if_pos h]
              have e1 : s.2 - linkUnit i j + linkUnit i j = s.2 := by
                funext a b; simp only [Pi.add_apply, Pi.sub_apply, linkUnit]
                split_ifs with hh
                · obtain ⟨rfl, rfl⟩ := hh; omega
                · omega
              have e2 : (((s.2 - linkUnit i j) i j : ℕ) : ℝ) + 1 = (s.2 i j : ℝ) := by
                simp only [Pi.sub_apply, linkUnit, and_self, if_true]
                rw [Nat.cast_sub (by omega)]; simp
              have := hfadd (s.2 - linkUnit i j) i j
              rw [e1, e2] at this
              have hτ0 := (hτ i j).ne'
              rw [mul_div_assoc', eq_div_iff hτ0]
              linear_combination -this
            · simp [h]
          have hT2 : ∀ i j, (if 0 < s.1 j then f (s.2 + linkUnit i j) * (((s.2 i j : ℝ) + 1) / τ i j)
              else 0) = (if 0 < s.1 j then f s.2 * (φ i j * qt i j) else 0) := by
            intro i j
            split_ifs
            · have := hfadd s.2 i j
              have hτ0 := (hτ i j).ne'
              rw [mul_div_assoc', div_eq_iff hτ0]
              linear_combination this
            · rfl
          simp only [hT1, hT2, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
          have eA : ∀ i j, f s.2 * (if 0 < s.1 i then φ i j * (toTTPolicy qt) s i j else 0) =
              if 0 < s.1 i then f s.2 * (φ i j * qt i j) else 0 := by
            intro i j
            split_ifs with h
            · rw [hQpos s i j h]
            · simp
          simp only [eA]
          have eB : (∑ i, ∑ j, if 0 < s.1 j then f s.2 * (φ i j * qt i j) else 0) =
              ∑ i, ∑ j, if 0 < s.1 i then f s.2 * (φ i j * qt i j) else 0 := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            split_ifs
            · rw [← Finset.mul_sum, ← Finset.mul_sum, hbal j]
            · simp
          rw [eB, add_comm]
        -- closure of zero sets of nonnegative balanced functions under predecessor moves
        have hclos : ∀ F : TTState n → ℝ, (∀ t ∈ (ttStates n m), 0 ≤ F t) →
            ∀ s ∈ (ttStates n m), F s * (∑ t ∈ (ttStates n m), ttRate φ τ (toTTPolicy qt) s t) = (∑ t ∈ (ttStates n m), F t * ttRate φ τ (toTTPolicy qt) t s) →
            F s = 0 →
            (∀ i j, 0 < s.2 i j → 0 < φ i j * qt i j →
                F (s.1 + Pi.single i 1, s.2 - linkUnit i j) = 0) ∧
              (∀ i j, 0 < s.1 j → F (s.1 - Pi.single j 1, s.2 + linkUnit i j) = 0) := by
          intro F hF s hs hFb hF0
          rw [hF0, zero_mul, hpred F s hs] at hFb
          have hT1 : ∀ i j, 0 ≤ (if 0 < s.2 i j then F (s.1 + Pi.single i 1, s.2 - linkUnit i j) *
              (φ i j * qt i j) else 0) := by
            intro i j; split_ifs with h
            · exact mul_nonneg (hF _ (harrK s hs i i j h)) (mul_nonneg (hφ i j) (hqt01 i j).1)
            · exact le_refl _
          have hT2 : ∀ i j, 0 ≤ (if 0 < s.1 j then F (s.1 - Pi.single j 1, s.2 + linkUnit i j) *
              (((s.2 i j : ℝ) + 1) / τ i j) else 0) := by
            intro i j; split_ifs with h
            · exact mul_nonneg (hF _ (hdepK s hs j i j h))
                (div_nonneg (by positivity) (hτ i j).le)
            · exact le_refl _
          have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
            Finset.sum_nonneg (fun j _ => add_nonneg (hT1 i j) (hT2 i j)))).1 hFb.symm
          have h1 : ∀ i j, _ := fun i j => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
            add_nonneg (hT1 i j) (hT2 i j))).1 (h0 i (Finset.mem_univ _)) j (Finset.mem_univ _)
          constructor
          · intro i j hy hpos
            have := ((add_eq_zero_iff_of_nonneg (hT1 i j) (hT2 i j)).1 (h1 i j)).1
            rw [if_pos hy] at this
            rcases mul_eq_zero.1 this with h | h
            · exact h
            · exact absurd h hpos.ne'
          · intro i j hx
            have := ((add_eq_zero_iff_of_nonneg (hT1 i j) (hT2 i j)).1 (h1 i j)).2
            rw [if_pos hx] at this
            rcases mul_eq_zero.1 this with h | h
            · exact h
            · exfalso
              exact absurd h (ne_of_gt (div_pos (by positivity) (hτ i j)))
        suffices hmain : ∀ s ∈ (ttStates n m), πt s * (∑ t ∈ (ttStates n m), f t.2) = f s.2 by
          intro s hs
          have := hmain s hs
          simp only [hfdef] at this
          exact this
        intro s hs
        have hsum1 : ∑ t ∈ (ttStates n m), πt t = 1 := hπt.2.2.1
        rcases Nat.eq_zero_or_pos n with hn | hn
        · have hSt1 : (ttStates n m) = {s} :=
            Finset.eq_singleton_iff_unique_mem.2 ⟨hs, fun t _ => Prod.ext
              (funext fun i => by subst hn; exact i.elim0)
              (funext fun i => by subst hn; exact i.elim0)⟩
          rw [hSt1, Finset.sum_singleton] at hsum1 ⊢
          rw [hsum1, one_mul]
        let i0 : Fin n := ⟨0, hn⟩
        have hs0 : ((Pi.single i0 m, 0) : TTState n) ∈ (ttStates n m) := hmem _ (by
          show (∑ i, (Pi.single i0 m : Fin n → ℕ) i) + ∑ i, ∑ j, (0 : Fin n → Fin n → ℕ) i j = m
          rw [Finset.sum_pi_single', if_pos (Finset.mem_univ _)]
          simp only [Pi.zero_apply, Finset.sum_const_zero, add_zero])
        have hR0 : ∀ i j, φ i j * qt i j = 0 → ((Pi.single i0 m, 0) : TTState n).2 i j = 0 :=
          fun i j _ => rfl
        have hf0 : f ((Pi.single i0 m, 0) : TTState n).2 = 1 := by rw [hfdef]; simp
        have hfnR : ∀ t : TTState n, ¬ (∀ i j, φ i j * qt i j = 0 → t.2 i j = 0) → f t.2 = 0 := by
          intro t ht; push Not at ht
          obtain ⟨a, b, hab, hy⟩ := ht
          exact hfzero t.2 a b hab (Nat.pos_of_ne_zero hy)
        have hπnR : ∀ t ∈ (ttStates n m), ¬ (∀ i j, φ i j * qt i j = 0 → t.2 i j = 0) → πt t = 0 := by
          intro t htS ht; push Not at ht
          obtain ⟨a, b, hab, hy⟩ := ht
          exact hoff t htS a b hab (Nat.pos_of_ne_zero hy)
        have hRSne : ((ttStates n m).filter (fun t : TTState n => ∀ i j, φ i j * qt i j = 0 → t.2 i j = 0)).Nonempty :=
          ⟨_, Finset.mem_filter.2 ⟨hs0, hR0⟩⟩
        obtain ⟨smax, hsmaxRS, hmax⟩ := Finset.exists_max_image _ (fun t => πt t / f t.2) hRSne
        obtain ⟨smin, hsminRS, hmin⟩ := Finset.exists_min_image _ (fun t => πt t / f t.2) hRSne
        obtain ⟨hsmaxS, hsmaxR⟩ := Finset.mem_filter.1 hsmaxRS
        obtain ⟨hsminS, hsminR⟩ := Finset.mem_filter.1 hsminRS
        have hfmax := hfpos smax.2 hsmaxR
        have hfmin := hfpos smin.2 hsminR
        -- the maximum
        have hF1nn : ∀ t ∈ (ttStates n m), 0 ≤ (fun t : TTState n => πt smax / f smax.2 * f t.2 - πt t) t := by
          intro t ht
          try simp only []
          by_cases hRt : ∀ i j, φ i j * qt i j = 0 → t.2 i j = 0
          · have h := hmax t (Finset.mem_filter.2 ⟨ht, hRt⟩)
            try simp only [] at h
            rw [div_le_iff₀ (hfpos t.2 hRt)] at h
            linarith
          · rw [hfnR t hRt, hπnR t ht hRt]; simp
        have hF2nn : ∀ t ∈ (ttStates n m), 0 ≤ (fun t : TTState n => πt t - πt smin / f smin.2 * f t.2) t := by
          intro t ht
          try simp only []
          by_cases hRt : ∀ i j, φ i j * qt i j = 0 → t.2 i j = 0
          · have h := hmin t (Finset.mem_filter.2 ⟨ht, hRt⟩)
            try simp only [] at h
            rw [le_div_iff₀ (hfpos t.2 hRt)] at h
            linarith
          · rw [hfnR t hRt, hπnR t ht hRt]; simp
        have hcomb : ∀ c d : ℝ, ∀ s ∈ (ttStates n m),
            (fun t : TTState n => c * f t.2 + d * πt t) s * (∑ t ∈ (ttStates n m), ttRate φ τ (toTTPolicy qt) s t) =
              ∑ t ∈ (ttStates n m), (fun t : TTState n => c * f t.2 + d * πt t) t * ttRate φ τ (toTTPolicy qt) t s := by
          intro c d s hs
          try simp only []
          rw [add_mul, mul_assoc, mul_assoc, hνbal s hs, hb s hs, Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun t _ => ?_; ring
        have hbal1 : ∀ s ∈ (ttStates n m), (fun t : TTState n => πt smax / f smax.2 * f t.2 - πt t) s *
            (∑ t ∈ (ttStates n m), ttRate φ τ (toTTPolicy qt) s t) =
              ∑ t ∈ (ttStates n m), (fun t : TTState n => πt smax / f smax.2 * f t.2 - πt t) t *
                ttRate φ τ (toTTPolicy qt) t s := by
          intro s hs
          have := hcomb (πt smax / f smax.2) (-1) s hs
          simp only [neg_one_mul, ← sub_eq_add_neg] at this
          exact this
        have hbal2 : ∀ s ∈ (ttStates n m), (fun t : TTState n => πt t - πt smin / f smin.2 * f t.2) s *
            (∑ t ∈ (ttStates n m), ttRate φ τ (toTTPolicy qt) s t) =
              ∑ t ∈ (ttStates n m), (fun t : TTState n => πt t - πt smin / f smin.2 * f t.2) t *
                ttRate φ τ (toTTPolicy qt) t s := by
          intro s hs
          have := hcomb (-(πt smin / f smin.2)) 1 s hs
          simp only [one_mul, neg_mul] at this
          simp only [sub_eq_neg_add]
          exact this
        have hP : ∀ F : TTState n → ℝ, (∀ t ∈ (ttStates n m), 0 ≤ F t) →
            (∀ s ∈ (ttStates n m), F s * (∑ t ∈ (ttStates n m), ttRate φ τ (toTTPolicy qt) s t) = ∑ t ∈ (ttStates n m), F t * ttRate φ τ (toTTPolicy qt) t s) →
            ∀ s ∈ (ttStates n m), (∀ i j, φ i j * qt i j = 0 → s.2 i j = 0) → F s = 0 →
              F ((Pi.single i0 m, 0) : TTState n) = 0 := by
          intro F hF hFb s hs hR hF0
          refine (hreach (fun t => t ∈ (ttStates n m) ∧ F t = 0) (fun t h => h.1) ?_ ?_ i0 s ⟨hs, hF0⟩ hR).2
          · intro t ht i j hy hpos
            exact ⟨harrK t ht.1 i i j hy, (hclos F hF t ht.1 (hFb t ht.1) ht.2).1 i j hy hpos⟩
          · intro t ht i j hx
            exact ⟨hdepK t ht.1 j i j hx, (hclos F hF t ht.1 (hFb t ht.1) ht.2).2 i j hx⟩
        have e1 := hP _ hF1nn hbal1 smax hsmaxS hsmaxR (by rw [div_mul_cancel₀ _ hfmax.ne', sub_self])
        have e2 := hP _ hF2nn hbal2 smin hsminS hsminR (by rw [div_mul_cancel₀ _ hfmin.ne', sub_self])
        simp only [hf0, mul_one] at e1 e2
        have hHL : πt smax / f smax.2 = πt smin / f smin.2 := by linarith only [e1, e2]
        have hall : ∀ t ∈ (ttStates n m), πt t = πt smax / f smax.2 * f t.2 := by
          intro t ht
          by_cases hRt : ∀ i j, φ i j * qt i j = 0 → t.2 i j = 0
          · have h1 := hmax t (Finset.mem_filter.2 ⟨ht, hRt⟩)
            have h2 := hmin t (Finset.mem_filter.2 ⟨ht, hRt⟩)
            try simp only [] at h1 h2
            have hft := hfpos t.2 hRt
            have : πt t / f t.2 = πt smax / f smax.2 := le_antisymm h1 (hHL ▸ h2)
            rw [div_eq_iff hft.ne'] at this
            exact this
          · rw [hfnR t hRt, hπnR t ht hRt, mul_zero]
        have hZ : πt smax / f smax.2 * ∑ t ∈ (ttStates n m), f t.2 = 1 := by
          rw [Finset.mul_sum, ← hsum1]
          exact Finset.sum_congr rfl fun t ht => (hall t ht).symm
        rw [hall s hs]
        rw [mul_right_comm, hZ, one_mul]
      have hw0 : ∀ i j, 0 ≤ φ i j * τ i j * qt i j := fun i j =>
        mul_nonneg (mul_nonneg (hφ i j) (hτ i j).le) (hqt01 i j).1
      obtain ⟨ν, hν⟩ : ∃ ν : TTState n → ℝ, ν = fun t =>
          ∏ i, ∏ j, (φ i j * τ i j * qt i j) ^ (t.2 i j) / ((t.2 i j).factorial : ℝ) := ⟨_, rfl⟩
      obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = Real.sqrt (m * Real.log m) / (Real.sqrt (m * Real.log m) + n - 1) -
            3 / Real.sqrt (m * Real.log m) := ⟨_, rfl⟩
      have hP1 : ∀ s ∈ ttStates n m, πt s * (∑ t ∈ ttStates n m, ν t) = ν s := by
        subst hν; exact hP1raw
      have hP2 : B * (∑ t ∈ ttStates n m, ν t) ≤
          ∑ t ∈ (ttStates n m).filter (fun s => 0 < s.1 i0), ν t := by
        subst hν hBdef; exact hP2gen _ hw0 hqtW i0
      clear hP1raw hP2gen hgenG htestG hdep harr hmem hmemIff hsumSt hLU
      have hν0 : ∀ t, 0 ≤ ν t := fun t => by
        rw [hν]
        exact Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ =>
          div_nonneg (pow_nonneg (hw0 i j) _) (Nat.cast_nonneg _)
      have hs0 : ((fun i => if i = i0 then m else 0, fun _ _ => 0) : TTState n) ∈ ttStates n m := by
        unfold ttStates
        simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range]
        refine ⟨⟨fun i => ?_, fun i j => Nat.succ_pos m⟩, ?_⟩
        · split_ifs <;> omega
        · rw [Finset.sum_ite_eq']; simp only [Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero]
      have hZpos : 0 < ∑ t ∈ ttStates n m, ν t := by
        have h1 : ν ((fun i => if i = i0 then m else 0, fun _ _ => 0) : TTState n) = 1 := by
          rw [hν]
          simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, Finset.prod_const_one]
        have := Finset.single_le_sum (fun t _ => hν0 t) hs0 (f := ν)
        rw [h1] at this; linarith only [this]
      obtain ⟨Av, hAv⟩ : ∃ Av : ℝ, Av = ∑ s ∈ (ttStates n m).filter (fun s => 0 < s.1 i0), πt s :=
        ⟨_, rfl⟩
      have hAvZ : Av * (∑ t ∈ ttStates n m, ν t) =
          ∑ t ∈ (ttStates n m).filter (fun s => 0 < s.1 i0), ν t := by
        rw [hAv, Finset.sum_mul]
        exact Finset.sum_congr rfl fun s hs => hP1 s (Finset.mem_filter.1 hs).1
      have hAvB : B ≤ Av := by
        have : B * (∑ t ∈ ttStates n m, ν t) ≤ Av * (∑ t ∈ ttStates n m, ν t) := by
          rw [hAvZ]; exact hP2
        exact le_of_mul_le_mul_right this hZpos
      have hAv0 : 0 ≤ Av := by rw [hAv]; exact Finset.sum_nonneg fun s _ => hπt.1 s
      rw [hE, ← hAv]
      have hmax : max (ttObj n m φ I q π) 0 ≤ elevObj φ I q' := max_le hA hE'0
      have hmax0 : 0 ≤ max (ttObj n m φ I q π) 0 := le_max_right _ _
      have hdf : delayFactor n m = (1 - ε) * B := by rw [hBdef]; rfl
      rw [hdf]
      rcases le_or_gt 0 B with hB0 | hB0
      · calc (1 - ε) * B * max (ttObj n m φ I q π) 0 ≤ (1 - ε) * B * elevObj φ I q' :=
              mul_le_mul_of_nonneg_left hmax (mul_nonneg (by linarith) hB0)
          _ = B * ((1 - ε) * elevObj φ I q') := by ring
          _ ≤ B * elevObj φ I qt := mul_le_mul_of_nonneg_left hqtE hB0
          _ ≤ Av * elevObj φ I qt := mul_le_mul_of_nonneg_right hAvB hEqt0
      · have : (1 - ε) * B * max (ttObj n m φ I q π) 0 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) hB0.le) hmax0
        exact this.trans (mul_nonneg hAv0 hEqt0)
