-- Prove2me | solution 1 for SharedVehicleApprox.Pricing.Supplement.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:04:27.698303+00:00
-- url     : https://prove2.me/submissions/fa9ebca8-f1b1-4969-a7ac-1bbaf3e60bd2

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_StationaryLaw
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_TravelTimes

open Finset QueueingFundamentals.Networks

open SharedVehicleApprox
open SharedVehicleApprox.Pricing
open SharedVehicleApprox.Pricing.Supplement

/-- Lemma 16, p. 19 (corrected: the support graph of `q` is strongly connected): conditioned on the
number `M₀` of available units, the node queues of the system with travel times follow the
`M₀`-unit Gordon–Newell network with the same quantiles and arrival rates. The conditional law is
stationary for that network and equals its product-form law (4). -/
theorem solution {n m : ℕ} (φ τ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (hτ : ∀ i j, 0 < τ i j) (q : Fin n → Fin n → ℝ) (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ 1)
    (hconn : SupportConnected φ q)
    (π : TTState n → ℝ) (hπ : IsTTStationary n m φ τ (toTTPolicy q) π)
    (M₀ : ℕ) (hM : 0 < availableProb m π M₀) :
    IsStationary n M₀ φ (toPolicy q) (condNodeLaw m π M₀) ∧
      ∀ r : Fin n → ℝ, (∀ i, 0 < r i) → IsTraffic φ q r →
        condNodeLaw m π M₀ = productForm (fun j y => r j ^ y) M₀ := by
          set St := ttStates n m with hSt
          set R := ttRate φ τ (toTTPolicy q) with hR
          have memSt : ∀ s : TTState n, s ∈ St ↔ (∑ i, s.1 i) + (∑ i, ∑ j, s.2 i j) = m := by
            intro s
            rw [hSt, ttStates, mem_filter]
            constructor
            · exact fun h => h.2
            · intro h
              refine ⟨?_, h⟩
              rw [mem_product]
              constructor
              · rw [Fintype.mem_piFinset]; intro i; rw [mem_range]
                have := single_le_sum (f := fun i => s.1 i) (fun _ _ => Nat.zero_le _) (mem_univ i)
                omega
              · rw [Fintype.mem_piFinset]; intro i; rw [Fintype.mem_piFinset]; intro j; rw [mem_range]
                have h1 := single_le_sum (f := fun j => s.2 i j) (fun _ _ => Nat.zero_le _) (mem_univ j)
                have h2 := single_le_sum (f := fun i => ∑ j, s.2 i j) (fun _ _ => Nat.zero_le _) (mem_univ i)
                omega
          have sumSingle : ∀ (x : Fin n → ℕ) (i : Fin n), ∑ k, (x + Pi.single i (1:ℕ) : Fin n → ℕ) k = ∑ k, x k + 1 := by
            intro x i
            simp only [Pi.add_apply, sum_add_distrib]
            congr 1
            simp [Pi.single_apply]
          have sumSub : ∀ (x : Fin n → ℕ) (i : Fin n), 0 < x i → ∑ k, (x - Pi.single i (1:ℕ) : Fin n → ℕ) k + 1 = ∑ k, x k := by
            intro x i hi
            have : x = (x - Pi.single i 1) + Pi.single i 1 := by
              funext k
              by_cases hk : k = i
              · subst hk; simp; omega
              · simp [Pi.single_apply, hk]
            conv_rhs => rw [this]
            rw [sumSingle]
          have sumLink : ∀ (y : Fin n → Fin n → ℕ) (i j : Fin n), ∑ a, ∑ b, (y + linkUnit i j) a b = ∑ a, ∑ b, y a b + 1 := by
            intro y i j
            simp only [Pi.add_apply, sum_add_distrib, linkUnit]
            congr 1
            rw [Finset.sum_eq_single i]
            · simp
            · intro b _ hb; simp [hb]
            · simp
          have sumLinkSub : ∀ (y : Fin n → Fin n → ℕ) (i j : Fin n), 0 < y i j → ∑ a, ∑ b, (y - linkUnit i j) a b + 1 = ∑ a, ∑ b, y a b := by
            intro y i j hij
            have : y = (y - linkUnit i j) + linkUnit i j := by
              funext a b
              by_cases h : a = i ∧ b = j
              · obtain ⟨rfl, rfl⟩ := h; simp [linkUnit]; omega
              · simp [linkUnit, h]
            conv_rhs => rw [this]
            rw [sumLink]
          -- membership of moves
          have memDep : ∀ s ∈ St, ∀ i j, 0 < s.1 i → ((s.1 - Pi.single i 1, s.2 + linkUnit i j) : TTState n) ∈ St := by
            intro s hs i j hi
            rw [memSt] at hs ⊢
            have := sumSub s.1 i hi; have := sumLink s.2 i j
            simp only at *; omega
          have memArr : ∀ s ∈ St, ∀ i j, 0 < s.2 i j → ((s.1 + Pi.single j 1, s.2 - linkUnit i j) : TTState n) ∈ St := by
            intro s hs i j hi
            rw [memSt] at hs ⊢
            have := sumSingle s.1 j; have := sumLinkSub s.2 i j hi
            simp only at *; omega
          have memArr' : ∀ s ∈ St, ∀ i j, 0 < s.2 i j → ((s.1 + Pi.single i 1, s.2 - linkUnit i j) : TTState n) ∈ St := by
            intro s hs i j hi
            rw [memSt] at hs ⊢
            have := sumSingle s.1 i; have := sumLinkSub s.2 i j hi
            simp only at *; omega
          have memDep' : ∀ s ∈ St, ∀ i j, 0 < s.1 j → ((s.1 - Pi.single j 1, s.2 + linkUnit i j) : TTState n) ∈ St := by
            intro s hs i j hi
            rw [memSt] at hs ⊢
            have := sumSub s.1 j hi; have := sumLink s.2 i j
            simp only at *; omega
          -- forward formula
          have FWD : ∀ s ∈ St, ∀ F : TTState n → ℝ, ∑ t ∈ St, R s t * F t =
              ∑ i, ∑ j, ((if 0 < s.1 i then φ i j * q i j * F (s.1 - Pi.single i 1, s.2 + linkUnit i j) else 0) +
                (if 0 < s.2 i j then (s.2 i j : ℝ) / τ i j * F (s.1 + Pi.single j 1, s.2 - linkUnit i j) else 0)) := by
            intro s hs F
            simp only [hR, ttRate, sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            simp only [add_mul, sum_add_distrib]
            congr 1
            · by_cases hi : 0 < s.1 i
              · simp only [hi, true_and, if_true, toTTPolicy, toPolicy]
                rw [Finset.sum_eq_single (s.1 - Pi.single i 1, s.2 + linkUnit i j)]
                · simp
                · intro b _ hb; simp [hb]
                · intro h; exact absurd (memDep s hs i j hi) h
              · simp [hi]
            · by_cases hi : 0 < s.2 i j
              · simp only [hi, true_and, if_true]
                rw [Finset.sum_eq_single (s.1 + Pi.single j 1, s.2 - linkUnit i j)]
                · simp
                · intro b _ hb; simp [hb]
                · intro h; exact absurd (memArr s hs i j hi) h
              · simp [hi]
          have hbal : ∀ s ∈ St, π s * ∑ t ∈ St, R s t = ∑ t ∈ St, π t * R t s := by
            intro s hs
            have := hπ.2.2.2 ⟨s, hs⟩
            simp only [tsum_fintype] at this
            rw [← Finset.sum_attach St (fun t => R s t), ← Finset.sum_attach St (fun t => π t * R t s)]
            exact this
          have INF : ∀ s ∈ St, ∀ G : TTState n → ℝ, ∑ t ∈ St, G t * R t s =
              ∑ i, ∑ j, ((if 0 < s.2 i j then G (s.1 + Pi.single i 1, s.2 - linkUnit i j) * (φ i j * q i j) else 0) +
                (if 0 < s.1 j then G (s.1 - Pi.single j 1, s.2 + linkUnit i j) * (((s.2 i j : ℝ) + 1) / τ i j) else 0)) := by
            intro s hs G
            simp only [hR, ttRate, mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            simp only [mul_add, sum_add_distrib]
            congr 1
            · have key : ∀ t : TTState n, (0 < t.1 i ∧ s = (t.1 - Pi.single i 1, t.2 + linkUnit i j)) ↔
                  (0 < s.2 i j ∧ t = (s.1 + Pi.single i 1, s.2 - linkUnit i j)) := by
                intro t
                constructor
                · rintro ⟨h0, rfl⟩
                  refine ⟨by simp [linkUnit], Prod.ext (funext fun k => ?_) (funext fun a => funext fun b => ?_)⟩
                  · by_cases hk : k = i
                    · subst hk; simp; omega
                    · simp [hk]
                  · by_cases hk : a = i ∧ b = j
                    · obtain ⟨rfl, rfl⟩ := hk; simp [linkUnit]
                    · simp [linkUnit, hk]
                · rintro ⟨h0, rfl⟩
                  refine ⟨by simp, Prod.ext (funext fun k => ?_) (funext fun a => funext fun b => ?_)⟩
                  · by_cases hk : k = i
                    · subst hk; simp
                    · simp [hk]
                  · by_cases hk : a = i ∧ b = j
                    · obtain ⟨rfl, rfl⟩ := hk; simp [linkUnit]; omega
                    · simp [linkUnit, hk]
              simp_rw [key]
              by_cases h0 : 0 < s.2 i j
              · simp only [h0, true_and]
                rw [Finset.sum_eq_single (s.1 + Pi.single i 1, s.2 - linkUnit i j)]
                · simp [toTTPolicy, toPolicy]
                · intro b _ hb; simp [hb]
                · intro h; exact absurd (memArr' s hs i j h0) h
              · simp [h0]
            · have key : ∀ t : TTState n, (0 < t.2 i j ∧ s = (t.1 + Pi.single j 1, t.2 - linkUnit i j)) ↔
                  (0 < s.1 j ∧ t = (s.1 - Pi.single j 1, s.2 + linkUnit i j)) := by
                intro t
                constructor
                · rintro ⟨h0, rfl⟩
                  refine ⟨by simp, Prod.ext (funext fun k => ?_) (funext fun a => funext fun b => ?_)⟩
                  · by_cases hk : k = j
                    · subst hk; simp
                    · simp [hk]
                  · by_cases hk : a = i ∧ b = j
                    · obtain ⟨rfl, rfl⟩ := hk; simp [linkUnit]; omega
                    · simp [linkUnit, hk]
                · rintro ⟨h0, rfl⟩
                  refine ⟨by simp [linkUnit], Prod.ext (funext fun k => ?_) (funext fun a => funext fun b => ?_)⟩
                  · by_cases hk : k = j
                    · subst hk; simp; omega
                    · simp [hk]
                  · by_cases hk : a = i ∧ b = j
                    · obtain ⟨rfl, rfl⟩ := hk; simp [linkUnit]
                    · simp [linkUnit, hk]
              simp_rw [key]
              by_cases h0 : 0 < s.1 j
              · simp only [h0, true_and]
                rw [Finset.sum_eq_single (s.1 - Pi.single j 1, s.2 + linkUnit i j)]
                · simp [linkUnit]
                · intro b _ hb; simp [hb]
                · intro h; exact absurd (memDep' s hs i j h0) h
              · simp [h0]
          have PTB : ∀ r : Fin n → ℝ, (∀ i, 0 < r i) → IsTraffic φ q r →
              ∀ s ∈ St, (fun s : TTState n => (∏ i, r i ^ s.1 i) * ∏ i, ∏ j, (r i * φ i j * q i j * τ i j) ^ s.2 i j / ((s.2 i j).factorial : ℝ)) s * ∑ t ∈ St, R s t =
                ∑ t ∈ St, (fun s : TTState n => (∏ i, r i ^ s.1 i) * ∏ i, ∏ j, (r i * φ i j * q i j * τ i j) ^ s.2 i j / ((s.2 i j).factorial : ℝ)) t * R t s := by
            intro r hr htr s hs
            set w : Fin n → Fin n → ℝ := fun i j => r i * φ i j * q i j * τ i j with hw
            set P : (Fin n → ℕ) → ℝ := fun x => ∏ i, r i ^ x i with hP
            set Q : (Fin n → Fin n → ℕ) → ℝ := fun y => ∏ i, ∏ j, w i j ^ y i j / ((y i j).factorial : ℝ) with hQ
            have PX1 : ∀ x a, P (x + Pi.single a 1) = r a * P x := by
              intro x a
              simp only [hP, Pi.add_apply, pow_add, prod_mul_distrib, Pi.single_apply]
              rw [mul_comm]; congr 1
              rw [Finset.prod_eq_single a]
              · simp
              · intro b _ hb; simp [hb]
              · simp
            have PX2 : ∀ x a, 0 < x a → P (x - Pi.single a 1) * r a = P x := by
              intro x a ha
              have : x = (x - Pi.single a 1) + Pi.single a 1 := by
                funext k
                by_cases hk : k = a
                · subst hk; simp; omega
                · simp [hk]
              conv_rhs => rw [this, PX1]
              ring
            have PY1 : ∀ y i j, Q (y + linkUnit i j) = w i j / ((y i j : ℝ) + 1) * Q y := by
              intro y i j
              have : ∀ a b, w a b ^ (y + linkUnit i j) a b / (((y + linkUnit i j) a b).factorial : ℝ) =
                  (w a b ^ y a b / ((y a b).factorial : ℝ)) * (if a = i then (if b = j then w i j / ((y i j : ℝ) + 1) else 1) else 1) := by
                intro a b
                by_cases hk : a = i ∧ b = j
                · obtain ⟨rfl, rfl⟩ := hk
                  simp only [Pi.add_apply, linkUnit, and_self, if_true, Nat.factorial_succ, Nat.cast_mul, pow_succ]
                  push_cast
                  field_simp
                · simp only [Pi.add_apply, linkUnit, hk, if_false, add_zero, mul_ite, mul_one]
                  by_cases ha : a = i
                  · subst ha; have hb : b ≠ j := fun h => hk ⟨rfl, h⟩; simp [hb]
                  · simp [ha]
              simp only [hQ, this, prod_mul_distrib]
              rw [mul_comm]; congr 1
              rw [Finset.prod_eq_single i]
              · rw [Finset.prod_eq_single j]
                · simp
                · intro b _ hb; simp [hb]
                · simp
              · intro b _ hb; simp [hb]
              · simp
            have PY2 : ∀ y i j, 0 < y i j → Q (y - linkUnit i j) * (w i j / (y i j : ℝ)) = Q y := by
              intro y i j hij
              have e : y = (y - linkUnit i j) + linkUnit i j := by
                funext a b
                by_cases h : a = i ∧ b = j
                · obtain ⟨rfl, rfl⟩ := h; simp [linkUnit]; omega
                · simp [linkUnit, h]
              have e2 : ((y - linkUnit i j) i j : ℝ) + 1 = (y i j : ℝ) := by
                have : (y - linkUnit i j) i j + 1 = y i j := by simp [linkUnit]; omega
                exact_mod_cast this
              conv_rhs => rw [e, PY1, e2]
              ring
            show P s.1 * Q s.2 * _ = ∑ t ∈ St, P t.1 * Q t.2 * R t s
            have h1 := FWD s hs (fun _ => 1)
            simp only [mul_one] at h1
            rw [h1, INF s hs (fun t => P t.1 * Q t.2)]
            have T1 : ∀ i j, (if 0 < s.2 i j then P (s.1 + Pi.single i 1) * Q (s.2 - linkUnit i j) * (φ i j * q i j) else 0)
                = if 0 < s.2 i j then P s.1 * Q s.2 * ((s.2 i j : ℝ) / τ i j) else 0 := by
              intro i j
              by_cases h0 : 0 < s.2 i j
              · rw [if_pos h0, if_pos h0, PX1, ← PY2 s.2 i j h0]
                have : (s.2 i j : ℝ) ≠ 0 := by positivity
                have := (hτ i j).ne'
                simp only [hw]; field_simp
              · rw [if_neg h0, if_neg h0]
            have T2 : ∀ i j, (if 0 < s.1 j then P (s.1 - Pi.single j 1) * Q (s.2 + linkUnit i j) * (((s.2 i j : ℝ) + 1) / τ i j) else 0)
                = if 0 < s.1 j then P s.1 * Q s.2 * (r i * φ i j * q i j / r j) else 0 := by
              intro i j
              by_cases h0 : 0 < s.1 j
              · rw [if_pos h0, if_pos h0, PY1, ← PX2 s.1 j h0]
                have : (s.2 i j : ℝ) + 1 ≠ 0 := by positivity
                have := (hτ i j).ne'
                have := (hr j).ne'
                simp only [hw]; field_simp
              · rw [if_neg h0, if_neg h0]
            simp only [T1, T2, sum_add_distrib]
            rw [Finset.sum_comm (f := fun i j => if 0 < s.1 j then P s.1 * Q s.2 * (r i * φ i j * q i j / r j) else 0)]
            have T3 : ∀ j, (∑ i, if 0 < s.1 j then P s.1 * Q s.2 * (r i * φ i j * q i j / r j) else 0) =
                ∑ k, if 0 < s.1 j then P s.1 * Q s.2 * (φ j k * q j k) else 0 := by
              intro j
              by_cases h0 : 0 < s.1 j
              · simp only [if_pos h0, ← mul_sum]
                congr 1
                have := htr j
                have hrj := (hr j).ne'
                rw [← Finset.sum_div]
                simp only [mul_assoc] at this ⊢
                rw [this]; field_simp
              · simp [h0]
            simp only [T3, mul_add, mul_sum]
            rw [add_comm]
            congr 1 <;>
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_)) <;>
            split_ifs <;> ring
          have GNS : ∀ (N : ℕ) (r : Fin n → ℝ), (∀ i, 0 < r i) → IsTraffic φ q r → (states n N).Nonempty →
              IsStationary n N φ (toPolicy q) (productForm (fun j y => r j ^ y) N) := by
            intro N r hr htr hne
            have memS : ∀ x : Fin n → ℕ, x ∈ states n N ↔ ∑ i, x i = N := by
              intro x
              rw [states, mem_filter]
              constructor
              · exact fun h => h.2
              · intro h
                refine ⟨?_, h⟩
                rw [Fintype.mem_piFinset]; intro i; rw [mem_range]
                have := single_le_sum (f := fun i => x i) (fun _ _ => Nat.zero_le _) (mem_univ i)
                omega
            set P : (Fin n → ℕ) → ℝ := fun x => ∏ i, r i ^ x i with hP
            have PX1 : ∀ x a, P (x + Pi.single a 1) = r a * P x := by
              intro x a
              simp only [hP, Pi.add_apply, pow_add, prod_mul_distrib, Pi.single_apply]
              rw [mul_comm]; congr 1
              rw [Finset.prod_eq_single a]
              · simp
              · intro b _ hb; simp [hb]
              · simp
            have Ppos : ∀ x, 0 < P x := fun x => Finset.prod_pos (fun i _ => pow_pos (hr i) _)
            set G := normConst (fun j y => r j ^ y) N with hGdef
            have hG : 0 < G := by
              rw [hGdef, normConst]
              exact Finset.sum_pos (fun x _ => Ppos x) hne
            have hpf : ∀ x, productForm (fun j y => r j ^ y) N x = if x ∈ states n N then P x / G else 0 := by
              intro x; rfl
            have MS : ∀ x : Fin n → ℕ, ∀ i j, i ≠ j → 1 ≤ x j →
                moveState x i j + Pi.single j 1 = x + Pi.single i 1 := by
              intro x i j hij hj
              funext k
              simp only [moveState, Pi.add_apply, Function.update_apply, Pi.single_apply]
              by_cases hki : k = i
              · subst hki; simp [hij]
              · by_cases hkj : k = j
                · subst hkj; simp [hki]; omega
                · simp [hki, hkj]
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro x; rw [hpf]; split_ifs
              · exact div_nonneg (Ppos x).le hG.le
              · exact le_refl _
            · intro x hx; rw [hpf, if_neg hx]
            · rw [Finset.sum_congr rfl (fun x hx => by rw [hpf, if_pos hx]), ← Finset.sum_div]
              exact div_self hG.ne'
            · intro x hx
              have T : ∀ i j, inflowTerm φ (toPolicy q) (productForm (fun j y => r j ^ y) N) x i j =
                  if 0 < x j then P x / G * (r i * φ i j * q i j / r j) else 0 := by
                intro i j
                unfold inflowTerm
                by_cases hij : i = j
                · subst hij
                  rw [if_pos rfl, hpf, if_pos hx]
                  simp only [toPolicy]
                  have := (hr i).ne'
                  split_ifs
                  · field_simp
                  · simp
                · rw [if_neg hij]
                  by_cases hj : 1 ≤ x j
                  · rw [if_pos hj, if_pos (by omega)]
                    have hms := MS x i j hij hj
                    have hmem : moveState x i j ∈ states n N := by
                      rw [memS] at hx ⊢
                      have h1 := sumSingle (moveState x i j) j
                      have h2 := sumSingle x i
                      rw [hms] at h1
                      omega
                    have hP2 : P (moveState x i j) * r j = P x * r i := by
                      rw [mul_comm, ← PX1, hms, PX1, mul_comm]
                    have hpos : 0 < moveState x i j i := by
                      simp [moveState]
                    rw [hpf, if_pos hmem]
                    simp only [toPolicy, if_pos hpos]
                    have := (hr j).ne'
                    have hPm : P (moveState x i j) = P x * r i / r j := by
                      field_simp; linarith [hP2]
                    rw [hPm]
                    field_simp
                  · rw [if_neg hj, if_neg (by omega)]
              simp only [T]
              rw [Finset.sum_comm (f := fun i j => if 0 < x j then P x / G * (r i * φ i j * q i j / r j) else 0)]
              have T3 : ∀ j, (∑ i, if 0 < x j then P x / G * (r i * φ i j * q i j / r j) else 0) =
                  if 0 < x j then P x / G * ∑ k, φ j k * q j k else 0 := by
                intro j
                by_cases h0 : 0 < x j
                · simp only [if_pos h0, ← mul_sum]
                  congr 1
                  have := htr j
                  have hrj := (hr j).ne'
                  rw [← Finset.sum_div]
                  simp only [mul_assoc] at this ⊢
                  rw [this]; field_simp
                · simp [h0]
              simp only [T3]
              rw [hpf, if_pos hx, mul_sum]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              simp only [toPolicy]
              split_ifs <;> simp
          have DEAD : ∀ s ∈ St, ∀ i j, ¬ (0 < φ i j * q i j) → 0 < s.2 i j → π s = 0 := by
            have GEN : ∀ F : TTState n → ℝ, ∑ s ∈ St, π s * ∑ t ∈ St, R s t * F t =
                ∑ s ∈ St, π s * F s * ∑ t ∈ St, R s t := by
              intro F
              simp only [mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl (fun t ht => ?_)
              have := hbal t ht
              rw [show ∑ s ∈ St, π s * (R s t * F t) = (∑ s ∈ St, π s * R s t) * F t by
                rw [sum_mul]; exact Finset.sum_congr rfl (fun _ _ => by ring), ← this, ← mul_sum]
              ring
            set Dy : (Fin n → Fin n → ℕ) → ℝ := fun y => ∑ a, ∑ b, (if 0 < φ a b * q a b then 0 else (y a b : ℝ)) with hDy
            have DyAdd : ∀ y i j, Dy (y + linkUnit i j) = Dy y + (if 0 < φ i j * q i j then 0 else 1) := by
              intro y i j
              have : ∀ a b, (if 0 < φ a b * q a b then 0 else (((y + linkUnit i j) a b : ℕ) : ℝ)) =
                  (if 0 < φ a b * q a b then 0 else (y a b : ℝ)) +
                    (if 0 < φ a b * q a b then 0 else ((linkUnit i j a b : ℕ) : ℝ)) := by
                intro a b; split_ifs <;> simp
              simp only [hDy, this, sum_add_distrib]
              congr 1
              rw [Finset.sum_eq_single i]
              · rw [Finset.sum_eq_single j]
                · simp [linkUnit]
                · intro b _ hb; simp [linkUnit, hb]
                · simp
              · intro b _ hb; apply Finset.sum_eq_zero; intro c _; simp [linkUnit, hb]
              · simp
            have DySub : ∀ y i j, 0 < y i j → Dy (y - linkUnit i j) = Dy y - (if 0 < φ i j * q i j then 0 else 1) := by
              intro y i j hij
              have e : y = (y - linkUnit i j) + linkUnit i j := by
                funext a b
                by_cases h : a = i ∧ b = j
                · obtain ⟨rfl, rfl⟩ := h; simp [linkUnit]; omega
                · simp [linkUnit, h]
              have := DyAdd (y - linkUnit i j) i j
              rw [← e] at this
              linarith
            set I : TTState n → ℝ := fun s => ∑ i, ∑ j, (if 0 < s.2 i j then (s.2 i j : ℝ) / τ i j *
                (if 0 < φ i j * q i j then 0 else -1) else 0) with hI
            have hInner : ∀ s ∈ St, ∑ t ∈ St, R s t * Dy t.2 - Dy s.2 * ∑ t ∈ St, R s t = I s := by
              intro s hs
              have e1 : ∑ t ∈ St, R s t * Dy t.2 - Dy s.2 * ∑ t ∈ St, R s t =
                  ∑ t ∈ St, R s t * (fun t : TTState n => Dy t.2 - Dy s.2) t := by
                rw [mul_sum, ← sum_sub_distrib]
                refine Finset.sum_congr rfl (fun t _ => ?_); ring
              rw [e1, FWD s hs]
              refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
              have hdep : (if 0 < s.1 i then φ i j * q i j * (Dy (s.2 + linkUnit i j) - Dy s.2) else 0) = 0 := by
                split_ifs with h
                · rw [DyAdd]
                  by_cases hl : 0 < φ i j * q i j
                  · simp [hl]
                  · have : φ i j * q i j = 0 := le_antisymm (not_lt.mp hl) (mul_nonneg (hφ i j) (hq i j).1)
                    rw [this]; ring
                · rfl
              simp only
              rw [hdep, zero_add]
              by_cases h1 : 0 < s.2 i j
              · rw [if_pos h1, if_pos h1, DySub _ _ _ h1]; split_ifs <;> ring
              · rw [if_neg h1, if_neg h1]
            have hIle : ∀ s ∈ St, I s ≤ 0 := by
              intro s _
              apply Finset.sum_nonpos; intro i _; apply Finset.sum_nonpos; intro j _
              split_ifs with h1 h2
              · simp
              · have : 0 ≤ (s.2 i j : ℝ) / τ i j := div_nonneg (Nat.cast_nonneg _) (hτ i j).le
                linarith
              · rfl
            have htot : ∑ s ∈ St, π s * I s = 0 := by
              have := GEN (fun t => Dy t.2)
              have h2 : ∑ s ∈ St, π s * I s = ∑ s ∈ St, π s * ∑ t ∈ St, R s t * Dy t.2 -
                  ∑ s ∈ St, π s * Dy s.2 * ∑ t ∈ St, R s t := by
                rw [← sum_sub_distrib]
                refine Finset.sum_congr rfl (fun s hs => ?_)
                rw [← hInner s hs]; ring
              rw [h2, this, sub_self]
            have hzero := (Finset.sum_eq_zero_iff_of_nonpos (fun s hs =>
              mul_nonpos_of_nonneg_of_nonpos (hπ.1 s) (hIle s hs))).mp htot
            intro s hs i j hd hy
            have hlt : I s < 0 := by
              have hterm : (if 0 < s.2 i j then (s.2 i j : ℝ) / τ i j *
                  (if 0 < φ i j * q i j then 0 else -1) else 0) < 0 := by
                rw [if_pos hy, if_neg hd]
                have : 0 < (s.2 i j : ℝ) / τ i j := div_pos (by exact_mod_cast hy) (hτ i j)
                linarith
              have hrow : ∀ a, (∑ b, (if 0 < s.2 a b then (s.2 a b : ℝ) / τ a b *
                  (if 0 < φ a b * q a b then 0 else -1) else 0)) ≤ 0 := by
                intro a; apply Finset.sum_nonpos; intro b _
                split_ifs with h1 h2
                · simp
                · have : 0 ≤ (s.2 a b : ℝ) / τ a b := div_nonneg (Nat.cast_nonneg _) (hτ a b).le
                  linarith
                · rfl
              have hrowi : (∑ b, (if 0 < s.2 i b then (s.2 i b : ℝ) / τ i b *
                  (if 0 < φ i b * q i b then 0 else -1) else 0)) < 0 := by
                rw [← Finset.add_sum_erase univ _ (mem_univ j)]
                have : (∑ b ∈ univ.erase j, (if 0 < s.2 i b then (s.2 i b : ℝ) / τ i b *
                    (if 0 < φ i b * q i b then 0 else -1) else 0)) ≤ 0 := by
                  apply Finset.sum_nonpos; intro b _
                  split_ifs with h1 h2
                  · simp
                  · have : 0 ≤ (s.2 i b : ℝ) / τ i b := div_nonneg (Nat.cast_nonneg _) (hτ i b).le
                    linarith
                  · rfl
                linarith
              show (∑ a, _) < 0
              rw [← Finset.add_sum_erase univ _ (mem_univ i)]
              have : (∑ a ∈ univ.erase i, (∑ b, (if 0 < s.2 a b then (s.2 a b : ℝ) / τ a b *
                  (if 0 < φ a b * q a b then 0 else -1) else 0))) ≤ 0 :=
                Finset.sum_nonpos (fun a _ => hrow a)
              linarith
            have := hzero s hs
            rcases mul_eq_zero.mp this with h | h
            · exact h
            · linarith
          have EXR : 0 < M₀ → ∃ r : Fin n → ℝ, (∀ i, 0 < r i) ∧ IsTraffic φ q r := by
            intro hM0
            have GEN : ∀ F : TTState n → ℝ, ∑ s ∈ St, π s * (∑ t ∈ St, R s t * F t - F s * ∑ t ∈ St, R s t) = 0 := by
              intro F
              have h1 : ∑ s ∈ St, π s * ∑ t ∈ St, R s t * F t = ∑ t ∈ St, (∑ s ∈ St, π s * R s t) * F t := by
                simp only [mul_sum, sum_mul]
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun s _ => ?_)); ring
              have h2 : ∑ t ∈ St, (∑ s ∈ St, π s * R s t) * F t = ∑ t ∈ St, π t * (F t * ∑ s ∈ St, R t s) := by
                refine Finset.sum_congr rfl (fun t ht => ?_)
                rw [← hbal t ht]; ring
              simp only [mul_sub, sum_sub_distrib, h1, h2, sub_self]
            have DIFF : ∀ s ∈ St, ∀ F : TTState n → ℝ, ∑ t ∈ St, R s t * F t - F s * ∑ t ∈ St, R s t =
                ∑ i, ∑ j, ((if 0 < s.1 i then φ i j * q i j * (F (s.1 - Pi.single i 1, s.2 + linkUnit i j) - F s) else 0) +
                  (if 0 < s.2 i j then (s.2 i j : ℝ) / τ i j * (F (s.1 + Pi.single j 1, s.2 - linkUnit i j) - F s) else 0)) := by
              intro s hs F
              have h1 := FWD s hs (fun _ => 1)
              simp only [mul_one] at h1
              rw [FWD s hs F, h1, mul_sum, ← sum_sub_distrib]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [mul_sum, ← sum_sub_distrib]
              refine Finset.sum_congr rfl (fun j _ => ?_)
              split_ifs <;> ring
            have IY : ∀ s ∈ St, ∀ a b, ∑ t ∈ St, R s t * (fun t : TTState n => (t.2 a b : ℝ)) t -
                (fun t : TTState n => (t.2 a b : ℝ)) s * ∑ t ∈ St, R s t =
                (if 0 < s.1 a then φ a b * q a b else 0) - (s.2 a b : ℝ) / τ a b := by
              intro s hs a b
              rw [DIFF s hs]
              have pw : ∀ i j, ((if 0 < s.1 i then φ i j * q i j * (((s.2 + linkUnit i j) a b : ℕ) - (s.2 a b : ℝ)) else 0) +
                  (if 0 < s.2 i j then (s.2 i j : ℝ) / τ i j * (((s.2 - linkUnit i j) a b : ℕ) - (s.2 a b : ℝ)) else 0)) =
                  if i = a then (if j = b then (if 0 < s.1 a then φ a b * q a b else 0) - (s.2 a b : ℝ) / τ a b else 0) else 0 := by
                intro i j
                by_cases h : i = a ∧ j = b
                · obtain ⟨rfl, rfl⟩ := h
                  simp only [Pi.add_apply, Pi.sub_apply, linkUnit, and_self, if_true]
                  by_cases hy : 0 < s.2 i j
                  · rw [if_pos hy]
                    push_cast [Nat.cast_sub (show 1 ≤ s.2 i j by omega)]
                    split_ifs <;> ring
                  · rw [if_neg hy]
                    have : (s.2 i j : ℝ) = 0 := by exact_mod_cast (by omega : s.2 i j = 0)
                    push_cast; rw [this]; split_ifs <;> ring
                · have h' : ¬(a = i ∧ b = j) := fun h2 => h ⟨h2.1.symm, h2.2.symm⟩
                  simp only [Pi.add_apply, Pi.sub_apply, linkUnit, h', if_false, add_zero, Nat.sub_zero, sub_self, mul_zero,
                    ite_self]
                  by_cases ha : i = a
                  · have hb : j ≠ b := fun hb => h ⟨ha, hb⟩
                    simp [ha, hb]
                  · simp [ha]
              simp only [pw]
              simp
            have IX : ∀ s ∈ St, ∀ b, ∑ t ∈ St, R s t * (fun t : TTState n => (t.1 b : ℝ)) t -
                (fun t : TTState n => (t.1 b : ℝ)) s * ∑ t ∈ St, R s t =
                -(if 0 < s.1 b then ∑ j, φ b j * q b j else 0) + ∑ i, (s.2 i b : ℝ) / τ i b := by
              intro s hs b
              rw [DIFF s hs]
              have pw : ∀ i j, ((if 0 < s.1 i then φ i j * q i j * ((((s.1 - Pi.single i (1:ℕ) : Fin n → ℕ) b : ℕ) : ℝ) - (s.1 b : ℝ)) else 0) +
                  (if 0 < s.2 i j then (s.2 i j : ℝ) / τ i j * ((((s.1 + Pi.single j (1:ℕ) : Fin n → ℕ) b : ℕ) : ℝ) - (s.1 b : ℝ)) else 0)) =
                  (if i = b then -(if 0 < s.1 b then φ b j * q b j else 0) else 0) +
                    (if j = b then (s.2 i b : ℝ) / τ i b else 0) := by
                intro i j
                congr 1
                · by_cases hi : i = b
                  · subst hi
                    by_cases h0 : 0 < s.1 i
                    · simp only [if_pos h0, if_true, Pi.sub_apply, Pi.single_eq_same]
                      push_cast [Nat.cast_sub (show 1 ≤ s.1 i by omega)]
                      ring
                    · simp [h0]
                  · simp [Pi.single_apply, Ne.symm hi, hi]
                · by_cases hj : j = b
                  · subst hj
                    by_cases h0 : 0 < s.2 i j
                    · simp [h0]
                    · have : (s.2 i j : ℝ) = 0 := by exact_mod_cast (by omega : s.2 i j = 0)
                      simp [h0, this]
                  · simp [Pi.single_apply, Ne.symm hj, hj]
              rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => pw i j))]
              simp only [sum_add_distrib]
              rw [Finset.sum_comm (f := fun i j => if j = b then (s.2 i b : ℝ) / τ i b else 0)]
              skip
              congr 1
              · by_cases h0 : 0 < s.1 b
                · simp [h0, Finset.sum_neg_distrib]
                · simp [h0]
              · rw [Finset.sum_eq_single b (fun y _ hy => by simp [hy]) (by simp)]
                simp
            set a : Fin n → ℝ := fun i => ∑ s ∈ St, π s * (if 0 < s.1 i then 1 else 0) with ha
            set E : Fin n → Fin n → ℝ := fun i j => ∑ s ∈ St, π s * (s.2 i j : ℝ) with hE
            have hY : ∀ i j, E i j / τ i j = φ i j * q i j * a i := by
              intro i j
              have := GEN (fun t => (t.2 i j : ℝ))
              rw [Finset.sum_congr rfl (fun s hs => by rw [IY s hs i j])] at this
              simp only [mul_sub, sum_sub_distrib, sub_eq_zero] at this
              simp only [hE, ha, sum_div, mul_sum]
              have e1 : ∑ s ∈ St, π s * (s.2 i j : ℝ) / τ i j = ∑ s ∈ St, π s * ((s.2 i j : ℝ) / τ i j) :=
                Finset.sum_congr rfl (fun _ _ => by ring)
              rw [e1, ← this]
              refine Finset.sum_congr rfl (fun s _ => ?_)
              split_ifs <;> ring
            have hX : ∀ b, a b * ∑ j, φ b j * q b j = ∑ i, E i b / τ i b := by
              intro b
              have := GEN (fun t => (t.1 b : ℝ))
              rw [Finset.sum_congr rfl (fun s hs => by rw [IX s hs b])] at this
              simp only [mul_add, sum_add_distrib, mul_neg, sum_neg_distrib, neg_add_eq_zero] at this
              simp only [hE, ha, sum_mul, sum_div]
              rw [Finset.sum_comm (s := Finset.univ)]
              skip
              have e2 : ∀ s : TTState n, π s * (if 0 < s.1 b then 1 else 0) * ∑ j, φ b j * q b j =
                  π s * (if 0 < s.1 b then ∑ j, φ b j * q b j else 0) := by
                intro s; split_ifs <;> ring
              simp only [e2]
              rw [this]
              refine Finset.sum_congr rfl (fun s _ => ?_)
              rw [mul_sum]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              ring
            have htr : IsTraffic φ q a := by
              intro i
              rw [hX i]
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [hY j i]; ring
            have anonneg : ∀ i, 0 ≤ a i := by
              intro i
              refine Finset.sum_nonneg (fun s _ => mul_nonneg (hπ.1 s) ?_)
              split_ifs <;> norm_num
            -- some positive coordinate
            obtain ⟨s0, hs0, hπs0⟩ : ∃ s ∈ St.filter (fun s => ∑ i, s.1 i = M₀), 0 < π s := by
              by_contra hcon
              push_neg at hcon
              have : availableProb m π M₀ ≤ 0 := Finset.sum_nonpos hcon
              linarith
            rw [mem_filter] at hs0
            obtain ⟨i0, hi0⟩ : ∃ i, 0 < s0.1 i := by
              by_contra hcon
              push_neg at hcon
              have : ∑ i, s0.1 i = 0 := Finset.sum_eq_zero (fun i _ => by have := hcon i; omega)
              omega
            have ai0 : 0 < a i0 := by
              have := Finset.single_le_sum (f := fun s => π s * (if 0 < s.1 i0 then (1:ℝ) else 0))
                (fun s _ => mul_nonneg (hπ.1 s) (by split_ifs <;> norm_num)) hs0.1
              simp only [if_pos hi0, mul_one] at this
              show 0 < ∑ s ∈ St, π s * (if 0 < s.1 i0 then 1 else 0)
              linarith
            have prop : ∀ k, a k = 0 → ∀ j, 0 < φ j k * q j k → a j = 0 := by
              intro k hk j hj
              have h := htr k
              rw [hk, zero_mul] at h
              have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by
                have := anonneg j; have := hφ j k; have := (hq j k).1; positivity)).1 h j (mem_univ j)
              rw [mul_assoc] at this
              rcases mul_eq_zero.1 this with h1 | h1
              · exact h1
              · linarith
            refine ⟨a, fun k => ?_, htr⟩
            by_contra hk
            have hk0 : a k = 0 := le_antisymm (not_lt.1 hk) (anonneg k)
            have key : ∀ x, Relation.ReflTransGen (fun u v => u ≠ v ∧ 0 < φ u v * q u v) x k → a x = 0 := by
              intro x hx
              induction hx using Relation.ReflTransGen.head_induction_on with
              | refl => exact hk0
              | head hxy _ ih => exact prop _ ih _ hxy.2
            have : a i0 = 0 := key i0 (hconn i0 k)
            linarith
          have UNIQ : ∀ r : Fin n → ℝ, (∀ i, 0 < r i) → IsTraffic φ q r → ∃ H : ℝ, ∀ s ∈ St,
              π s = H * ((∏ i, r i ^ s.1 i) * ∏ i, ∏ j, (r i * φ i j * q i j * τ i j) ^ s.2 i j / ((s.2 i j).factorial : ℝ)) := by
            classical
            intro r hr htr
            let pt : TTState n → ℝ := fun s => (∏ i, r i ^ s.1 i) * ∏ i, ∏ j, (r i * φ i j * q i j * τ i j) ^ s.2 i j / ((s.2 i j).factorial : ℝ)
            have hPT : ∀ s ∈ St, pt s * ∑ t ∈ St, R s t = ∑ t ∈ St, pt t * R t s := PTB r hr htr
            suffices hsuff : ∃ H : ℝ, ∀ s ∈ St, π s = H * pt s from hsuff
            -- basic rate facts
            let T : TTState n → TTState n → Fin n → Fin n → ℝ := fun s t i j =>
              (if 0 < s.1 i ∧ t = (s.1 - Pi.single i 1, s.2 + linkUnit i j) then φ i j * toTTPolicy q s i j else 0) +
                (if 0 < s.2 i j ∧ t = (s.1 + Pi.single j 1, s.2 - linkUnit i j) then (s.2 i j : ℝ) / τ i j else 0)
            have hRT : ∀ s t, R s t = ∑ i, ∑ j, T s t i j := fun s t => rfl
            have Tnn : ∀ s t i j, 0 ≤ T s t i j := by
              intro s t i j
              simp only [T]
              apply add_nonneg
              · split_ifs
                · simp only [toTTPolicy, toPolicy]; split_ifs
                  · exact mul_nonneg (hφ i j) (hq i j).1
                  · simp
                · exact le_refl _
              · split_ifs
                · exact div_nonneg (Nat.cast_nonneg _) (hτ i j).le
                · exact le_refl _
            have Rnn : ∀ s t, 0 ≤ R s t := fun s t => by
              rw [hRT]; exact sum_nonneg fun i _ => sum_nonneg fun j _ => Tnn s t i j
            have Rge : ∀ s t i j, T s t i j ≤ R s t := by
              intro s t i j
              rw [hRT]
              refine le_trans ?_ (single_le_sum (f := fun i => ∑ j, T s t i j) (fun i _ => sum_nonneg fun j _ => Tnn s t i j) (mem_univ i))
              exact single_le_sum (f := fun j => T s t i j) (fun j _ => Tnn s t i j) (mem_univ j)
            have Rdep : ∀ s : TTState n, ∀ i j, 0 < s.1 i → 0 < φ i j * q i j → 0 < R s (s.1 - Pi.single i 1, s.2 + linkUnit i j) := by
              intro s i j hi hL
              refine lt_of_lt_of_le ?_ (Rge s _ i j)
              dsimp only [T]
              rw [if_pos ⟨hi, rfl⟩]
              have : toTTPolicy q s i j = q i j := by simp [toTTPolicy, toPolicy, hi]
              rw [this]
              have : 0 ≤ (if 0 < s.2 i j ∧ ((s.1 - Pi.single i 1, s.2 + linkUnit i j) : TTState n) = (s.1 + Pi.single j 1, s.2 - linkUnit i j) then (s.2 i j : ℝ) / τ i j else 0) := by
                split_ifs
                · exact div_nonneg (Nat.cast_nonneg _) (hτ i j).le
                · exact le_refl _
              linarith
            have Rarr : ∀ s : TTState n, ∀ i j, 0 < s.2 i j → 0 < R s (s.1 + Pi.single j 1, s.2 - linkUnit i j) := by
              intro s i j hi
              refine lt_of_lt_of_le ?_ (Rge s _ i j)
              dsimp only [T]
              rw [if_pos (And.intro hi rfl)]
              have : 0 ≤ (if 0 < s.1 i ∧ ((s.1 + Pi.single j 1, s.2 - linkUnit i j) : TTState n) = (s.1 - Pi.single i 1, s.2 + linkUnit i j) then φ i j * toTTPolicy q s i j else 0) := by
                split_ifs
                · simp only [toTTPolicy, toPolicy]; split_ifs
                  · exact mul_nonneg (hφ i j) (hq i j).1
                  · simp
                · exact le_refl _
              have : 0 < (s.2 i j : ℝ) / τ i j := div_pos (by exact_mod_cast hi) (hτ i j)
              linarith
            -- the closed class
            let C : Finset (TTState n) := St.filter (fun s => ∀ i j, ¬ (0 < φ i j * q i j) → s.2 i j = 0)
            have ptpos : ∀ s ∈ C, 0 < pt s := by
              intro s hs
              rw [mem_filter] at hs
              apply mul_pos
              · exact prod_pos fun i _ => pow_pos (hr i) _
              · refine prod_pos fun i _ => prod_pos fun j _ => ?_
                by_cases hL : 0 < φ i j * q i j
                · apply div_pos _ (by exact_mod_cast Nat.factorial_pos _)
                  apply pow_pos
                  have : r i * φ i j * q i j * τ i j = r i * (φ i j * q i j) * τ i j := by ring
                  rw [this]; exact mul_pos (mul_pos (hr i) hL) (hτ i j)
                · rw [hs.2 i j hL]; simp
            have ptzero : ∀ s ∈ St, s ∉ C → pt s = 0 ∧ π s = 0 := by
              intro s hs hC
              rw [mem_filter] at hC
              push_neg at hC
              obtain ⟨i, j, hL, hy⟩ := hC hs
              have hy' : 0 < s.2 i j := Nat.pos_of_ne_zero hy
              refine ⟨?_, DEAD s hs i j (not_lt.mpr hL) hy'⟩
              have h0 : φ i j * q i j = 0 := le_antisymm hL (mul_nonneg (hφ i j) (hq i j).1)
              have hw : r i * φ i j * q i j * τ i j = 0 := by
                have : r i * φ i j * q i j * τ i j = r i * (φ i j * q i j) * τ i j := by ring
                rw [this, h0]; ring
              show (∏ i, r i ^ s.1 i) * ∏ i, ∏ j, (r i * φ i j * q i j * τ i j) ^ s.2 i j / ((s.2 i j).factorial : ℝ) = 0
              have hf : (r i * φ i j * q i j * τ i j) ^ s.2 i j / ((s.2 i j).factorial : ℝ) = 0 := by
                rw [hw, zero_pow hy]; simp
              have hp : ∏ j, (r i * φ i j * q i j * τ i j) ^ s.2 i j / ((s.2 i j).factorial : ℝ) = 0 :=
                Finset.prod_eq_zero (mem_univ j) hf
              exact mul_eq_zero.mpr (Or.inr (Finset.prod_eq_zero (mem_univ i) hp))
            by_cases hCne : C.Nonempty
            swap
            · refine ⟨0, fun s hs => ?_⟩
              have : s ∉ C := fun h => hCne ⟨s, h⟩
              rw [(ptzero s hs this).2]; ring
            obtain ⟨s₀, hs₀C, hmax⟩ := Finset.exists_max_image C (fun s => π s / pt s) hCne
            have hs₀ : s₀ ∈ St := (mem_filter.mp hs₀C).1
            set H := π s₀ / pt s₀ with hH
            refine ⟨H, ?_⟩
            let g : TTState n → ℝ := fun s => H * pt s - π s
            have gnn : ∀ s ∈ St, 0 ≤ g s := by
              intro s hs
              by_cases hC : s ∈ C
              · have h1 := hmax s hC
                have h2 := ptpos s hC
                rw [div_le_iff₀ h2] at h1
                simp only [g]; linarith
              · obtain ⟨h1, h2⟩ := ptzero s hs hC
                simp only [g, h1, h2]; ring_nf; exact le_refl _
            have gbal : ∀ s ∈ St, g s * ∑ t ∈ St, R s t = ∑ t ∈ St, g t * R t s := by
              intro s hs
              have e1 := hPT s hs
              have e2 := hbal s hs
              calc g s * ∑ t ∈ St, R s t = H * (pt s * ∑ t ∈ St, R s t) - π s * ∑ t ∈ St, R s t := by
                    simp only [g]; ring
                _ = H * ∑ t ∈ St, pt t * R t s - ∑ t ∈ St, π t * R t s := by rw [e1, e2]
                _ = ∑ t ∈ St, g t * R t s := by
                    rw [mul_sum, ← sum_sub_distrib]
                    exact sum_congr rfl fun t _ => by simp only [g]; ring
            have gzero : ∀ s ∈ St, g s = 0 → ∀ t ∈ St, 0 < R t s → g t = 0 := by
              intro s hs hg t ht hRts
              have h := gbal s hs
              rw [hg, zero_mul, eq_comm] at h
              have := (Finset.sum_eq_zero_iff_of_nonneg (fun u hu => mul_nonneg (gnn u hu) (Rnn u s))).mp h t ht
              rcases mul_eq_zero.mp this with h' | h'
              · exact h'
              · linarith
            have g0 : g s₀ = 0 := by
              have := (ptpos s₀ hs₀C).ne'
              simp only [g, hH]; field_simp; ring
            let Step : TTState n → TTState n → Prop := fun a b => a ∈ St ∧ b ∈ St ∧ 0 < R a b
            have prop : ∀ t, Relation.ReflTransGen Step t s₀ → g t = 0 := by
              intro t ht
              induction ht using Relation.ReflTransGen.head_induction_on with
              | refl => exact g0
              | head hab _ ih => exact gzero _ hab.2.1 ih _ hab.1 hab.2.2
            have IRR : ∀ t ∈ C, Relation.ReflTransGen Step t s₀ := by
              rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i0⟩⟩
              · intro t _
                have : t = s₀ := Prod.ext (funext fun i => (IsEmpty.false i).elim) (funext fun i => (IsEmpty.false i).elim)
                rw [this]
              have addsub : ∀ (z : Fin n → ℕ) (a : Fin n), z + Pi.single a 1 - Pi.single a 1 = z := by
                intro z a; funext k; simp
              have subadd : ∀ (x : Fin n → ℕ) (a : Fin n), 0 < x a → x - Pi.single a 1 + Pi.single a 1 = x := by
                intro x a ha; funext k
                by_cases hk : k = a
                · subst hk; simp; omega
                · simp [hk]
              have addsubL : ∀ (w : Fin n → Fin n → ℕ) (a b : Fin n), w + linkUnit a b - linkUnit a b = w := by
                intro w a b; funext c d; simp
              have subaddL : ∀ (w : Fin n → Fin n → ℕ) (a b : Fin n), 0 < w a b → w - linkUnit a b + linkUnit a b = w := by
                intro w a b h; funext c d
                by_cases hk : c = a ∧ d = b
                · obtain ⟨rfl, rfl⟩ := hk; simp [linkUnit]; omega
                · simp [linkUnit, hk]
              have stepDep : ∀ s ∈ St, ∀ i j t, 0 < s.1 i → 0 < φ i j * q i j →
                  ((s.1 - Pi.single i 1, s.2 + linkUnit i j) : TTState n) = t → Step s t := by
                rintro s hs i j t hi hL rfl; exact ⟨hs, memDep s hs i j hi, Rdep s i j hi hL⟩
              have stepArr : ∀ s ∈ St, ∀ i j t, 0 < s.2 i j →
                  ((s.1 + Pi.single j 1, s.2 - linkUnit i j) : TTState n) = t → Step s t := by
                rintro s hs i j t hi rfl; exact ⟨hs, memArr s hs i j hi, Rarr s i j hi⟩
              have REACHMEM : ∀ a b, Relation.ReflTransGen Step a b → a ∈ St → b ∈ St := by
                intro a b h ha
                induction h with
                | refl => exact ha
                | tail _ hst _ => exact hst.2.1
              have memShift : ∀ (z : Fin n → ℕ) w a b, ((z + Pi.single a 1, w) : TTState n) ∈ St →
                  ((z + Pi.single b 1, w) : TTState n) ∈ St := by
                intro z w a b h
                rw [memSt] at h ⊢
                simp only at h ⊢
                rw [sumSingle] at h ⊢; exact h
              have MOVE1 : ∀ (z : Fin n → ℕ) w a b, ((z + Pi.single a 1, w) : TTState n) ∈ St → 0 < φ a b * q a b →
                  Relation.ReflTransGen Step (z + Pi.single a 1, w) (z + Pi.single b 1, w) := by
                intro z w a b h hL
                have s1 : Step (z + Pi.single a 1, w) (z, w + linkUnit a b) :=
                  stepDep _ h a b _ (by simp) hL (Prod.ext (addsub z a) rfl)
                have s2 : Step (z, w + linkUnit a b) (z + Pi.single b 1, w) :=
                  stepArr _ s1.2.1 a b _ (by simp [linkUnit]) (Prod.ext rfl (addsubL w a b))
                exact Relation.ReflTransGen.head s1 (Relation.ReflTransGen.single s2)
              have PATH : ∀ a b, Relation.ReflTransGen (fun a b => a ≠ b ∧ 0 < φ a b * q a b) a b →
                  ∀ (z : Fin n → ℕ) w, ((z + Pi.single a 1, w) : TTState n) ∈ St →
                    Relation.ReflTransGen Step (z + Pi.single a 1, w) (z + Pi.single b 1, w) := by
                intro a b hab
                induction hab with
                | refl => intro z w _; exact Relation.ReflTransGen.refl
                | tail _ hcd ih =>
                  intro z w h
                  exact (ih z w h).trans (MOVE1 z w _ _ (memShift z w a _ h) hcd.2)
              have CONC : ∀ d, ∀ (x : Fin n → ℕ) (w : Fin n → Fin n → ℕ), ∑ k, x k - x i0 = d → ((x, w) : TTState n) ∈ St →
                  Relation.ReflTransGen Step (x, w) (Pi.single i0 (∑ k, x k), w) ∧
                    Relation.ReflTransGen Step (Pi.single i0 (∑ k, x k), w) (x, w) := by
                intro d
                induction d using Nat.strong_induction_on with
                | _ d ih =>
                intro x w hd hmem
                by_cases hall : ∀ j, j ≠ i0 → x j = 0
                · have : Pi.single i0 (∑ k, x k) = x := by
                    funext k
                    by_cases hk : k = i0
                    · subst hk; simp only [Pi.single_eq_same]
                      exact Finset.sum_eq_single k (fun j _ hj => hall j hj) (by simp)
                    · simp [hk, hall k hk]
                  rw [this]; exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
                · push_neg at hall
                  obtain ⟨j, hj, hxj⟩ := hall
                  have hxj' : 0 < x j := Nat.pos_of_ne_zero hxj
                  have hsum : ∑ k, (x - Pi.single j 1 + Pi.single i0 1 : Fin n → ℕ) k = ∑ k, x k := by
                    rw [sumSingle, sumSub x j hxj']
                  have hi0 : (x - Pi.single j 1 + Pi.single i0 1 : Fin n → ℕ) i0 = x i0 + 1 := by
                    simp [Pi.single_apply, Ne.symm hj]
                  have hle : x i0 + x j ≤ ∑ k, x k := by
                    have := Finset.sum_le_sum_of_subset (f := x) (Finset.subset_univ {i0, j})
                    rwa [Finset.sum_pair (Ne.symm hj)] at this
                  have hd' : ∑ k, (x - Pi.single j 1 + Pi.single i0 1 : Fin n → ℕ) k - (x - Pi.single j 1 + Pi.single i0 1 : Fin n → ℕ) i0 < d := by
                    rw [hsum, hi0]; omega
                  have hxm : ((x - Pi.single j 1 + Pi.single j 1, w) : TTState n) ∈ St := by
                    rw [subadd x j hxj']; exact hmem
                  have hmem' : ((x - Pi.single j 1 + Pi.single i0 1, w) : TTState n) ∈ St := memShift _ w j i0 hxm
                  obtain ⟨h1, h2⟩ := ih _ hd' _ w rfl hmem'
                  rw [hsum] at h1 h2
                  have p1 := PATH j i0 (hconn j i0) (x - Pi.single j 1) w hxm
                  have p2 := PATH i0 j (hconn i0 j) (x - Pi.single j 1) w hmem'
                  rw [subadd x j hxj'] at p1 p2
                  exact ⟨p1.trans h1, h2.trans p2⟩
              have exPos : ∀ y : Fin n → Fin n → ℕ, ∑ i, ∑ j, y i j ≠ 0 → ∃ i j, 0 < y i j := by
                intro y hy
                by_contra hne
                push_neg at hne
                exact hy (Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by have := hne i j; omega)
              have yzero : ∀ y : Fin n → Fin n → ℕ, ∑ i, ∑ j, y i j = 0 → y = 0 := by
                intro y hy; funext a b
                simp only [Finset.sum_eq_zero_iff, mem_univ, true_implies] at hy
                exact hy a b
              have DRAIN : ∀ k, ∀ s ∈ St, ∑ i, ∑ j, s.2 i j = k → ∃ x' : Fin n → ℕ, Relation.ReflTransGen Step s (x', 0) := by
                intro k
                induction k with
                | zero =>
                  rintro ⟨x, y⟩ _ hk
                  refine ⟨x, ?_⟩
                  have := yzero y hk
                  subst this; exact Relation.ReflTransGen.refl
                | succ k ih =>
                  intro s hs hk
                  obtain ⟨i, j, hij⟩ := exPos s.2 (by omega)
                  have st := stepArr s hs i j _ hij rfl
                  have hk' : ∑ a, ∑ b, (s.2 - linkUnit i j) a b = k := by
                    have := sumLinkSub s.2 i j hij; omega
                  obtain ⟨x', hx'⟩ := ih _ st.2.1 hk'
                  exact ⟨x', Relation.ReflTransGen.head st hx'⟩
              have BUILD : ∀ k, ∀ s ∈ C, ∑ i, ∑ j, s.2 i j = k →
                  Relation.ReflTransGen Step (Pi.single i0 m, (0 : Fin n → Fin n → ℕ)) s := by
                intro k
                induction k with
                | zero =>
                  rintro ⟨x, y⟩ hs hk
                  have := yzero y hk
                  subst this
                  have hsSt := (mem_filter.mp hs).1
                  have hsum : ∑ k, x k = m := by have := (memSt _).mp hsSt; simpa using this
                  have c2 := (CONC _ x 0 rfl hsSt).2
                  rw [hsum] at c2; exact c2
                | succ k ih =>
                  intro s hs hk
                  have hsSt := (mem_filter.mp hs).1
                  obtain ⟨i, j, hij⟩ := exPos s.2 (by omega)
                  have hL : 0 < φ i j * q i j := by
                    by_contra h; have := (mem_filter.mp hs).2 i j h; omega
                  have hs'St := memArr' s hsSt i j hij
                  have hs'C : ((s.1 + Pi.single i 1, s.2 - linkUnit i j) : TTState n) ∈ C := by
                    refine mem_filter.mpr ⟨hs'St, fun a b hab => ?_⟩
                    have := (mem_filter.mp hs).2 a b hab
                    show (s.2 - linkUnit i j) a b = 0
                    simp [this]
                  have hk' : ∑ a, ∑ b, (s.2 - linkUnit i j) a b = k := by
                    have := sumLinkSub s.2 i j hij; omega
                  have r1 := ih _ hs'C hk'
                  have st : Step (s.1 + Pi.single i 1, s.2 - linkUnit i j) s :=
                    stepDep _ hs'St i j s (by simp) hL (Prod.ext (addsub s.1 i) (subaddL s.2 i j hij))
                  exact r1.tail st
              intro t ht
              have htSt := (mem_filter.mp ht).1
              obtain ⟨x', hx'⟩ := DRAIN _ t htSt rfl
              have hx'St : ((x', 0) : TTState n) ∈ St := REACHMEM _ _ hx' htSt
              have hsum : ∑ k, x' k = m := by have := (memSt _).mp hx'St; simpa using this
              have c1 := (CONC _ x' 0 rfl hx'St).1
              rw [hsum] at c1
              exact hx'.trans (c1.trans (BUILD _ s₀ hs₀C rfl))
            intro s hs
            by_cases hC : s ∈ C
            · have := prop s (IRR s hC)
              simp only [g] at this; linarith
            · obtain ⟨h1, h2⟩ := ptzero s hs hC
              rw [h1, h2]; ring
          -- conditional law
          have memStates : ∀ (N : ℕ) (x : Fin n → ℕ), x ∈ states n N ↔ ∑ i, x i = N := by
            intro N x
            rw [states, mem_filter]
            constructor
            · exact fun h => h.2
            · intro h
              refine ⟨?_, h⟩
              rw [Fintype.mem_piFinset]; intro i; rw [mem_range]
              have := single_le_sum (f := fun i => x i) (fun _ _ => Nat.zero_le _) (mem_univ i)
              omega
          have availEq : availableProb m π M₀ = ∑ x ∈ states n M₀, ∑ s ∈ St.filter (fun s => s.1 = x), π s := by
            rw [availableProb, ← Finset.sum_fiberwise_of_maps_to (s := St.filter (fun s : TTState n => ∑ i, s.1 i = M₀))
              (t := states n M₀) (g := Prod.fst)]
            · refine Finset.sum_congr rfl (fun x hx => ?_)
              rw [Finset.filter_filter]
              congr 1
              ext s
              simp only [mem_filter]
              constructor
              · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
              · rintro ⟨h1, h3⟩; exact ⟨h1, by rw [h3]; exact (memStates M₀ x).1 hx, h3⟩
            · intro s hs
              rw [mem_filter] at hs
              exact (memStates M₀ s.1).2 hs.2
          have hπ0 : ∀ s, 0 ≤ π s := hπ.1
          have condNN : ∀ x, 0 ≤ condNodeLaw m π M₀ x := by
            intro x
            unfold condNodeLaw
            split_ifs
            · exact div_nonneg (Finset.sum_nonneg (fun s _ => hπ0 s)) hM.le
            · exact le_refl _
          have condOff : ∀ x, x ∉ states n M₀ → condNodeLaw m π M₀ x = 0 := by
            intro x hx; unfold condNodeLaw; rw [if_neg hx]
          have condSum : ∑ x ∈ states n M₀, condNodeLaw m π M₀ x = 1 := by
            unfold condNodeLaw
            rw [Finset.sum_congr rfl (fun x hx => if_pos hx), ← Finset.sum_div, ← availEq]
            exact div_self hM.ne'
          have COND : ∀ r : Fin n → ℝ, (∀ i, 0 < r i) → IsTraffic φ q r →
              condNodeLaw m π M₀ = productForm (fun j y => r j ^ y) M₀ := by
            intro r hr htr
            obtain ⟨H, hH⟩ := UNIQ r hr htr
            set P : (Fin n → ℕ) → ℝ := fun x => ∏ i, r i ^ x i with hP
            set Q : (Fin n → Fin n → ℕ) → ℝ := fun y => ∏ i, ∏ j, (r i * φ i j * q i j * τ i j) ^ y i j / ((y i j).factorial : ℝ) with hQ
            set K : (Fin n → ℕ) → ℝ := fun x => ∑ s ∈ St.filter (fun s => s.1 = x), Q s.2 with hK
            have fib : ∀ x, ∑ s ∈ St.filter (fun s => s.1 = x), π s = H * P x * K x := by
              intro x
              simp only [hK, mul_sum]
              refine Finset.sum_congr rfl (fun s hs => ?_)
              rw [mem_filter] at hs
              rw [hH s hs.1, hs.2]; simp only [hP, hQ]; ring
            have Kinv : ∀ x x', ∑ i, x i = ∑ i, x' i → K x = K x' := by
              intro x x' hxx
              simp only [hK]
              refine Finset.sum_nbij' (fun s => (x', s.2)) (fun s => (x, s.2)) ?_ ?_ ?_ ?_ ?_
              · intro s hs
                simp only [mem_filter, coe_filter, Set.mem_setOf_eq] at hs ⊢
                obtain ⟨h1, h2⟩ := hs
                refine ⟨?_, trivial⟩
                rw [memSt] at h1 ⊢; rw [h2] at h1; simp only; omega
              · intro s hs
                simp only [mem_filter, coe_filter, Set.mem_setOf_eq] at hs ⊢
                obtain ⟨h1, h2⟩ := hs
                refine ⟨?_, trivial⟩
                rw [memSt] at h1 ⊢; rw [h2] at h1; simp only; omega
              · intro s hs
                simp only [mem_filter, coe_filter, Set.mem_setOf_eq] at hs
                rw [← hs.2]
              · intro s hs
                simp only [mem_filter, coe_filter, Set.mem_setOf_eq] at hs
                rw [← hs.2]
              · intro s hs; rfl
            funext x
            unfold condNodeLaw productForm normConst
            by_cases hx : x ∈ states n M₀
            · rw [if_pos hx, if_pos hx]
              have hden : availableProb m π M₀ = H * K x * ∑ x' ∈ states n M₀, P x' := by
                rw [availEq, mul_sum]
                refine Finset.sum_congr rfl (fun x' hx' => ?_)
                rw [fib, Kinv x' x (by rw [(memStates M₀ x).1 hx, (memStates M₀ x').1 hx'])]
                ring
              have hpos := hM
              rw [hden] at hpos ⊢
              rw [fib]
              have h1 : H * K x ≠ 0 := by
                intro h; rw [h, zero_mul] at hpos; exact lt_irrefl _ hpos
              show H * P x * K x / (H * K x * ∑ x' ∈ states n M₀, P x') = P x / ∑ x' ∈ states n M₀, P x'
              rw [show H * P x * K x = (H * K x) * P x by ring, mul_div_mul_left _ _ h1]
            · rw [if_neg hx, if_neg hx]
          refine ⟨?_, COND⟩
          rcases Nat.eq_zero_or_pos M₀ with h0 | h0
          · subst h0
            refine ⟨condNN, condOff, condSum, ?_⟩
            intro x hx
            have hx0 : ∀ i, x i = 0 := by
              intro i
              have := (memStates 0 x).1 hx
              exact (Finset.sum_eq_zero_iff.1 this) i (mem_univ i)
            have e1 : ∀ i j, toPolicy q x i j = 0 := by intro i j; simp only [toPolicy, hx0, lt_irrefl, if_false]
            simp only [e1, mul_zero, sum_const_zero, inflowTerm]
            symm
            refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
            have hj : ¬ (1 ≤ x j) := by rw [hx0 j]; omega
            split_ifs <;> first | rfl | exact absurd ‹1 ≤ x j› hj | rw [e1, mul_zero]
          · obtain ⟨r, hr, htr⟩ := EXR h0
            rw [COND r hr htr]
            refine GNS M₀ r hr htr ?_
            obtain ⟨s, hs, hsp⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := St.filter (fun s : TTState n => ∑ i, s.1 i = M₀)) (f := π) hM.ne'
            rw [mem_filter] at hs
            exact ⟨s.1, (memStates M₀ s.1).2 hs.2⟩
