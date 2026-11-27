-- Prove2me | solution 1 for SharedVehicleApprox.Pricing.Supplement.lemma_33
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:08:08.756491+00:00
-- url     : https://prove2.me/submissions/4cb2ab61-cc7f-4e26-8737-1229cb54b5bb

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_PointPricing

open Finset QueueingFundamentals.Networks

open SharedVehicleApprox
open SharedVehicleApprox.Pricing
open SharedVehicleApprox.Pricing.Supplement

/-- Lemma 33, p. 40 (corrected: the graph `{(i, j) : φ_ij > 0}` is strongly connected): raising
point quantiles does not decrease the steady-state rate of realized trips between any pair of
nodes. -/
theorem solution {n m : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (hconn : SupportConnected φ (fun _ _ => 1))
    (q qt : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (hqt : ∀ i, 0 ≤ qt i ∧ qt i ≤ 1)
    (hle : ∀ k, q k ≤ qt k)
    (π πt : (Fin n → ℕ) → ℝ)
    (hπ : IsStationary n m φ (toPolicy (pointQuantile q)) π)
    (hπt : IsStationary n m φ (toPolicy (pointQuantile qt)) πt) (i j : Fin n) :
    flow n m φ (toPolicy (pointQuantile q)) π i j ≤
      flow n m φ (toPolicy (pointQuantile qt)) πt i j := by
        classical
        let add (x : Fin n → ℕ) (a : Fin n) := Function.update x a (x a + 1)
        have mem_states (x : Fin n → ℕ) (M : ℕ) :
            x ∈ states n M ↔ ∑ a, x a = M := by
          simp only [states, mem_filter, Fintype.mem_piFinset, mem_range]
          constructor
          · exact fun h => h.2
          · intro h
            refine ⟨?_, h⟩
            intro a
            have := single_le_sum (fun b _ => Nat.zero_le (x b)) (mem_univ a)
            omega
        have add_mem (x : Fin n → ℕ) (M : ℕ) (a : Fin n) :
            add x a ∈ states n (M + 1) ↔ x ∈ states n M := by
          rw [mem_states, mem_states]
          dsimp [add]
          rw [sum_update_of_mem (mem_univ a)]
          simp only [sdiff_singleton_eq_erase]
          have hs := sum_erase_add univ x (mem_univ a)
          have := single_le_sum (fun b _ => Nat.zero_le (x b)) (mem_univ a)
          omega
        have add_inj (a : Fin n) : Function.Injective (fun x => add x a) := by
          intro x y h
          funext b
          by_cases hb : b = a
          · subst b
            have := congrFun h a
            simpa [add] using this
          · have := congrFun h b
            simpa [add, hb] using this
        have sum_add (M : ℕ) (a : Fin n) (f : (Fin n → ℕ) → ℝ) :
            (∑ x ∈ states n (M+1), if 0 < x a then f x else 0) =
              ∑ x ∈ states n M, f (add x a) := by
          rw [← sum_filter]
          symm
          apply sum_bij (fun x _ => add x a)
          · intro x hx
            exact mem_filter.mpr ⟨(add_mem x M a).mpr hx, by simp [add]⟩
          · intro x hx y hy h
            exact add_inj a h
          · intro y hy
            have hy' := mem_filter.mp hy
            let x := Function.update y a (y a - 1)
            have hxy : add x a = y := by
              funext b
              by_cases hb : b = a
              · subst b; simp [add, x]; omega
              · simp [add, x, hb]
            exact ⟨x, (add_mem x M a).mp (hxy ▸ hy'.1), hxy⟩
          · intro x hx; rfl
        have move_add (x : Fin n → ℕ) (a b : Fin n) (hab : a ≠ b) :
            moveState (add x b) a b = add x a := by
          ext c
          by_cases hca : c = a
          · subst c; simp [moveState, add, hab]
          · by_cases hcb : c = b
            · subst c; simp [moveState, add, hab, Ne.symm hab]
            · simp [moveState, add, hca, hcb]
        have inflow_add (a : Fin n → ℝ) (p : (Fin n → ℕ) → ℝ)
            (x : Fin n → ℕ) (u v : Fin n) :
            inflowTerm φ (toPolicy (pointQuantile a)) p (add x v) u v =
              p (add x u) * φ u v * a u := by
          by_cases h : u = v
          · subst v; simp [inflowTerm, toPolicy, pointQuantile, add]
          · rw [inflowTerm, if_neg h, if_pos (by simp [add]), move_add x u v h]
            simp [toPolicy, pointQuantile, add]
        have inflow_zero (a : Fin n → ℝ) (p : (Fin n → ℕ) → ℝ)
            (x : Fin n → ℕ) (u v : Fin n) (hv : x v = 0) :
            inflowTerm φ (toPolicy (pointQuantile a)) p x u v = 0 := by
          by_cases h : u = v
          · subst v; simp [inflowTerm, toPolicy, hv]
          · simp [inflowTerm, h, hv]
        have weak (M : ℕ) (a : Fin n → ℝ) (p : (Fin n → ℕ) → ℝ)
            (hp : IsStationary n (M+1) φ (toPolicy (pointQuantile a)) p)
            (F : (Fin n → ℕ) → ℝ) :
            ∑ x ∈ states n M, ∑ u, ∑ v,
              p (add x u) * a u * φ u v * (F (add x u) - F (add x v)) = 0 := by
          have hout (u v : Fin n) :
              (∑ x ∈ states n (M+1),
                F x * (p x * (φ u v * toPolicy (pointQuantile a) x u v))) =
                ∑ x ∈ states n M, p (add x u) * a u * φ u v * F (add x u) := by
            convert sum_add M u (fun x => p x * a u * φ u v * F x) using 1
            apply sum_congr rfl
            intro x hx
            by_cases h : 0 < x u <;> simp [toPolicy, pointQuantile, h] <;> ring
          have hin (u v : Fin n) :
              (∑ x ∈ states n (M+1), F x * inflowTerm φ (toPolicy (pointQuantile a)) p x u v) =
                ∑ x ∈ states n M, p (add x u) * a u * φ u v * F (add x v) := by
            calc
              _ = ∑ x ∈ states n (M+1), if 0 < x v then
                  F x * inflowTerm φ (toPolicy (pointQuantile a)) p x u v else 0 := by
                apply sum_congr rfl
                intro x hx
                split_ifs with h
                · rfl
                · rw [inflow_zero a p x u v (by omega), mul_zero]
              _ = ∑ x ∈ states n M,
                  F (add x v) * inflowTerm φ (toPolicy (pointQuantile a)) p (add x v) u v :=
                sum_add M v _
              _ = _ := by simp_rw [inflow_add]; congr 1; funext x; ring
          have shuffle (f : (Fin n → ℕ) → Fin n → Fin n → ℝ) :
              (∑ x ∈ states n (M+1), ∑ u, ∑ v, f x u v) =
                ∑ u, ∑ v, ∑ x ∈ states n (M+1), f x u v := by
            rw [sum_comm]
            apply sum_congr rfl
            intro u hu
            rw [sum_comm]
          have h := sum_congr rfl (fun x hx => congrArg (fun t : ℝ => F x * t) (hp.2.2.2 x hx))
          simp only [mul_sum] at h
          rw [shuffle, shuffle] at h
          simp_rw [hout, hin] at h
          have shuffle' (f : (Fin n → ℕ) → Fin n → Fin n → ℝ) :
              (∑ x ∈ states n M, ∑ u, ∑ v, f x u v) =
                ∑ u, ∑ v, ∑ x ∈ states n M, f x u v := by
            rw [sum_comm]
            apply sum_congr rfl
            intro u hu
            rw [sum_comm]
          simp_rw [mul_sub, sum_sub_distrib]
          rw [shuffle', shuffle']
          exact sub_eq_zero.mpr h
        let rate (M : ℕ) (a : Fin n → ℝ) (p : (Fin n → ℕ) → ℝ) (u : Fin n) :=
          (∑ x ∈ states n M, p (add x u)) * a u
        have flow_rate (M : ℕ) (a : Fin n → ℝ) (p : (Fin n → ℕ) → ℝ) (u v : Fin n) :
            flow n (M+1) φ (toPolicy (pointQuantile a)) p u v = rate M a p u * φ u v := by
          unfold flow
          calc
            _ = ∑ x ∈ states n (M+1), if 0 < x u then p x * a u * φ u v else 0 := by
              apply sum_congr rfl
              intro x hx
              by_cases h : 0 < x u <;> simp [toPolicy, pointQuantile, h] <;> ring
            _ = ∑ x ∈ states n M, p (add x u) * a u * φ u v := sum_add M u _
            _ = _ := by simp [rate, sum_mul]
        have traffic (M : ℕ) (a : Fin n → ℝ) (p : (Fin n → ℕ) → ℝ)
            (hp : IsStationary n (M+1) φ (toPolicy (pointQuantile a)) p) (k : Fin n) :
            rate M a p k * (∑ v, φ k v) = ∑ u, rate M a p u * φ u k := by
          have h := weak M a p hp (fun x => (x k : ℝ))
          have diff (x : Fin n → ℕ) (u v : Fin n) :
              (add x u k : ℝ) - (add x v k : ℝ) =
                (if u = k then 1 else 0) - (if v = k then 1 else 0) := by
            have ev (u : Fin n) : add x u k = x k + if u = k then 1 else 0 := by
              by_cases hu : u = k
              · subst u; simp [add]
              · rw [show add x u k = x k from Function.update_of_ne (Ne.symm hu) _ _]
                simp [hu]
            rw [ev u, ev v]
            push_cast
            ring
          simp_rw [diff] at h
          have collapse (g : Fin n → Fin n → ℝ) :
              (∑ x ∈ states n M, ∑ u, ∑ v, p (add x u) * a u * φ u v * g u v) =
                ∑ u, ∑ v, rate M a p u * φ u v * g u v := by
            rw [sum_comm]
            apply sum_congr rfl
            intro u hu
            rw [sum_comm]
            apply sum_congr rfl
            intro v hv
            simp [rate, sum_mul]
          rw [collapse] at h
          simp_rw [mul_sub, sum_sub_distrib] at h
          simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true] at h
          rw [sum_comm] at h
          simp only [sum_ite_eq', mem_univ, if_true] at h
          simpa only [← mul_sum] using sub_eq_zero.mp h
        have zero_traffic (r : Fin n → ℝ) (hr : ∀ u, 0 ≤ r u)
            (ht : ∀ k, r k * (∑ v, φ k v) = ∑ u, r u * φ u k)
            (b : Fin n) (hb : r b = 0) : ∀ u, r u = 0 := by
          have edge (u v : Fin n) (huv : 0 < φ u v) (hv : r v = 0) : r u = 0 := by
            have hs := ht v
            rw [hv, zero_mul] at hs
            have hle := single_le_sum (fun a _ => mul_nonneg (hr a) (hφ a v)) (mem_univ u)
            have : r u * φ u v = 0 := le_antisymm (by linarith) (mul_nonneg (hr u) (hφ u v))
            exact (mul_eq_zero.mp this).resolve_right (ne_of_gt huv)
          intro u
          have path := hconn u b
          have hp : r b = 0 → r u = 0 := by
            clear hb
            induction path with
            | refl => exact id
            | @tail v w hvw hw ih =>
              intro hz
              exact ih (edge v w (by simpa using hw.2) hz)
          exact hp hb
        have proportional (r s : Fin n → ℝ) (hr : ∀ u, 0 < r u)
            (ht : ∀ k, r k * (∑ v, φ k v) = ∑ u, r u * φ u k)
            (hs : ∀ k, s k * (∑ v, φ k v) = ∑ u, s u * φ u k) :
            ∃ c : ℝ, ∀ u, s u = c * r u := by
          obtain ⟨b, hb, hmax⟩ := exists_max_image univ (fun u => s u / r u) ⟨i, mem_univ i⟩
          let c := s b / r b
          have hc : ∀ u, 0 ≤ c * r u - s u := by
            intro u
            have := hmax u (mem_univ u)
            have := (div_le_iff₀ (hr u)).mp this
            dsimp [c]; linarith
          have hd : ∀ k, (c * r k - s k) * (∑ v, φ k v) = ∑ u, (c * r u - s u) * φ u k := by
            intro k
            simp_rw [sub_mul, mul_assoc, sum_sub_distrib, ← mul_sum]
            rw [ht k, hs k]
          have hz : c * r b - s b = 0 := by dsimp [c]; rw [div_mul_cancel₀ _ (ne_of_gt (hr b)), sub_self]
          have hall := zero_traffic (fun u => c * r u - s u) hc hd b hz
          exact ⟨c, fun u => by have := hall u; linarith⟩
        have rate_nn (M : ℕ) (a : Fin n → ℝ) (p : (Fin n → ℕ) → ℝ)
            (ha : ∀ u, 0 ≤ a u) (hp : ∀ x, 0 ≤ p x) (u : Fin n) : 0 ≤ rate M a p u :=
          mul_nonneg (sum_nonneg fun x hx => hp _) (ha u)
        by_cases hm : m = 0
        · subst m
          have hf (a : Fin n → ℝ) (p : (Fin n → ℕ) → ℝ) :
              flow n 0 φ (toPolicy (pointQuantile a)) p i j = 0 := by
            apply sum_eq_zero
            intro x hx
            have hx' := (mem_states x 0).mp hx
            have := single_le_sum (fun u _ => Nat.zero_le (x u)) (mem_univ i)
            have hxi : x i = 0 := by omega
            simp [toPolicy, hxi]
          rw [hf, hf]
        obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
        change flow n (M+1) φ (toPolicy (pointQuantile q)) π i j ≤ _
        by_cases hpos : ∀ u, 0 < q u
        swap
        · push_neg at hpos
          obtain ⟨b, hb⟩ := hpos
          have hbq : q b = 0 := le_antisymm hb (hq b).1
          have hbr : rate M q π b = 0 := by simp [rate, hbq]
          have hz := zero_traffic (rate M q π) (rate_nn M q π (fun u => (hq u).1) hπ.1)
            (traffic M q π hπ) b hbr i
          rw [flow_rate, hz, zero_mul, flow_rate]
          exact mul_nonneg (rate_nn M qt πt (fun u => (hqt u).1) hπt.1 i) (hφ i j)
        have hpost : ∀ u, 0 < qt u := fun u => lt_of_lt_of_le (hpos u) (hle u)
        have hrpos : ∀ u, 0 < rate M q π u := by
          have hex : ∃ x ∈ states n (M+1), 0 < π x := by
            apply (sum_pos_iff_of_nonneg (fun x hx => hπ.1 x)).mp
            rw [hπ.2.2.1]
            norm_num
          obtain ⟨x, hx, hpx⟩ := hex
          have hexu : ∃ u, 0 < x u := by
            by_contra hn
            push_neg at hn
            have hz : ∑ u, x u = 0 := sum_eq_zero (fun u _ => by have := hn u; omega)
            have := (mem_states x (M+1)).mp hx
            omega
          obtain ⟨u, hu⟩ := hexu
          let z := Function.update x u (x u - 1)
          have hzx : add z u = x := by
            ext v
            by_cases hv : v = u
            · subst v; simp [add, z]; omega
            · simp [add, z, hv]
          have hz : z ∈ states n M := (add_mem z M u).mp (hzx ▸ hx)
          have hru : 0 < rate M q π u := by
            apply mul_pos _ (hpos u)
            exact lt_of_lt_of_le (by simpa [hzx] using hpx)
              (single_le_sum (fun z _ => hπ.1 (add z u)) hz)
          intro v
          by_contra hv
          have hvz : rate M q π v = 0 := le_antisymm (by linarith)
            (rate_nn M q π (fun u => (hq u).1) hπ.1 v)
          have := zero_traffic (rate M q π) (rate_nn M q π (fun u => (hq u).1) hπ.1)
            (traffic M q π hπ) v hvz u
          linarith
        let v := rate M q π
        have hv : ∀ u, 0 < v u := hrpos
        have hvt : ∀ k, v k * (∑ b, φ k b) = ∑ a, v a * φ a k := traffic M q π hπ
        let W (r : Fin n → ℝ) (x : Fin n → ℕ) := ∏ u, r u ^ x u
        have Wpos (r : Fin n → ℝ) (hr : ∀ u, 0 < r u) (x : Fin n → ℕ) : 0 < W r x :=
          prod_pos fun u _ => pow_pos (hr u) _
        have Wadd (r : Fin n → ℝ) (x : Fin n → ℕ) (u : Fin n) :
            W r (add x u) = W r x * r u := by
          have he : (∏ a ∈ univ.erase u, r a ^ add x u a) = ∏ a ∈ univ.erase u, r a ^ x a := by
            apply prod_congr rfl
            intro a ha
            rw [show add x u a = x a from Function.update_of_ne (mem_erase.mp ha).1 _ _]
          dsimp [W]
          rw [← mul_prod_erase univ (fun a => r a ^ add x u a) (mem_univ u), he]
          rw [← mul_prod_erase univ (fun a => r a ^ x a) (mem_univ u)]
          simp only [add, Function.update_self, pow_succ]
          ring
        have traffic_weak (f : Fin n → ℝ) :
            ∑ a, ∑ b, v a * φ a b * (f a - f b) = 0 := by
          simp_rw [mul_sub, sum_sub_distrib]
          have h₁ : (∑ a, ∑ b, v a * φ a b * f a) = ∑ a, (v a * ∑ b, φ a b) * f a := by
            apply sum_congr rfl
            intro a ha
            simp only [← sum_mul, ← mul_sum]
          rw [h₁, sum_comm (f := fun a b => v a * φ a b * f b)]
          simp_rw [← sum_mul, ← hvt]
          exact sub_self _
        have composition_const (g : (Fin n → ℕ) → ℝ)
            (hg : ∀ x ∈ states n M, ∀ a b, g (add x a) = g (add x b)) :
            ∃ c, ∀ x ∈ states n (M+1), g x = c := by
          let pile := Function.update (fun _ : Fin n => 0) i (M+1)
          refine ⟨g pile, ?_⟩
          have hall : ∀ K, ∀ x ∈ states n (M+1), M+1-x i = K → g x = g pile := by
            intro K
            induction K using Nat.strong_induction_on with
            | h K ih =>
              intro x hx hK
              have hsum := (mem_states x (M+1)).mp hx
              have hxi : x i ≤ M+1 := by
                have := single_le_sum (fun a _ => Nat.zero_le (x a)) (mem_univ i)
                omega
              by_cases hbase : ∀ a, a ≠ i → x a = 0
              · have hxeq : x = pile := by
                  have hs : ∑ a, x a = x i := sum_eq_single i (fun a _ hai => hbase a hai) (by simp)
                  ext a
                  by_cases hai : a = i
                  · subst a; simp [pile]; omega
                  · simp [pile, hai, hbase a hai]
                rw [hxeq]
              · push_neg at hbase
                obtain ⟨a, hai, hxa⟩ := hbase
                let z := Function.update x a (x a - 1)
                have hzxa : add z a = x := by
                  ext b
                  by_cases hb : b = a
                  · subst b; simp [add, z]; omega
                  · simp [add, z, hb]
                have hz : z ∈ states n M := (add_mem z M a).mp (hzxa ▸ hx)
                have hy : add z i ∈ states n (M+1) := (add_mem z M i).mpr hz
                have hiy : add z i i = x i + 1 := by simp [add, z, Ne.symm hai]
                have hlt : M+1 - add z i i < K := by
                  have := single_le_sum (fun b _ => Nat.zero_le (add z i b)) (mem_univ i)
                  have hys := (mem_states (add z i) (M+1)).mp hy
                  omega
                calc
                  g x = g (add z i) := by rw [← hzxa]; exact hg z hz a i
                  _ = g pile := ih _ hlt _ hy rfl
          intro x hx
          exact hall _ x hx rfl
        have product_rep (a : Fin n → ℝ) (ha : ∀ u, 0 < a u)
            (p : (Fin n → ℕ) → ℝ) (hp : IsStationary n (M+1) φ (toPolicy (pointQuantile a)) p) :
            ∃ c, 0 < c ∧ ∀ x ∈ states n (M+1), p x = c * W (fun u => v u / a u) x := by
          let r := fun u => v u / a u
          have hr : ∀ u, 0 < r u := fun u => div_pos (hv u) (ha u)
          have hcancel (u : Fin n) : r u * a u = v u := div_mul_cancel₀ _ (ne_of_gt (ha u))
          have Wweak (F : (Fin n → ℕ) → ℝ) :
              ∑ x ∈ states n M, ∑ u, ∑ b,
                W r (add x u) * a u * φ u b * (F (add x u) - F (add x b)) = 0 := by
            apply sum_eq_zero
            intro x hx
            simp_rw [Wadd, mul_assoc (W r x), hcancel, ← mul_sum]
            rw [traffic_weak (fun u => F (add x u)), mul_zero]
          let d := fun x => p x / W r x
          have hd (x : Fin n → ℕ) : p x = W r x * d x := by
            dsimp [d]; field_simp [ne_of_gt (Wpos r hr x)]
          have henergy :
              ∑ x ∈ states n M, ∑ u, ∑ b,
                W r (add x u) * a u * φ u b * (d (add x u) - d (add x b)) ^ 2 = 0 := by
            calc
              _ = 2 * (∑ x ∈ states n M, ∑ u, ∑ b,
                    p (add x u) * a u * φ u b * (d (add x u) - d (add x b))) -
                  (∑ x ∈ states n M, ∑ u, ∑ b,
                    W r (add x u) * a u * φ u b * ((d (add x u))^2 - (d (add x b))^2)) := by
                simp_rw [mul_sum, ← sum_sub_distrib]
                apply sum_congr rfl
                intro x hx
                apply sum_congr rfl
                intro u hu
                apply sum_congr rfl
                intro b hb
                rw [hd (add x u)]
                ring
              _ = 0 := by rw [weak M a p hp d, Wweak (fun x => d x ^ 2)]; ring
          have hedges (x : Fin n → ℕ) (hx : x ∈ states n M) (u b : Fin n) (hub : 0 < φ u b) :
              d (add x u) = d (add x b) := by
            have hnn (x : Fin n → ℕ) (u b : Fin n) :
                0 ≤ W r (add x u) * a u * φ u b * (d (add x u) - d (add x b))^2 :=
              mul_nonneg (mul_nonneg (mul_nonneg (Wpos r hr _).le (ha u).le) (hφ u b)) (sq_nonneg _)
            have hx0 := (sum_eq_zero_iff_of_nonneg (fun x _ => sum_nonneg (fun u _ =>
              sum_nonneg (fun b _ => hnn x u b)))).mp henergy x hx
            have hu0 := (sum_eq_zero_iff_of_nonneg (fun u _ => sum_nonneg (fun b _ => hnn x u b))).mp hx0 u (mem_univ u)
            have hb0 := (sum_eq_zero_iff_of_nonneg (fun b _ => hnn x u b)).mp hu0 b (mem_univ b)
            have hcoeff : 0 < W r (add x u) * a u * φ u b := mul_pos (mul_pos (Wpos r hr _) (ha u)) hub
            have hsq : (d (add x u) - d (add x b))^2 = 0 :=
              (mul_eq_zero.mp hb0).resolve_left (ne_of_gt hcoeff)
            nlinarith [sq_nonneg (d (add x u) - d (add x b))]
          have hlocal : ∀ x ∈ states n M, ∀ u b, d (add x u) = d (add x b) := by
            intro x hx u b
            have path := hconn u b
            induction path with
            | refl => rfl
            | @tail u b hub hbc ih =>
              exact ih.trans (hedges x hx u b (by simpa using hbc.2))
          obtain ⟨c, hc⟩ := composition_const d hlocal
          have hrep : ∀ x ∈ states n (M+1), p x = c * W r x := by
            intro x hx
            rw [hd x, hc x hx, mul_comm]
          have hcpos : 0 < c := by
            obtain ⟨x, hx, hpx⟩ := (sum_pos_iff_of_nonneg (fun x hx => hp.1 x)).mp
              (show 0 < ∑ x ∈ states n (M+1), p x by rw [hp.2.2.1]; norm_num)
            rw [hrep x hx] at hpx
            exact (mul_pos_iff_of_pos_right (Wpos r hr x)).mp hpx
          exact ⟨c, hcpos, hrep⟩
        obtain ⟨c, hc, hrep⟩ := product_rep q hpos π hπ
        obtain ⟨ct, hct, hrept⟩ := product_rep qt hpost πt hπt
        let t := fun u => Real.log (q u / qt u)
        have hexsort : ∃ e : Fin n ≃ Fin n, Antitone (fun k => t (e k)) := by
          let key : ULift.{0} (Fin n) → ℝ ×ₗ Fin n := fun x => toLex (-t x.down, x.down)
          have hkey : Function.Injective key := by
            intro a b hab
            apply ULift.ext
            exact congrArg (fun z : ℝ ×ₗ Fin n => (ofLex z).2) hab
          let ord := LinearOrder.lift' key hkey
          letI : LE (ULift.{0} (Fin n)) := ord.toLE
          letI : LT (ULift.{0} (Fin n)) := ord.toLT
          letI : Preorder (ULift.{0} (Fin n)) := ord.toPreorder
          letI : PartialOrder (ULift.{0} (Fin n)) := ord.toPartialOrder
          letI : LinearOrder (ULift.{0} (Fin n)) := ord
          let eo : Fin n ≃o ULift.{0} (Fin n) := Fintype.orderIsoFinOfCardEq (ULift.{0} (Fin n)) (by exact (Fintype.card_congr Equiv.ulift).trans (Fintype.card_fin n))
          refine ⟨eo.toEquiv.trans Equiv.ulift, ?_⟩
          intro a b hab
          have h := eo.monotone hab
          change key (eo a) ≤ key (eo b) at h
          have hfst := (Prod.Lex.toLex_le_toLex'.mp h).1
          dsimp [key] at hfst
          simpa using neg_le_neg_iff.mp hfst
        obtain ⟨e, he⟩ := hexsort
        have hn : 0 < n := by have := i.isLt; omega
        let first : Fin n := ⟨0, hn⟩
        let L : Sublattice (Fin (n+1) → Fin (M+2)) :=
          { carrier := {p | Monotone p ∧ p 0 = 0 ∧ p (Fin.last n) = Fin.last (M+1)}
            supClosed' := by
              intro a ha b hb
              exact ⟨ha.1.sup hb.1, by simp [ha.2.1, hb.2.1], by simp [ha.2.2, hb.2.2]⟩
            infClosed' := by
              intro a ha b hb
              exact ⟨ha.1.inf hb.1, by simp [ha.2.1, hb.2.1], by simp [ha.2.2, hb.2.2]⟩ }
        letI : Fintype L := Fintype.ofFinite _
        let cum (x : Fin n → ℕ) (k : Fin (n+1)) :=
          ∑ a ∈ univ.filter (fun a : Fin n => a.val < k.val), x (e a)
        have cum_zero (x : Fin n → ℕ) : cum x 0 = 0 := by simp [cum]
        have cum_last (x : Fin n → ℕ) : cum x (Fin.last n) = ∑ a, x a := by
          change (∑ a ∈ univ.filter (fun a : Fin n => a.val < n), x (e a)) = _
          rw [filter_true_of_mem (fun a _ => a.isLt)]
          exact e.sum_comp x
        have cum_step (x : Fin n → ℕ) (k : Fin n) :
            cum x k.succ = cum x k.castSucc + x (e k) := by
          have hf : univ.filter (fun a : Fin n => a.val < k.succ.val) =
              insert k (univ.filter (fun a : Fin n => a.val < k.castSucc.val)) := by
            ext a
            simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.val_succ, Fin.val_castSucc]
            rw [Fin.ext_iff]
            omega
          change (∑ a ∈ univ.filter (fun a : Fin n => a.val < k.succ.val), x (e a)) = _
          rw [hf, sum_insert (by simp)]
          change x (e k) + cum x k.castSucc = cum x k.castSucc + x (e k)
          omega
        have cum_mono (x : Fin n → ℕ) : Monotone (cum x) := by
          intro a b hab
          apply sum_le_sum_of_subset_of_nonneg
          · intro u hu
            simp only [mem_filter, mem_univ, true_and] at hu ⊢
            exact lt_of_lt_of_le hu hab
          · intros; exact Nat.zero_le _
        let enc (x : {x // x ∈ states n (M+1)}) : L :=
          ⟨fun k => ⟨cum x.val k, by
            have hle := cum_mono x.val (Fin.le_last k)
            rw [cum_last, (mem_states x.val (M+1)).mp x.property] at hle
            omega⟩,
            by
              refine ⟨?_, ?_, ?_⟩
              · intro a b hab; exact cum_mono x.val hab
              · apply Fin.ext; exact cum_zero x.val
              · apply Fin.ext
                exact (cum_last x.val).trans ((mem_states x.val (M+1)).mp x.property)⟩
        let occ (p : L) (k : Fin n) : ℕ :=
          (p.val k.succ).val - (p.val k.castSucc).val
        have occ_sum (p : L) : ∑ k, occ p k = M+1 := by
          have hmono (k : Fin n) : (p.val k.castSucc).val ≤ (p.val k.succ).val :=
            p.property.1 (by simp [Fin.le_iff_val_le_val])
          have hs := Fin.sum_univ_succ (fun k => (p.val k).val)
          have hs' := Fin.sum_univ_castSucc (fun k => (p.val k).val)
          simp only [p.property.2.1, p.property.2.2, Fin.val_zero, Fin.val_last] at hs hs'
          dsimp [occ]
          rw [sum_tsub_distrib _ (fun k _ => hmono k)]
          omega
        let dec (p : L) : {x // x ∈ states n (M+1)} :=
          ⟨fun u => occ p (e.symm u), (mem_states _ _).mpr (by
            have hsum := e.symm.sum_comp (occ p)
            exact hsum.trans (occ_sum p))⟩
        have dec_enc (x : {x // x ∈ states n (M+1)}) : dec (enc x) = x := by
          apply Subtype.ext
          ext u
          change cum x.val (e.symm u).succ - cum x.val (e.symm u).castSucc = x.val u
          rw [cum_step]
          simp
        have enc_dec (p : L) : enc (dec p) = p := by
          apply Subtype.ext
          funext k
          apply Fin.ext
          change cum (dec p).val k = (p.val k).val
          induction k using Fin.induction with
          | zero => rw [cum_zero, p.property.2.1]; rfl
          | succ k ih =>
            rw [cum_step, ih]
            change (p.val k.castSucc).val + occ p (e.symm (e k)) = _
            rw [e.symm_apply_apply]
            dsimp [occ]
            have := p.property.1 (show k.castSucc ≤ k.succ by simp [Fin.le_iff_val_le_val])
            change (p.val k.castSucc).val ≤ (p.val k.succ).val at this
            omega
        let E : {x // x ∈ states n (M+1)} ≃ L :=
          { toFun := enc, invFun := dec, left_inv := dec_enc, right_inv := enc_dec }
        have reindex (F : (Fin n → ℕ) → ℝ) :
            (∑ x ∈ states n (M+1), F x) = ∑ p : L, F (dec p).val := by
          rw [sum_subtype (states n (M+1)) (fun x => Iff.rfl)]
          exact Fintype.sum_equiv E (fun x => F x.val) (fun p => F (dec p).val)
            (fun x => congrArg (fun x : {x // x ∈ states n (M+1)} => F x.val) (dec_enc x).symm)
        have occ_cast (p : L) (k : Fin n) :
            (occ p k : ℝ) = ((p.val k.succ).val : ℝ) - ((p.val k.castSucc).val : ℝ) := by
          exact Nat.cast_sub (p.property.1 (show k.castSucc ≤ k.succ by simp [Fin.le_iff_val_le_val]))
        let lin (b : Fin n → ℝ) (p : L) := ∑ k, (occ p k : ℝ) * b k
        have lin_mod (b : Fin n → ℝ) (p z : L) :
            lin b p + lin b z = lin b (p ⊓ z) + lin b (p ⊔ z) := by
          have hvmod (k : Fin (n+1)) :
              ((p.val k).val : ℝ) + ((z.val k).val : ℝ) =
                (((p ⊓ z).val k).val : ℝ) + (((p ⊔ z).val k).val : ℝ) := by
            change ((p.val k).val : ℝ) + ((z.val k).val : ℝ) =
              ((min (p.val k) (z.val k)).val : ℝ) + ((max (p.val k) (z.val k)).val : ℝ)
            rw [Fin.coe_min, Fin.coe_max]
            exact_mod_cast (min_add_max (p.val k).val (z.val k).val).symm
          dsimp [lin]
          rw [← sum_add_distrib, ← sum_add_distrib]
          apply sum_congr rfl
          intro k hk
          simp_rw [occ_cast]
          have h₁ := hvmod k.succ
          have h₂ := hvmod k.castSucc
          linear_combination b k * h₁ - b k * h₂
        have lin_add (b d : Fin n → ℝ) (p : L) :
            lin (fun k => b k + d k) p = lin b p + lin d p := by
          simp [lin, mul_add, sum_add_distrib]
        have Wexp (r : Fin n → ℝ) (hr : ∀ u, 0 < r u) (p : L) :
            W r (dec p).val = Real.exp (lin (fun k => Real.log (r (e k))) p) := by
          calc
            _ = ∏ k, r (e k) ^ occ p k := by
              dsimp [W, dec]
              rw [← e.prod_comp (fun u => r u ^ occ p (e.symm u))]
              simp
            _ = _ := by
              dsimp only [lin]
              rw [Real.exp_sum]
              apply prod_congr rfl
              intro k hk
              rw [Real.exp_nat_mul, Real.exp_log (hr (e k))]
        have lin_mono (b : Fin n → ℝ) (hb : Antitone b) : Monotone (lin b) := by
          intro p z hpz
          let D : Fin (n+1) → ℝ := fun k => ((z.val k).val : ℝ) - ((p.val k).val : ℝ)
          let B : Fin (n+1) → ℝ := fun k => if h : k.val < n then b ⟨k.val, h⟩ else 0
          have Dzero : D 0 = 0 := by simp [D, p.property.2.1, z.property.2.1]
          have Dlast : D (Fin.last n) = 0 := by simp [D, p.property.2.2, z.property.2.2]
          have Dnn (k : Fin (n+1)) : 0 ≤ D k := by
            have h := hpz k
            change p.val k ≤ z.val k at h
            dsimp [D]
            exact sub_nonneg.mpr (by exact_mod_cast h)
          have Bcast (k : Fin n) : B k.castSucc = b k := by simp [B]
          have htel : (∑ k : Fin n, D k.succ * B k.succ) -
              (∑ k : Fin n, D k.castSucc * B k.castSucc) = 0 := by
            have h₁ := Fin.sum_univ_succ (fun k => D k * B k)
            have h₂ := Fin.sum_univ_castSucc (fun k => D k * B k)
            rw [Dzero, zero_mul] at h₁
            rw [Dlast, zero_mul] at h₂
            linarith
          have hid : lin b z - lin b p = ∑ k : Fin n, D k.succ * (b k - B k.succ) := by
            calc
              _ = ∑ k : Fin n, (D k.succ - D k.castSucc) * b k := by
                dsimp [lin]
                rw [← sum_sub_distrib]
                apply sum_congr rfl
                intro k hk
                rw [occ_cast, occ_cast]
                dsimp [D]
                ring
              _ = (∑ k : Fin n, D k.succ * (b k - B k.succ)) +
                  ((∑ k : Fin n, D k.succ * B k.succ) -
                    (∑ k : Fin n, D k.castSucc * B k.castSucc)) := by
                simp_rw [mul_sub, sub_mul, sum_sub_distrib, Bcast]
                ring
              _ = _ := by rw [htel, add_zero]
          apply sub_nonneg.mp
          rw [hid]
          apply sum_nonneg
          intro k hk
          by_cases hkn : k.val + 1 < n
          · apply mul_nonneg (Dnn _)
            have h := hb (show k ≤ (⟨k.val+1, hkn⟩ : Fin n) by simp [Fin.le_iff_val_le_val])
            simpa [B, hkn] using sub_nonneg.mpr h
          · have hklast : k.succ = Fin.last n := by apply Fin.ext; have := k.isLt; simp; omega
            rw [hklast, Dlast, zero_mul]
        let b : Fin n → ℝ := fun k => Real.log (v (e k) / q (e k))
        let T : Fin n → ℝ := fun k => t (e k)
        have blog (u : Fin n) : Real.log (v u / qt u) = Real.log (v u / q u) + t u := by
          dsimp [t]
          rw [Real.log_div (ne_of_gt (hv u)) (ne_of_gt (hpost u)),
            Real.log_div (ne_of_gt (hv u)) (ne_of_gt (hpos u)),
            Real.log_div (ne_of_gt (hpos u)) (ne_of_gt (hpost u))]
          ring
        have pexp (p : L) : π (dec p).val = c * Real.exp (lin b p) := by
          rw [hrep _ (dec p).property, Wexp _ (fun u => div_pos (hv u) (hpos u))]
        have ptexp (p : L) : πt (dec p).val = ct * Real.exp (lin b p + lin T p) := by
          rw [hrept _ (dec p).property, Wexp _ (fun u => div_pos (hv u) (hpost u))]
          have hh : (fun k => Real.log (v (e k) / qt (e k))) = fun k => b k + T k := by
            funext k; exact blog (e k)
          rw [hh, lin_add]
        let μ : L → ℝ := fun p => if 0 < (p.val first.succ).val then 1 else 0
        have μnn : ∀ p, 0 ≤ μ p := by intro p; dsimp [μ]; split_ifs <;> norm_num
        have μmono : Monotone μ := by
          intro p z hpz
          by_cases hpp : 0 < (p.val first.succ).val
          · have hzz : 0 < (z.val first.succ).val := by
              have h := hpz first.succ
              change p.val first.succ ≤ z.val first.succ at h
              change (p.val first.succ).val ≤ (z.val first.succ).val at h
              omega
            dsimp only [μ]
            rw [if_pos hpp, if_pos hzz]
          · dsimp only [μ]
            rw [if_neg hpp]
            split_ifs <;> norm_num
        have hsum : (∑ p : L, π (dec p).val) = 1 := by rw [← reindex]; exact hπ.2.2.1
        have hsumt : (∑ p : L, πt (dec p).val) = 1 := by rw [← reindex]; exact hπt.2.2.1
        have hcross (p z : L) :
            π (dec p).val * πt (dec z).val ≤ π (dec (p ⊓ z)).val * πt (dec (p ⊔ z)).val := by
          rw [pexp, ptexp, pexp, ptexp]
          have hmod := lin_mod b p z
          have hmon : lin T z ≤ lin T (p ⊔ z) := lin_mono T he le_sup_right
          have hexp : Real.exp (lin b p + (lin b z + lin T z)) ≤
              Real.exp (lin b (p ⊓ z) + (lin b (p ⊔ z) + lin T (p ⊔ z))) := by
            apply Real.exp_le_exp.mpr
            linarith
          calc
            _ = (c * ct) * Real.exp (lin b p + (lin b z + lin T z)) := by simp only [Real.exp_add]; ring
            _ ≤ (c * ct) * Real.exp (lin b (p ⊓ z) + (lin b (p ⊔ z) + lin T (p ⊔ z))) :=
              mul_le_mul_of_nonneg_left hexp (mul_nonneg hc.le hct.le)
            _ = _ := by simp only [Real.exp_add]; ring
        have havail : (∑ p : L, μ p * π (dec p).val) ≤ ∑ p : L, μ p * πt (dec p).val :=
          holley (fun p => π (dec p).val) (fun p => πt (dec p).val) μ μnn (fun p => hπ.1 _) (fun p => hπt.1 _) μmono (hsum.trans hsumt.symm) hcross
        have busy (p : L) : (dec p).val (e first) = (p.val first.succ).val := by
          change occ p (e.symm (e first)) = _
          rw [e.symm_apply_apply]
          have hfirst : first.castSucc = (0 : Fin (n+1)) := by apply Fin.ext; rfl
          dsimp [occ]
          rw [hfirst, p.property.2.1]
          simp
        have rate_first (a : Fin n → ℝ) (p : (Fin n → ℕ) → ℝ) :
            rate M a p (e first) = (∑ z : L, μ z * p (dec z).val) * a (e first) := by
          dsimp only [rate]
          rw [← sum_add M (e first), reindex]
          congr 1
          apply sum_congr rfl
          intro z hz
          rw [busy]
          dsimp [μ]
          split_ifs <;> simp
        have hfirst_rate : rate M q π (e first) ≤ rate M qt πt (e first) := by
          rw [rate_first, rate_first]
          exact mul_le_mul havail (hle _) (hq _).1
            (sum_nonneg (fun p _ => mul_nonneg (μnn p) (hπt.1 _)))
        obtain ⟨scale, hscale⟩ := proportional v (rate M qt πt) hv hvt (traffic M qt πt hπt)
        have hscalege : 1 ≤ scale := by
          rw [hscale] at hfirst_rate
          change v (e first) ≤ scale * v (e first) at hfirst_rate
          nlinarith [hv (e first)]
        have hrate : rate M q π i ≤ rate M qt πt i := by
          rw [hscale]
          change v i ≤ scale * v i
          nlinarith [hv i]
        rw [flow_rate, flow_rate]
        exact mul_le_mul_of_nonneg_right hrate (hφ i j)
