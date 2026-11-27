-- Prove2me | solution 1 for SharedVehicleApprox.Pricing.Supplement.lemma_17
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:04:58.109785+00:00
-- url     : https://prove2.me/submissions/1e166e21-4c3d-43a6-94b0-555cc049584a

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_StationaryLaw
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_TravelTimes

open Finset QueueingFundamentals.Networks

open SharedVehicleApprox
open SharedVehicleApprox.Pricing
open SharedVehicleApprox.Pricing.Supplement

/-- Lemma 17, p. 20 (corrected: the support graph of `q` is strongly connected): with travel times,
if `m ≥ 100` and `∑_{i,j} φ_ij τ_ij q_ij ≤ m − 2 √(m ln m)`, the maximum availability satisfies
`A_m(q) ≥ (1 − 3/√m) (√(m ln m) / (√(m ln m) + n − 1))`. -/
theorem solution {n m : ℕ} [NeZero n] (hm : 100 ≤ m) (φ τ : Fin n → Fin n → ℝ)
    (hφ : ∀ i j, 0 ≤ φ i j) (hτ : ∀ i j, 0 < τ i j)
    (q : Fin n → Fin n → ℝ) (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ 1)
    (hconn : SupportConnected φ q)
    (hload : ∑ i, ∑ j, φ i j * τ i j * q i j ≤ (m : ℝ) - 2 * Real.sqrt (m * Real.log m))
    (π : TTState n → ℝ) (hπ : IsTTStationary n m φ τ (toTTPolicy q) π) :
    (1 - 3 / Real.sqrt m) *
        (Real.sqrt (m * Real.log m) / (Real.sqrt (m * Real.log m) + n - 1)) ≤
      ttMaxAvailability m π := by
        classical
        have key : ∀ (S : Type) [Fintype S] (k : S → S → ℝ), (∀ s t, 0 ≤ k s t) → ∀ v : S → ℝ,
            (∀ s, v s * ∑ t, k s t = ∑ t, v t * k t s) →
            (∀ s, |v s| * ∑ t, k s t = ∑ t, |v t| * k t s) ∧
            ∀ s t, v t = 0 → 0 < k s t → v s = 0 := by
          intro S _ k hk v hv
          have hle : ∀ s ∈ (univ : Finset S), |v s| * ∑ t, k s t ≤ ∑ t, |v t| * k t s := by
            intro s _
            have h0 : 0 ≤ ∑ t, k s t := Finset.sum_nonneg fun t _ => hk s t
            calc |v s| * ∑ t, k s t = |v s * ∑ t, k s t| := by rw [abs_mul, abs_of_nonneg h0]
              _ = |∑ t, v t * k t s| := by rw [hv s]
              _ ≤ ∑ t, |v t * k t s| := Finset.abs_sum_le_sum_abs _ _
              _ = ∑ t, |v t| * k t s := by
                refine Finset.sum_congr rfl fun t _ => ?_
                rw [abs_mul, abs_of_nonneg (hk t s)]
          have hsum : ∑ s, |v s| * ∑ t, k s t = ∑ s, ∑ t, |v t| * k t s := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [Finset.mul_sum]
          have habs : ∀ s, |v s| * ∑ t, k s t = ∑ t, |v t| * k t s := by
            intro s
            exact (Finset.sum_eq_sum_iff_of_le hle).1 hsum s (Finset.mem_univ s)
          refine ⟨habs, ?_⟩
          intro s t ht hst
          have h1 := habs t
          rw [ht, abs_zero, zero_mul] at h1
          have h2 := (Finset.sum_eq_zero_iff_of_nonneg
            (fun u _ => mul_nonneg (abs_nonneg (v u)) (hk u t))).1 h1.symm s (Finset.mem_univ s)
          rcases mul_eq_zero.1 h2 with h3 | h3
          · exact abs_eq_zero.1 h3
          · exact absurd h3 hst.ne'
        obtain ⟨c, hc⟩ : ∃ c : Fin n → Fin n → ℝ, c = fun i j => φ i j * q i j := ⟨_, rfl⟩
        have hc0 : ∀ i j, 0 ≤ c i j := fun i j => by rw [hc]; exact mul_nonneg (hφ i j) (hq i j).1
        have traffic : ∃ r : Fin n → ℝ, (∀ i, 0 < r i) ∧ (∀ i, r i ≤ 1) ∧ (∃ i0, r i0 = 1) ∧
            ∀ i, ∑ j, r j * c j i = r i * ∑ k, c i k := by
          let M : Matrix (Fin n) (Fin n) ℝ := fun i j => c i j - if i = j then ∑ k, c i k else 0
          have hdet : M.det = 0 := by
            apply Matrix.exists_mulVec_eq_zero_iff.1
            refine ⟨fun _ => 1, ?_, ?_⟩
            · intro h
              have := congrFun h (0 : Fin n)
              simp at this
            · funext i
              simp [Matrix.mulVec, dotProduct, M, Finset.sum_sub_distrib]
          obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
          have hv' : ∀ s, v s * ∑ t, c s t = ∑ t, v t * c t s := by
            intro s
            have := congrFun hv s
            simp [Matrix.vecMul, dotProduct, M, mul_sub, Finset.sum_sub_distrib] at this
            linarith
          obtain ⟨h1, h2⟩ := key (Fin n) c hc0 v hv'
          have hne : ∀ i, v i ≠ 0 := by
            intro i hi
            apply hv0
            funext j
            have hp := hconn j i
            induction hp using Relation.ReflTransGen.head_induction_on with
            | refl => exact hi
            | head hab _ ih =>
              refine h2 _ _ ih ?_
              rw [hc]; exact hab.2
          obtain ⟨i0, _, hi0⟩ := Finset.exists_max_image (univ : Finset (Fin n)) (fun i => |v i|) ⟨0, Finset.mem_univ 0⟩
          have hpos : 0 < |v i0| := abs_pos.2 (hne i0)
          refine ⟨fun i => |v i| / |v i0|, fun i => div_pos (abs_pos.2 (hne i)) hpos,
            fun i => (div_le_one hpos).2 (hi0 i (Finset.mem_univ i)), ⟨i0, div_self hpos.ne'⟩, ?_⟩
          intro i
          have := h1 i
          have e1 : ∑ j, |v j| / |v i0| * c j i = (∑ j, |v j| * c j i) / |v i0| := by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl fun j _ => by ring
          rw [e1, ← this]; ring
        obtain ⟨r, hr0, hr1, ⟨i0, hri0⟩, hr⟩ := traffic
        obtain ⟨a, ha⟩ : ∃ a : Fin n → Fin n → ℝ, a = fun i j => r i * c i j * τ i j := ⟨_, rfl⟩
        have ha0 : ∀ i j, 0 ≤ a i j := fun i j => by
          rw [ha]; exact mul_nonneg (mul_nonneg (hr0 i).le (hc0 i j)) (hτ i j).le
        obtain ⟨w, hw⟩ : ∃ w : TTState n → ℝ, w = fun s =>
          (∏ i, r i ^ s.1 i) * ∏ i, ∏ j, (a i j ^ s.2 i j / ((s.2 i j).factorial : ℝ)) := ⟨_, rfl⟩
        have hw0 : ∀ s, 0 ≤ w s := by
          intro s
          rw [hw]
          refine mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (hr0 i).le _) ?_
          refine Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => ?_
          exact div_nonneg (pow_nonneg (ha0 i j) _) (Nat.cast_nonneg _)
        have W1 : ∀ (s : TTState n) i, w (s.1 + Pi.single i 1, s.2) = r i * w s := by
          intro s i
          simp only [hw, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
          have : ∏ x, r x ^ (Pi.single i 1 : Fin n → ℕ) x = r i := by
            rw [Finset.prod_eq_single i]
            · simp
            · intro b _ hb
              simp [Pi.single_eq_of_ne hb]
            · simp
          rw [this]; ring
        have W2 : ∀ (s : TTState n) i j,
            w (s.1, s.2 + linkUnit i j) * ((s.2 i j : ℝ) + 1) = a i j * w s := by
          intro s i j
          have hfac : ∀ x y, a x y ^ (s.2 + linkUnit i j) x y / (((s.2 + linkUnit i j) x y).factorial : ℝ)
              = (a x y ^ s.2 x y / ((s.2 x y).factorial : ℝ)) *
                (if x = i then (if y = j then a i j / ((s.2 i j : ℝ) + 1) else 1) else 1) := by
            intro x y
            by_cases hx : x = i
            · by_cases hy : y = j
              · subst hx; subst hy
                have hp : ((s.2 x y : ℝ) + 1) ≠ 0 := by positivity
                have hf : ((s.2 x y).factorial : ℝ) ≠ 0 := by positivity
                simp only [Pi.add_apply, linkUnit, and_self, if_true, pow_succ, Nat.factorial_succ]
                push_cast
                field_simp
              · simp [linkUnit, hx, hy]
            · simp [linkUnit, hx]
          have hp : ((s.2 i j : ℝ) + 1) ≠ 0 := by positivity
          simp only [hw]
          rw [Finset.prod_congr rfl fun x _ => Finset.prod_congr rfl fun y _ => hfac x y]
          simp only [Finset.prod_mul_distrib]
          have : ∏ x, ∏ y, (if x = i then (if y = j then a i j / ((s.2 i j : ℝ) + 1) else 1) else 1)
              = a i j / ((s.2 i j : ℝ) + 1) := by
            rw [Finset.prod_eq_single i]
            · simp
            · intro b _ hb
              simp [hb]
            · simp
          rw [this]
          field_simp
        have mem : ∀ (M : ℕ) (s : TTState n), s ∈ ttStates n M ↔
            (∑ i, s.1 i) + (∑ i, ∑ j, s.2 i j) = M := by
          intro M s
          simp only [ttStates, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset,
            Finset.mem_range, and_iff_right_iff_imp]
          intro h
          refine ⟨fun i => ?_, fun i j => ?_⟩
          · have := Finset.single_le_sum (f := fun i => s.1 i) (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
            omega
          · have h1 := Finset.single_le_sum (f := fun j => s.2 i j) (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
            have h2 := Finset.single_le_sum (f := fun i => ∑ j, s.2 i j) (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
            omega
        have sumx : ∀ (x : Fin n → ℕ) i, ∑ k, (x + Pi.single i 1 : Fin n → ℕ) k = (∑ k, x k) + 1 := by
          intro x i
          simp [Finset.sum_add_distrib]
        have sumy : ∀ (y : Fin n → Fin n → ℕ) i j,
            ∑ k, ∑ l, (y + linkUnit i j : Fin n → Fin n → ℕ) k l = (∑ k, ∑ l, y k l) + 1 := by
          intro y i j
          simp only [Pi.add_apply, Finset.sum_add_distrib]
          congr 1
          rw [Finset.sum_eq_single i]
          · simp [linkUnit]
          · intro b _ hb
            simp [linkUnit, hb]
          · simp
        have subx : ∀ (x : Fin n → ℕ) i, 0 < x i → x - Pi.single i 1 + Pi.single i 1 = x := by
          intro x i hx
          funext k
          by_cases hk : k = i
          · subst hk; simp; omega
          · simp [Pi.single_eq_of_ne hk]
        have suby : ∀ (y : Fin n → Fin n → ℕ) i j, 0 < y i j →
            y - linkUnit i j + linkUnit i j = y := by
          intro y i j hy
          funext k l
          by_cases hk : k = i ∧ l = j
          · obtain ⟨h1, h2⟩ := hk
            subst h1; subst h2; simp [linkUnit]; omega
          · simp [linkUnit, hk]
        have addx : ∀ (x : Fin n → ℕ) i, x + Pi.single i 1 - Pi.single i 1 = x := by
          intro x i; funext k; simp
        have addy : ∀ (y : Fin n → Fin n → ℕ) i j, y + linkUnit i j - linkUnit i j = y := by
          intro y i j; funext k l; simp
        have T1 : ∀ (M : ℕ) (s : TTState n) i, s ∈ ttStates n M ↔
            ((s.1 + Pi.single i 1, s.2) : TTState n) ∈ ttStates n (M + 1) := by
          intro M s i
          rw [mem, mem]
          have := sumx s.1 i
          simp only at this ⊢
          rw [this]; omega
        have T2 : ∀ (M : ℕ) (s : TTState n) i j, s ∈ ttStates n M ↔
            ((s.1, s.2 + linkUnit i j) : TTState n) ∈ ttStates n (M + 1) := by
          intro M s i j
          rw [mem, mem]
          have := sumy s.2 i j
          simp only at this ⊢
          rw [this]; omega
        have B1 : ∀ (M : ℕ) (F : TTState n → ℝ) i,
            ∑ s ∈ ttStates n (M + 1), (if 0 < s.1 i then F s else 0) =
              ∑ s ∈ ttStates n M, F (s.1 + Pi.single i 1, s.2) := by
          intro M F i
          rw [← Finset.sum_filter]
          symm
          refine Finset.sum_nbij' (fun s => (s.1 + Pi.single i 1, s.2))
            (fun s => (s.1 - Pi.single i 1, s.2)) ?_ ?_ ?_ ?_ ?_
          · intro s hs
            rw [Finset.mem_filter]
            refine ⟨(T1 M s i).1 hs, ?_⟩
            simp
          · intro s hs
            rw [Finset.mem_filter] at hs
            rw [T1 M _ i]
            simp only
            rw [subx _ _ hs.2]
            exact hs.1
          · intro s _
            simp only [addx]
          · intro s hs
            rw [Finset.mem_filter] at hs
            simp only
            rw [subx _ _ hs.2]
          · intro s _
            rfl
        have B2 : ∀ (M : ℕ) (F : TTState n → ℝ) i j,
            ∑ s ∈ ttStates n (M + 1), (if 0 < s.2 i j then F s else 0) =
              ∑ s ∈ ttStates n M, F (s.1, s.2 + linkUnit i j) := by
          intro M F i j
          rw [← Finset.sum_filter]
          symm
          refine Finset.sum_nbij' (fun s => (s.1, s.2 + linkUnit i j))
            (fun s => (s.1, s.2 - linkUnit i j)) ?_ ?_ ?_ ?_ ?_
          · intro s hs
            rw [Finset.mem_filter]
            refine ⟨(T2 M s i j).1 hs, ?_⟩
            simp [linkUnit]
          · intro s hs
            rw [Finset.mem_filter] at hs
            rw [T2 M _ i j]
            simp only
            rw [suby _ _ _ hs.2]
            exact hs.1
          · intro s _
            simp only [addy]
          · intro s hs
            rw [Finset.mem_filter] at hs
            simp only
            rw [suby _ _ _ hs.2]
          · intro s _
            rfl
        have D1 : ∀ (s : TTState n) i j, 0 < s.1 i → s ∈ ttStates n m →
            ((s.1 - Pi.single i 1, s.2 + linkUnit i j) : TTState n) ∈ ttStates n m := by
          intro s i j hi hs
          obtain ⟨M, hM⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
          rw [hM] at hs ⊢
          rw [← T2 M (s.1 - Pi.single i 1, s.2) i j, T1 M _ i]
          simp only
          rw [subx _ _ hi]
          exact hs
        have D2 : ∀ (s : TTState n) i j k, 0 < s.2 i j → s ∈ ttStates n m →
            ((s.1 + Pi.single k 1, s.2 - linkUnit i j) : TTState n) ∈ ttStates n m := by
          intro s i j k hi hs
          obtain ⟨M, hM⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
          rw [hM] at hs ⊢
          rw [← T1 M (s.1, s.2 - linkUnit i j) k, T2 M _ i j]
          simp only
          rw [suby _ _ _ hi]
          exact hs
        have In1 : ∀ s ∈ ttStates n m, ∀ i j, ∑ t ∈ ttStates n m, w t *
            (if 0 < t.1 i ∧ s = (t.1 - Pi.single i 1, t.2 + linkUnit i j) then
              φ i j * toTTPolicy q t i j else 0) =
            (if 0 < s.2 i j then (s.2 i j : ℝ) / τ i j * w s else 0) := by
          intro s hs i j
          by_cases hp : 0 < s.2 i j
          · rw [if_pos hp, Finset.sum_eq_single ((s.1 + Pi.single i 1, s.2 - linkUnit i j) : TTState n)]
            · have h1 : 0 < (s.1 + Pi.single i 1 : Fin n → ℕ) i := by simp
              simp only
              rw [if_pos ⟨h1, by rw [addx, suby _ _ _ hp]⟩]
              simp only [toTTPolicy, toPolicy]
              rw [if_pos h1]
              have e1 := W1 (s.1, s.2 - linkUnit i j) i
              have e2 := W2 (s.1, s.2 - linkUnit i j) i j
              simp only at e1 e2
              rw [suby _ _ _ hp] at e2
              have e3 : (((s.2 - linkUnit i j) i j : ℕ) : ℝ) + 1 = (s.2 i j : ℝ) := by
                have : (s.2 - linkUnit i j) i j + 1 = s.2 i j := by simp [linkUnit]; omega
                exact_mod_cast this
              rw [e3] at e2
              rw [e1]
              have e4 : w s * (s.2 i j : ℝ) = a i j * w (s.1, s.2 - linkUnit i j) := e2
              have hτ' := (hτ i j).ne'
              have : (s.2 i j : ℝ) / τ i j * w s = (w s * (s.2 i j : ℝ)) / τ i j := by ring
              rw [this, e4, ha, hc]
              field_simp
            · intro t _ ht
              rw [if_neg, mul_zero]
              rintro ⟨h1, h2⟩
              apply ht
              rw [h2]
              simp only
              rw [subx _ _ h1, addy]
            · intro h
              exact absurd (D2 s i j i hp hs) h
          · rw [if_neg hp]
            refine Finset.sum_eq_zero fun t _ => ?_
            rw [if_neg, mul_zero]
            rintro ⟨h1, h2⟩
            apply hp
            rw [h2]
            simp [linkUnit]
        have In2 : ∀ s ∈ ttStates n m, ∀ i j, ∑ t ∈ ttStates n m, w t *
            (if 0 < t.2 i j ∧ s = (t.1 + Pi.single j 1, t.2 - linkUnit i j) then
              (t.2 i j : ℝ) / τ i j else 0) =
            (if 0 < s.1 j then r i * c i j / r j * w s else 0) := by
          intro s hs i j
          by_cases hp : 0 < s.1 j
          · rw [if_pos hp, Finset.sum_eq_single ((s.1 - Pi.single j 1, s.2 + linkUnit i j) : TTState n)]
            · have h1 : 0 < (s.2 + linkUnit i j) i j := by simp [linkUnit]
              simp only
              rw [if_pos ⟨h1, by rw [addy, subx _ _ hp]⟩]
              have e1 := W1 (s.1 - Pi.single j 1, s.2) j
              have e2 := W2 (s.1 - Pi.single j 1, s.2) i j
              simp only at e1 e2
              rw [subx _ _ hp] at e1
              have e3 : (((s.2 + linkUnit i j) i j : ℕ) : ℝ) = (s.2 i j : ℝ) + 1 := by
                simp [linkUnit]
              rw [e3]
              have e4 : w s = r j * w (s.1 - Pi.single j 1, s.2) := e1
              rw [e4]
              have hτ' := (hτ i j).ne'
              have hr' := (hr0 j).ne'
              have : w (s.1 - Pi.single j 1, s.2 + linkUnit i j) * (((s.2 i j : ℝ) + 1) / τ i j)
                = (w (s.1 - Pi.single j 1, s.2 + linkUnit i j) * ((s.2 i j : ℝ) + 1)) / τ i j := by ring
              rw [this, e2, ha]
              field_simp
            · intro t _ ht
              rw [if_neg, mul_zero]
              rintro ⟨h1, h2⟩
              apply ht
              rw [h2]
              simp only
              rw [suby _ _ _ h1, addx]
            · intro h
              exact absurd (D1 s j i hp hs) (by
                intro _
                apply h
                obtain ⟨M, hM⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
                rw [hM] at hs ⊢
                rw [← T2 M (s.1 - Pi.single j 1, s.2) i j, T1 M _ j]
                simp only
                rw [subx _ _ hp]
                exact hs)
          · rw [if_neg hp]
            refine Finset.sum_eq_zero fun t _ => ?_
            rw [if_neg, mul_zero]
            rintro ⟨h1, h2⟩
            apply hp
            rw [h2]
            simp
        have Out : ∀ s ∈ ttStates n m, ∑ t ∈ ttStates n m, ttRate φ τ (toTTPolicy q) s t =
            ∑ i, ∑ j, ((if 0 < s.1 i then c i j else 0) +
              (if 0 < s.2 i j then (s.2 i j : ℝ) / τ i j else 0)) := by
          intro s hs
          simp only [ttRate]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_add_distrib]
          congr 1
          · by_cases hp : 0 < s.1 i
            · simp only [hp, true_and, if_true]
              rw [Finset.sum_ite_eq', if_pos (D1 s i j hp hs)]
              simp [toTTPolicy, toPolicy, hp, hc]
            · simp [hp]
          · by_cases hp : 0 < s.2 i j
            · simp only [hp, true_and, if_true]
              rw [Finset.sum_ite_eq', if_pos (D2 s i j j hp hs)]
            · simp [hp]
        have Bal : ∀ s ∈ ttStates n m, w s * ∑ t ∈ ttStates n m, ttRate φ τ (toTTPolicy q) s t =
            ∑ t ∈ ttStates n m, w t * ttRate φ τ (toTTPolicy q) t s := by
          intro s hs
          rw [Out s hs]
          have e1 : ∑ t ∈ ttStates n m, w t * ttRate φ τ (toTTPolicy q) t s =
              ∑ i, ∑ j, ((if 0 < s.2 i j then (s.2 i j : ℝ) / τ i j * w s else 0) +
                (if 0 < s.1 j then r i * c i j / r j * w s else 0)) := by
            simp only [ttRate, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← In1 s hs i j, ← In2 s hs i j, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [mul_add]
          rw [e1]
          simp only [Finset.sum_add_distrib, mul_add]
          rw [add_comm]
          congr 1
          · simp only [Finset.mul_sum, mul_ite, mul_zero]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [mul_comm]
          · rw [Finset.mul_sum]
            rw [Finset.sum_comm (f := fun i j => if 0 < s.1 j then r i * c i j / r j * w s else 0)]
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases hp : 0 < s.1 j
            · simp only [hp, if_true]
              have hr' := (hr0 j).ne'
              have : ∑ i, r i * c i j / r j * w s = (∑ i, r i * c i j) / r j * w s := by
                rw [Finset.sum_div, Finset.sum_mul]
              rw [this, hr j]
              field_simp
            · simp [hp]
        have rate0 : ∀ s i j, 0 ≤ ((0 : ℝ) + (if 0 < s.1 i then c i j else 0)) ∧
            0 ≤ φ i j * toTTPolicy q s i j := by
          intro s i j
          refine ⟨?_, ?_⟩
          · split_ifs
            · simpa using hc0 i j
            · simp
          · refine mul_nonneg (hφ i j) ?_
            simp only [toTTPolicy, toPolicy]
            split_ifs
            · exact (hq i j).1
            · exact le_rfl
        have term0 : ∀ (s t : TTState n) i j, 0 ≤
            ((if 0 < s.1 i ∧ t = (s.1 - Pi.single i 1, s.2 + linkUnit i j) then
                φ i j * toTTPolicy q s i j else 0) +
            (if 0 < s.2 i j ∧ t = (s.1 + Pi.single j 1, s.2 - linkUnit i j) then
              (s.2 i j : ℝ) / τ i j else 0)) := by
          intro s t i j
          refine add_nonneg ?_ ?_
          · split_ifs
            · exact (rate0 s i j).2
            · exact le_rfl
          · split_ifs
            · exact div_nonneg (Nat.cast_nonneg _) (hτ i j).le
            · exact le_rfl
        have rateNN : ∀ s t, 0 ≤ ttRate φ τ (toTTPolicy q) s t := by
          intro s t
          exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => term0 s t i j
        have rateGe : ∀ (s t : TTState n) i j,
            ((if 0 < s.1 i ∧ t = (s.1 - Pi.single i 1, s.2 + linkUnit i j) then
                φ i j * toTTPolicy q s i j else 0) +
            (if 0 < s.2 i j ∧ t = (s.1 + Pi.single j 1, s.2 - linkUnit i j) then
              (s.2 i j : ℝ) / τ i j else 0)) ≤ ttRate φ τ (toTTPolicy q) s t := by
          intro s t i j
          unfold ttRate
          refine le_trans ?_ (Finset.single_le_sum
            (fun i _ => Finset.sum_nonneg fun j _ => term0 s t i j) (Finset.mem_univ i))
          exact Finset.single_le_sum (f := fun j => ((if 0 < s.1 i ∧ t = (s.1 - Pi.single i 1, s.2 + linkUnit i j) then
                φ i j * toTTPolicy q s i j else 0) +
            (if 0 < s.2 i j ∧ t = (s.1 + Pi.single j 1, s.2 - linkUnit i j) then
              (s.2 i j : ℝ) / τ i j else 0))) (fun j _ => term0 s t i j) (Finset.mem_univ j)
        have R1 : ∀ (s : TTState n) i j, 0 < s.1 i → 0 < c i j →
            0 < ttRate φ τ (toTTPolicy q) s (s.1 - Pi.single i 1, s.2 + linkUnit i j) := by
          intro s i j hs hcc
          refine lt_of_lt_of_le ?_ (rateGe s _ i j)
          refine add_pos_of_pos_of_nonneg ?_ ?_
          · rw [if_pos ⟨hs, rfl⟩]
            simp only [toTTPolicy, toPolicy]
            rw [if_pos hs]
            rw [hc] at hcc; exact hcc
          · split_ifs
            · exact div_nonneg (Nat.cast_nonneg _) (hτ i j).le
            · exact le_rfl
        have R2 : ∀ (s : TTState n) i j, 0 < s.2 i j →
            0 < ttRate φ τ (toTTPolicy q) s (s.1 + Pi.single j 1, s.2 - linkUnit i j) := by
          intro s i j hs
          refine lt_of_lt_of_le ?_ (rateGe s _ i j)
          refine add_pos_of_nonneg_of_pos ?_ ?_
          · split_ifs
            · exact (rate0 s i j).2
            · exact le_rfl
          · rw [if_pos ⟨hs, rfl⟩]
            exact div_pos (Nat.cast_pos.2 hs) (hτ i j)
        obtain ⟨π0, πoff, πsum, πbal⟩ := hπ
        have πBal : ∀ s ∈ ttStates n m, π s * ∑ t ∈ ttStates n m, ttRate φ τ (toTTPolicy q) s t =
            ∑ t ∈ ttStates n m, π t * ttRate φ τ (toTTPolicy q) t s := by
          intro s hs
          have := πbal ⟨s, hs⟩
          rw [tsum_fintype, tsum_fintype] at this
          rw [← Finset.sum_coe_sort (ttStates n m), ← Finset.sum_coe_sort (ttStates n m)]
          exact this
        obtain ⟨s0, hs0⟩ : ∃ s0 : TTState n, s0 = (Pi.single 0 m, 0) := ⟨_, rfl⟩
        obtain ⟨D, hD⟩ : ∃ D : TTState n → ℝ, D = fun s => π s * w s0 - π s0 * w s := ⟨_, rfl⟩
        have DBal : ∀ s ∈ ttStates n m, D s * ∑ t ∈ ttStates n m, ttRate φ τ (toTTPolicy q) s t =
            ∑ t ∈ ttStates n m, D t * ttRate φ τ (toTTPolicy q) t s := by
          intro s hs
          have e : ∑ t ∈ ttStates n m, D t * ttRate φ τ (toTTPolicy q) t s =
              w s0 * (∑ t ∈ ttStates n m, π t * ttRate φ τ (toTTPolicy q) t s) -
              π s0 * (∑ t ∈ ttStates n m, w t * ttRate φ τ (toTTPolicy q) t s) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [hD]; ring
          rw [e, ← πBal s hs, ← Bal s hs, hD]; ring
        have Dstep : ∀ s ∈ ttStates n m, ∀ t ∈ ttStates n m, D t = 0 →
            0 < ttRate φ τ (toTTPolicy q) s t → D s = 0 := by
          intro s hs t ht h1 h2
          refine (key {s // s ∈ ttStates n m} (fun s t => ttRate φ τ (toTTPolicy q) s t)
            (fun s t => rateNN s t) (fun s => D s) ?_).2 ⟨s, hs⟩ ⟨t, ht⟩ h1 h2
          intro s
          have := DBal s s.2
          rw [← Finset.sum_coe_sort (ttStates n m), ← Finset.sum_coe_sort (ttStates n m)] at this
          exact this
        have D00 : D s0 = 0 := by rw [hD]; ring
        have Dmove : ∀ i, ∀ x : Fin n → ℕ, 0 < x i → ((x, 0) : TTState n) ∈ ttStates n m →
            D (x - Pi.single i 1 + Pi.single 0 1, 0) = 0 → D (x, 0) = 0 := by
          intro i
          have hp := hconn i 0
          induction hp using Relation.ReflTransGen.head_induction_on with
          | refl =>
            intro x hx _ h
            rwa [subx _ _ hx] at h
          | @head i b hab _ ih =>
            intro x hx hmem h
            have hcc : 0 < c i b := by rw [hc]; exact hab.2
            have hm1 := D1 (x, 0) i b hx hmem
            have hy : 0 < ((0 : Fin n → Fin n → ℕ) + linkUnit i b) i b := by simp [linkUnit]
            have hm2 := D2 _ i b b hy hm1
            simp only at hm1 hm2
            rw [addy] at hm2
            have h1 : D (x - Pi.single i 1 + Pi.single b 1, 0) = 0 := by
              refine ih _ (by simp) hm2 ?_
              rw [addx]
              exact h
            have hr2 := R2 (x - Pi.single i 1, 0 + linkUnit i b) i b hy
            simp only at hr2
            rw [addy] at hr2
            have h2 := Dstep _ hm1 _ hm2 h1 hr2
            exact Dstep _ hmem _ hm1 h2 (R1 (x, 0) i b hx hcc)
        have Dx : ∀ k, ∀ x : Fin n → ℕ, m - x 0 = k → ((x, 0) : TTState n) ∈ ttStates n m →
            D (x, 0) = 0 := by
          intro k
          induction k with
          | zero =>
            intro x hk hmem
            have hs := (mem _ _).1 hmem
            simp at hs
            have hx : x = Pi.single 0 m := by
              have h1 := Finset.add_sum_erase (univ : Finset (Fin n)) x (Finset.mem_univ 0)
              have h0 : ∑ i ∈ univ.erase 0, x i = 0 := by omega
              have h2 := Finset.sum_eq_zero_iff.1 h0
              funext i
              by_cases hi : i = 0
              · subst hi; simp; omega
              · rw [Pi.single_eq_of_ne hi]
                exact h2 i (by simp [hi])
            rw [hx, ← hs0]; exact D00
          | succ k ih =>
            intro x hk hmem
            have hs := (mem _ _).1 hmem
            simp at hs
            have h1 := Finset.add_sum_erase (univ : Finset (Fin n)) x (Finset.mem_univ 0)
            have hne : ∑ i ∈ univ.erase 0, x i ≠ 0 := by omega
            obtain ⟨i, hi, hxi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
            have hi0 : i ≠ 0 := by simpa using hi
            have hxp : 0 < x i := Nat.pos_of_ne_zero hxi
            refine Dmove i x hxp hmem (ih _ ?_ ?_)
            · simp [Pi.single_eq_of_ne hi0.symm]
              omega
            · have hm1 := D1 (x, 0) i 0 hxp hmem
              have hy : 0 < ((0 : Fin n → Fin n → ℕ) + linkUnit i 0) i 0 := by simp [linkUnit]
              have hm2 := D2 _ i 0 0 hy hm1
              simp only at hm2
              rw [addy] at hm2
              exact hm2
        have Dall : ∀ k, ∀ s : TTState n, ∑ i, ∑ j, s.2 i j = k → s ∈ ttStates n m → D s = 0 := by
          intro k
          induction k with
          | zero =>
            intro s hk hmem
            have : s.2 = 0 := by
              funext i j
              have h1 := Finset.sum_eq_zero_iff.1 hk i (Finset.mem_univ i)
              exact Finset.sum_eq_zero_iff.1 h1 j (Finset.mem_univ j)
            have hs : s = (s.1, 0) := by rw [← this]
            rw [hs] at hmem ⊢
            exact Dx _ _ rfl hmem
          | succ k ih =>
            intro s hk hmem
            have hne : ∑ i, ∑ j, s.2 i j ≠ 0 := by omega
            obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
            obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
            have hp : 0 < s.2 i j := Nat.pos_of_ne_zero hj
            have hm2 := D2 s i j j hp hmem
            refine Dstep s hmem _ hm2 (ih _ ?_ hm2) (R2 s i j hp)
            have := sumy (s.2 - linkUnit i j) i j
            rw [suby _ _ _ hp] at this
            simp only
            omega
        have ws0 : 0 < w s0 := by
          rw [hw, hs0]
          simp only
          refine mul_pos (Finset.prod_pos fun i _ => pow_pos (hr0 i) _) ?_
          simp
        have hs0m : s0 ∈ ttStates n m := by
          rw [mem, hs0]; simp
        have hprop : ∀ s ∈ ttStates n m, π s * w s0 = π s0 * w s := by
          intro s hs
          have := Dall _ s rfl hs
          rw [hD] at this
          simp only at this
          linarith
        obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑ s ∈ ttStates n m, w s := ⟨_, rfl⟩
        have hWpos : 0 < W := by
          rw [hW]
          exact Finset.sum_pos' (fun s _ => hw0 s) ⟨s0, hs0m, ws0⟩
        have hW1 : w s0 = π s0 * W := by
          rw [hW, Finset.mul_sum, ← Finset.sum_congr rfl hprop, ← Finset.sum_mul, πsum, one_mul]
        have hπw : ∀ s ∈ ttStates n m, π s = w s / W := by
          intro s hs
          have h1 := hprop s hs
          rw [hW1] at h1
          have h2 : π s0 ≠ 0 := by
            intro h; rw [h, zero_mul] at hW1; exact ws0.ne' hW1
          rw [eq_div_iff hWpos.ne']
          apply mul_left_cancel₀ h2
          linarith
        clear Dall Dx Dmove D00 Dstep DBal hD D hs0 hs0m ws0 hprop hW1 R1 R2 rateGe rateNN term0 rate0 Bal Out In1 In2 πBal πbal s0 key
        obtain ⟨M, hM⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
        obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = ∑ i, ∑ j, a i j := ⟨_, rfl⟩
        obtain ⟨N, hN⟩ : ∃ N : TTState n → ℕ, N = fun s => ∑ i, ∑ j, s.2 i j := ⟨_, rfl⟩
        obtain ⟨X, hX⟩ : ∃ X : TTState n → ℕ, X = fun s => ∑ i, s.1 i := ⟨_, rfl⟩
        have memXN : ∀ (M : ℕ) (s : TTState n), s ∈ ttStates n M ↔ X s + N s = M := by
          intro M s; rw [mem, hX, hN]
        have NL : ∀ s i j, N (s.1, s.2 + linkUnit i j) = N s + 1 := by
          intro s i j; rw [hN]; exact sumy s.2 i j
        have NX : ∀ s i, N (s.1 + Pi.single i 1, s.2) = N s := by
          intro s i; rw [hN]
        have Little : ∀ g : ℕ → ℝ, ∑ s ∈ ttStates n m, w s * N s * g (N s) =
            Λ * ∑ s ∈ ttStates n M, w s * g (N s + 1) := by
          intro g
          have e1 : ∀ i j, ∑ s ∈ ttStates n m, w s * (s.2 i j : ℝ) * g (N s) =
              a i j * ∑ s ∈ ttStates n M, w s * g (N s + 1) := by
            intro i j
            have e2 : ∑ s ∈ ttStates n m, w s * (s.2 i j : ℝ) * g (N s) =
                ∑ s ∈ ttStates n m, (if 0 < s.2 i j then w s * (s.2 i j : ℝ) * g (N s) else 0) := by
              refine Finset.sum_congr rfl fun s _ => ?_
              split_ifs with h
              · rfl
              · have : s.2 i j = 0 := by omega
                rw [this]; simp
            rw [e2, hM, B2 M (fun s => w s * (s.2 i j : ℝ) * g (N s)) i j, Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            have e3 := W2 s i j
            have e4 : (((s.2 + linkUnit i j) i j : ℕ) : ℝ) = (s.2 i j : ℝ) + 1 := by
              simp [linkUnit]
            simp only
            rw [e4, e3, NL]; ring
          rw [hΛ, Finset.sum_mul]
          simp only [Finset.sum_mul, ← e1]
          have e5 : ∀ s : TTState n, w s * (N s : ℝ) * g (N s) =
              ∑ i, ∑ j, w s * (s.2 i j : ℝ) * g (N s) := by
            intro s
            have : (N s : ℝ) = ∑ i, ∑ j, (s.2 i j : ℝ) := by rw [hN]; push_cast; rfl
            rw [this]
            simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_congr rfl fun s _ => e5 s, Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
        obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ s ∈ ttStates n M, w s := ⟨_, rfl⟩
        have Busy : ∀ h : ℕ → ℝ, ∑ s ∈ ttStates n m, (if 0 < s.1 i0 then w s * h (N s) else 0) =
            ∑ s ∈ ttStates n M, w s * h (N s) := by
          intro h
          rw [hM, B1 M (fun s => w s * h (N s)) i0]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [W1, NX, hri0, one_mul]
        have Avail : A / W ≤ ttMaxAvailability m π := by
          have hA1 : ∑ s ∈ (ttStates n m).filter (fun s => 0 < s.1 i0), π s ≤ ttMaxAvailability m π := by
            rw [ttMaxAvailability]
            exact Finset.le_sup' (fun i => ∑ s ∈ (ttStates n m).filter (fun s => 0 < s.1 i), π s)
              (Finset.mem_univ i0)
          have hA2 : ∑ s ∈ (ttStates n m).filter (fun s => 0 < s.1 i0), π s =
              ∑ s ∈ (ttStates n m).filter (fun s => 0 < s.1 i0), w s / W :=
            Finset.sum_congr rfl fun s hs => hπw s (Finset.mem_filter.1 hs).1
          have hA3 : ∑ s ∈ (ttStates n m).filter (fun s => 0 < s.1 i0), w s = A := by
            rw [Finset.sum_filter, hA]
            have hb := Busy (fun _ => 1)
            simpa using hb
          rw [← hA3, Finset.sum_div, ← hA2]
          exact hA1
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.one_le
        have Main : ∑ s ∈ ttStates n m, w s * ((X s : ℝ) / ((X s : ℝ) + n - 1)) ≤ A := by
          have e1 : ∀ (h : ℕ → ℝ) i, ∑ s ∈ ttStates n m, w s * (s.1 i : ℝ) * h (N s) =
              r i * ∑ s ∈ ttStates n M, w s * ((s.1 i : ℝ) + 1) * h (N s) := by
            intro h i
            have e2 : ∑ s ∈ ttStates n m, w s * (s.1 i : ℝ) * h (N s) =
                ∑ s ∈ ttStates n m, (if 0 < s.1 i then w s * (s.1 i : ℝ) * h (N s) else 0) := by
              refine Finset.sum_congr rfl fun s _ => ?_
              split_ifs with h
              · rfl
              · have : s.1 i = 0 := by omega
                rw [this]; simp
            rw [e2, hM, B1 M (fun s => w s * (s.1 i : ℝ) * h (N s)) i, Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            simp only
            rw [W1, NX]
            have e4 : (((s.1 + Pi.single i 1 : Fin n → ℕ) i : ℕ) : ℝ) = (s.1 i : ℝ) + 1 := by
              simp
            rw [e4]; ring
          obtain ⟨h, hh⟩ : ∃ h : ℕ → ℝ, h = fun k : ℕ => 1 / ((m : ℝ) - (k : ℝ) + n - 1) := ⟨_, rfl⟩
          have hhM : ∀ s ∈ ttStates n M, 0 < (X s : ℝ) + n ∧ h (N s) = 1 / ((X s : ℝ) + n) := by
            intro s hs
            have h1 := (memXN M s).1 hs
            have h2 : (m : ℝ) = (X s : ℝ) + N s + 1 := by rw [hM, ← h1]; push_cast; ring
            refine ⟨by have : (0 : ℝ) ≤ X s := Nat.cast_nonneg _
                       linarith only [this, hn1], ?_⟩
            rw [hh]; simp only; rw [h2]; congr 1; ring
          have hhm : ∀ s ∈ ttStates n m, h (N s) = 1 / ((X s : ℝ) + n - 1) := by
            intro s hs
            have h1 := (memXN m s).1 hs
            have h2 : (m : ℝ) = (X s : ℝ) + N s := by rw [← h1]; push_cast; ring
            rw [hh]; simp only; rw [h2]; congr 1; ring
          calc ∑ s ∈ ttStates n m, w s * ((X s : ℝ) / ((X s : ℝ) + n - 1))
              = ∑ s ∈ ttStates n m, ∑ i, w s * (s.1 i : ℝ) * h (N s) := by
                refine Finset.sum_congr rfl fun s hs => ?_
                rw [hhm s hs]
                have : (X s : ℝ) = ∑ i, (s.1 i : ℝ) := by rw [hX]; push_cast; rfl
                rw [← Finset.sum_mul, ← Finset.mul_sum, ← this]
                ring
            _ = ∑ i, r i * ∑ s ∈ ttStates n M, w s * ((s.1 i : ℝ) + 1) * h (N s) := by
                rw [Finset.sum_comm]
                exact Finset.sum_congr rfl fun i _ => e1 h i
            _ ≤ ∑ i, ∑ s ∈ ttStates n M, w s * ((s.1 i : ℝ) + 1) * h (N s) := by
                refine Finset.sum_le_sum fun i _ => ?_
                refine mul_le_of_le_one_left (Finset.sum_nonneg fun s hs => ?_) (hr1 i)
                obtain ⟨h1, h2⟩ := hhM s hs
                rw [h2]
                exact mul_nonneg (mul_nonneg (hw0 s) (add_nonneg (Nat.cast_nonneg _) zero_le_one)) (one_div_nonneg.2 h1.le)
            _ = A := by
                rw [Finset.sum_comm, hA]
                refine Finset.sum_congr rfl fun s hs => ?_
                obtain ⟨h1, h2⟩ := hhM s hs
                have : (X s : ℝ) = ∑ i, (s.1 i : ℝ) := by rw [hX]; push_cast; rfl
                rw [← Finset.sum_mul, ← Finset.mul_sum, h2, Finset.sum_add_distrib, ← this]
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
                field_simp
        have hΛ0 : 0 ≤ Λ := by
          rw [hΛ]; exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ha0 i j
        obtain ⟨P, hP⟩ : ∃ P : ℝ → ℝ, P = fun z => ∑ s ∈ ttStates n m, w s * z ^ N s := ⟨_, rfl⟩
        obtain ⟨P', hP'⟩ : ∃ P' : ℝ → ℝ, P' = fun z => ∑ s ∈ ttStates n m, w s * N s * z ^ (N s - 1) :=
          ⟨_, rfl⟩
        have hder : ∀ z, HasDerivAt P (P' z) z := by
          intro z
          rw [hP, hP']
          refine HasDerivAt.fun_sum fun s _ => ?_
          have := (hasDerivAt_pow (N s) z).const_mul (w s)
          simpa [mul_assoc] using this
        have hPle : ∀ z, 0 ≤ z → P' z ≤ Λ * P z := by
          intro z hz
          rw [hP']
          beta_reduce
          rw [Little (fun k => z ^ (k - 1))]
          refine mul_le_mul_of_nonneg_left ?_ hΛ0
          simp only [Nat.add_sub_cancel]
          rw [← Busy (fun k => z ^ k), hP]
          refine Finset.sum_le_sum fun s _ => ?_
          split_ifs
          · exact le_rfl
          · exact mul_nonneg (hw0 s) (pow_nonneg hz _)
        have hP1 : P 1 = W := by rw [hP, hW]; simp
        have hMGF : ∀ z, 1 ≤ z → P z ≤ W * Real.exp (Λ * (z - 1)) := by
          intro z hz
          have hd : ∀ y, HasDerivAt (fun y => P y * Real.exp (-(Λ * y)))
              (P' y * Real.exp (-(Λ * y)) + P y * (Real.exp (-(Λ * y)) * (-Λ))) y := by
            intro y
            refine (hder y).mul ?_
            refine HasDerivAt.exp ?_
            simpa only [mul_one, neg_mul] using (hasDerivAt_id' y).const_mul (-Λ)
          have hanti : AntitoneOn (fun y => P y * Real.exp (-(Λ * y))) (Set.Ici 1) := by
            refine antitoneOn_of_deriv_nonpos (convex_Ici 1)
              (fun y _ => (hd y).continuousAt.continuousWithinAt)
              (fun y _ => (hd y).differentiableAt.differentiableWithinAt) ?_
            intro y hy
            rw [interior_Ici] at hy
            rw [(hd y).deriv]
            have h1 := hPle y (le_trans zero_le_one (le_of_lt hy))
            have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(Λ * y))).le
            linarith only [h2]
          have h := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hz) hz
          simp only [mul_one] at h
          rw [hP1] at h
          have h2 : P z = P z * Real.exp (-(Λ * z)) * Real.exp (Λ * z) := by
            rw [mul_assoc, ← Real.exp_add]; simp
          rw [h2]
          calc P z * Real.exp (-(Λ * z)) * Real.exp (Λ * z) ≤ W * Real.exp (-Λ) * Real.exp (Λ * z) :=
                mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
            _ = W * Real.exp (Λ * (z - 1)) := by
                rw [mul_assoc, ← Real.exp_add]; congr 2; ring
        obtain ⟨K, hK⟩ : ∃ K : ℝ, K = Real.sqrt (m * Real.log m) := ⟨_, rfl⟩
        rw [← hK] at hload ⊢
        have hm' : (100 : ℝ) ≤ m := by exact_mod_cast hm
        have hlog : 0 < Real.log m := Real.log_pos (by linarith only [hm'])
        have hK2 : K ^ 2 = m * Real.log m := by
          rw [hK, Real.sq_sqrt]; positivity
        have hKpos : 0 < K := by rw [hK]; exact Real.sqrt_pos.2 (by positivity)
        obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Real.sqrt m := ⟨_, rfl⟩
        have hu2 : u ^ 2 = m := by rw [hu, Real.sq_sqrt]; positivity
        have hu10 : 10 ≤ u := by
          rw [hu]; apply Real.le_sqrt_of_sq_le; linarith only [hm']
        have hlogu : Real.log m = 2 * Real.log u := by
          rw [← hu2, Real.log_pow]; norm_num
        have hKm : 2 * K < m := by
          have h1 : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos (by linarith only [hu10])
          have h2 : 4 * Real.log m < m := by rw [hlogu, ← hu2]; nlinarith only [h1, hu10]
          have h3 : (2 * K) ^ 2 < (m : ℝ) ^ 2 := by
            have : (2 * K) ^ 2 = m * (4 * Real.log m) := by rw [mul_pow, hK2]; ring
            rw [this, sq]
            exact mul_lt_mul_of_pos_left h2 (by linarith only [hm'])
          exact lt_of_pow_lt_pow_left₀ 2 (by linarith only [hm']) h3
        have hΛL : Λ ≤ m - 2 * K := by
          refine le_trans ?_ hload
          rw [hΛ]
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [ha]
          simp only
          have e : φ i j * τ i j * q i j = c i j * τ i j := by rw [hc]; ring
          rw [e, mul_assoc]
          exact mul_le_of_le_one_left (mul_nonneg (hc0 i j) (hτ i j).le) (hr1 i)
        obtain ⟨b, hb⟩ : ∃ b : ℝ, b = m - K := ⟨_, rfl⟩
        have hbK : K < b := by linarith only [hb, hKm]
        have hb0 : 0 < b := by linarith only [hbK, hKpos]
        obtain ⟨z, hz⟩ : ∃ z : ℝ, z = b / (b - K) := ⟨_, rfl⟩
        have hz1 : 1 ≤ z := by
          rw [hz, le_div_iff₀ (by linarith only [hbK])]; linarith only [hKpos]
        have hlogz : K / b + (K / b) ^ 2 / 2 ≤ Real.log z := by
          have hx0 : 0 ≤ K / b := by positivity
          have hx1 : K / b < 1 := (div_lt_one hb0).2 hbK
          have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := K / b) (by rw [abs_of_nonneg hx0]; exact hx1)
          have h1 := sum_le_hasSum (Finset.range 2) (fun i _ => by positivity) hs
          have h2 : Real.log z = - Real.log (1 - K / b) := by
            rw [← Real.log_inv, hz]
            congr 1
            field_simp
          rw [h2]
          simp [Finset.sum_range_succ] at h1
          norm_num at h1
          linarith only [h1]
        have hTail : ∑ s ∈ ttStates n m, (if (X s : ℝ) < K then w s else 0) ≤ W * (1 / u) := by
          have hzb : 0 < Real.exp (b * Real.log z) := Real.exp_pos _
          have h1 : (∑ s ∈ ttStates n m, (if (X s : ℝ) < K then w s else 0)) * Real.exp (b * Real.log z)
              ≤ P z := by
            rw [Finset.sum_mul, hP]
            refine Finset.sum_le_sum fun s hs => ?_
            split_ifs with h
            · refine mul_le_mul_of_nonneg_left ?_ (hw0 s)
              have h2 : (X s : ℝ) + N s = m := by exact_mod_cast (memXN m s).1 hs
              have h3 : z ^ N s = Real.exp (N s * Real.log z) := by
                rw [mul_comm, Real.exp_mul, Real.exp_log (by linarith only [hz1]), Real.rpow_natCast]
              rw [h3]
              apply Real.exp_le_exp.2
              exact mul_le_mul_of_nonneg_right (by linarith only [hb, h, h2]) (Real.log_nonneg hz1)
            · rw [zero_mul]
              exact mul_nonneg (hw0 s) (pow_nonneg (by linarith only [hz1]) _)
          have h2 := h1.trans (hMGF z hz1)
          have h3 : Real.exp (Λ * (z - 1)) ≤ 1 / u * Real.exp (b * Real.log z) := by
            have e1 : 1 / u = Real.exp (-Real.log u) := by
              rw [Real.exp_neg, Real.exp_log (by linarith only [hu10]), one_div]
            rw [e1, ← Real.exp_add]
            apply Real.exp_le_exp.2
            have h4 : Λ * (z - 1) ≤ K := by
              have e2 : z - 1 = K / (b - K) := by
                rw [hz]
                have : b - K ≠ 0 := (sub_pos.2 hbK).ne'
                field_simp
                ring
              have e3 : Λ ≤ b - K := by linarith only [hΛL, hb]
              have e4 : 0 < b - K := by linarith only [hbK]
              calc Λ * (z - 1) ≤ (b - K) * (z - 1) := mul_le_mul_of_nonneg_right e3 (by linarith only [hz1])
                _ = K := by rw [e2]; field_simp
            have h5 : b * (K / b + (K / b) ^ 2 / 2) ≤ b * Real.log z :=
              mul_le_mul_of_nonneg_left hlogz hb0.le
            have h6 : b * (K / b + (K / b) ^ 2 / 2) = K + K ^ 2 / (2 * b) := by
              field_simp
            have h7 : Real.log u ≤ K ^ 2 / (2 * b) := by
              rw [le_div_iff₀ (by linarith only [hb0]), hK2, hlogu]
              have h8 : 0 ≤ Real.log u := by linarith only [hlog, hlogu]
              have h9 : b ≤ m := by linarith only [hb, hKpos]
              have h10 := mul_le_mul_of_nonneg_right h9 h8
              linarith only [h10]
            linarith only [h4, h5, h6, h7]
          have h4 : W * Real.exp (Λ * (z - 1)) ≤ W * (1 / u) * Real.exp (b * Real.log z) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left h3 hWpos.le
          exact le_of_mul_le_mul_right (h2.trans h4) hzb
        have hfrac0 : 0 ≤ K / (K + n - 1) := div_nonneg hKpos.le (by linarith only [hKpos, hn1])
        have hFin : (W - W * (1 / u)) * (K / (K + n - 1)) ≤ A := by
          refine le_trans ?_ Main
          have e1 : W - ∑ s ∈ ttStates n m, (if (X s : ℝ) < K then w s else 0) =
              ∑ s ∈ ttStates n m, (if (X s : ℝ) < K then 0 else w s) := by
            rw [hW, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun s _ => ?_
            split_ifs <;> ring
          calc (W - W * (1 / u)) * (K / (K + n - 1))
              ≤ (∑ s ∈ ttStates n m, (if (X s : ℝ) < K then 0 else w s)) * (K / (K + n - 1)) := by
                refine mul_le_mul_of_nonneg_right ?_ hfrac0
                rw [← e1]; linarith only [hTail]
            _ ≤ _ := by
                rw [Finset.sum_mul]
                refine Finset.sum_le_sum fun s _ => ?_
                have hXs : (0 : ℝ) ≤ X s := Nat.cast_nonneg _
                split_ifs with h
                · rw [zero_mul]
                  refine mul_nonneg (hw0 s) ?_
                  rcases hXs.eq_or_lt with h0 | h0
                  · rw [← h0]; simp
                  · exact div_nonneg hXs (by linarith only [h0, hn1])
                · refine mul_le_mul_of_nonneg_left ?_ (hw0 s)
                  rw [not_lt] at h
                  rw [div_le_div_iff₀ (by linarith only [hKpos, hn1]) (by linarith only [hKpos, hn1, h])]
                  have h8 := mul_le_mul_of_nonneg_right h (sub_nonneg.2 hn1)
                  linarith only [h8]
        refine le_trans ?_ Avail
        rw [le_div_iff₀ hWpos, ← hu]
        refine le_trans ?_ hFin
        have e : (1 - 3 / u) * (K / (K + n - 1)) * W = (W * (1 - 3 / u)) * (K / (K + n - 1)) := by ring
        rw [e]
        refine mul_le_mul_of_nonneg_right ?_ hfrac0
        have h1 : 1 / u ≤ 3 / u := by
          exact div_le_div_of_nonneg_right (by norm_num) (by linarith only [hu10])
        have h2 : W * (1 / u) ≤ W * (3 / u) := mul_le_mul_of_nonneg_left h1 hWpos.le
        linarith only [h2]
