-- Prove2me | solution 1 for SharedVehicleApprox.Pricing.Supplement.theorem_28
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:06:44.714366+00:00
-- url     : https://prove2.me/submissions/105ff50d-f917-484d-8edd-361cc586e2f4

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_PointPricing

open Finset QueueingFundamentals.Networks

open SharedVehicleApprox
open SharedVehicleApprox.Pricing
open SharedVehicleApprox.Pricing.Supplement

/-- Theorem 28, p. 37 (corrected: the graph `{(i, j) : φ_ij > 0}` is strongly connected, as App. A
assumes): the point quantiles returned by Algorithm 6 earn at least `m/(m+n−1)` times the objective
of every state-dependent point-pricing policy under every stationary law of it. -/
theorem solution {n m : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (I : Fin n → Fin n → ℝ → ℝ)
    (hR : ∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (rewardCurve I i j))
    (hconn : SupportConnected φ (fun _ _ => 1))
    (qt : Fin n → ℝ) (hopt : IsAlg6Optimal φ I qt)
    (πt : (Fin n → ℕ) → ℝ) (hπt : IsStationary n m φ (toPolicy (pointQuantile qt)) πt)
    (q : (Fin n → ℕ) → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ)
    (hq : IsPolicy n m (pointPolicy q)) (hπ : IsStationary n m φ (pointPolicy q) π) :
    (m : ℝ) / ((m : ℝ) + n - 1) * obj n m φ I (pointPolicy q) π ≤
      obj n m φ I (toPolicy (pointQuantile qt)) πt := by
        classical
        have memS : ∀ {k : ℕ} {x : Fin n → ℕ}, x ∈ states n k ↔ ∑ i, x i = k := by
          intro k x
          simp only [states, mem_filter, Fintype.mem_piFinset, mem_range]
          constructor
          · exact fun h => h.2
          · intro h
            refine ⟨?_, h⟩
            intro i
            have := single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin n))) => Nat.zero_le (x j)) (mem_univ i)
            omega
        let inc : (Fin n → ℕ) → Fin n → (Fin n → ℕ) := fun x i => Function.update x i (x i + 1)
        let dec : (Fin n → ℕ) → Fin n → (Fin n → ℕ) := fun x i => Function.update x i (x i - 1)
        have inc_apply : ∀ x i j, inc x i j = x j + if j = i then 1 else 0 := by
          intro x i j
          by_cases h : j = i <;> simp [inc, h]
        have sum_inc : ∀ x i, ∑ j, inc x i j = (∑ j, x j) + 1 := by
          intro x i
          simp [inc_apply, sum_add_distrib]
        have sum_dec : ∀ x i, 0 < x i → (∑ j, dec x i j) + 1 = ∑ j, x j := by
          intro x i hi
          have he : inc (dec x i) i = x := by
            ext j
            by_cases h : j = i <;> simp [inc, dec, h, Nat.sub_add_cancel hi]
          rw [← sum_inc, he]
        have inc_dec : ∀ x i, 0 < x i → inc (dec x i) i = x := by
          intro x i hi
          ext j
          by_cases h : j = i <;> simp [inc, dec, h, Nat.sub_add_cancel hi]
        have dec_inc : ∀ x i, dec (inc x i) i = x := by
          intro x i
          ext j
          by_cases h : j = i <;> simp [inc, dec, h]
        have move_inc : ∀ x i j, i ≠ j → moveState (inc x j) i j = inc x i := by
          intro x i j hij
          ext k
          by_cases hki : k = i
          · subst k; simp [moveState, inc, hij]
          · by_cases hkj : k = j
            · subst k; simp [moveState, inc, hij, Ne.symm hij]
            · simp [moveState, inc, hki]
        have move_mem : ∀ {k : ℕ} {x : Fin n → ℕ} (i j : Fin n),
            x ∈ states n k → i ≠ j → 1 ≤ x j → moveState x i j ∈ states n k := by
          intro k x i j hx hij hj
          rw [← inc_dec x j hj, move_inc _ _ _ hij]
          apply memS.mpr
          rw [sum_inc]
          have := sum_dec x j hj
          rw [memS.mp hx] at this
          omega
        have move_rev : ∀ (x : Fin n → ℕ) (i j : Fin n), i ≠ j → 1 ≤ x j → moveState (moveState x i j) j i = x := by
          intro x i j hij hj
          rw [← inc_dec x j hj, move_inc _ _ _ hij, move_inc _ _ _ hij.symm, inc_dec _ _ hj]
        have move_pos : ∀ (x : Fin n → ℕ) (i j : Fin n), 0 < moveState x i j i := by
          intro x i j
          simp [moveState]
        have reindex_move : ∀ (k : ℕ) (i j : Fin n) (hij : i ≠ j)
            (F : (Fin n → ℕ) → (Fin n → ℕ) → ℝ),
            (∑ x ∈ (states n k).filter (fun x => 1 ≤ x j), F x (moveState x i j)) =
            ∑ y ∈ (states n k).filter (fun y => 1 ≤ y i), F (moveState y j i) y := by
          intro k i j hij F
          apply sum_bij (fun x _ => moveState x i j)
          · intro x hx
            exact mem_filter.mpr ⟨move_mem i j (mem_filter.mp hx).1 hij (mem_filter.mp hx).2, move_pos x i j⟩
          · intro x hx y hy he
            have h1 := move_rev x i j hij (mem_filter.mp hx).2
            have h2 := move_rev y i j hij (mem_filter.mp hy).2
            rw [he] at h1
            exact h1.symm.trans h2
          · intro y hy
            refine ⟨moveState y j i, ?_, move_rev y j i hij.symm (mem_filter.mp hy).2⟩
            exact mem_filter.mpr ⟨move_mem j i (mem_filter.mp hy).1 hij.symm (mem_filter.mp hy).2, move_pos y j i⟩
          · intro x hx
            rw [move_rev x i j hij (mem_filter.mp hx).2]
        let T : (Fin n → ℕ) → Fin n → Fin n → (Fin n → ℕ) :=
          fun x i j => if i = j then x else moveState x j i
        have test_eq : ∀ (p : (Fin n → ℕ) → Fin n → Fin n → ℝ)
            (ρ : (Fin n → ℕ) → ℝ), IsPolicy n m p → IsStationary n m φ p ρ →
            ∀ v : (Fin n → ℕ) → ℝ,
            (∑ x ∈ states n m, ∑ i, ∑ j, ρ x * φ i j * p x i j * v x) =
            ∑ x ∈ states n m, ∑ i, ∑ j, ρ x * φ i j * p x i j * v (T x i j) := by
          intro p ρ hp hρ v
          have hpair : ∀ i j,
              (∑ x ∈ states n m, inflowTerm φ p ρ x i j * v x) =
              ∑ x ∈ states n m, ρ x * φ i j * p x i j * v (T x i j) := by
            intro i j
            by_cases hij : i = j
            · subst j; simp [inflowTerm, T]
            · simp only [inflowTerm, hij, ↓reduceIte, T]
              simp only [ite_mul, zero_mul]
              rw [← sum_filter]
              rw [reindex_move m i j hij (fun x y => ρ y * φ i j * p y i j * v x)]
              rw [sum_filter]
              apply sum_congr rfl
              intro x hx
              by_cases hi : 1 ≤ x i
              · simp [hi]
              · have hx0 : x i = 0 := by omega
                simp [hi, (hp x hx i j).2.2 hx0]
          calc
            _ = ∑ x ∈ states n m, (ρ x * (∑ i, ∑ j, φ i j * p x i j)) * v x := by
              simp_rw [mul_sum, sum_mul]; simp [mul_assoc]
            _ = ∑ x ∈ states n m, (∑ i, ∑ j, inflowTerm φ p ρ x i j) * v x := by
              apply sum_congr rfl
              intro x hx
              rw [hρ.2.2.2 x hx]
            _ = ∑ i, ∑ j, ∑ x ∈ states n m, inflowTerm φ p ρ x i j * v x := by
              simp_rw [sum_mul]
              rw [sum_comm]
              apply sum_congr rfl
              intro i hi
              rw [sum_comm]
            _ = ∑ i, ∑ j, ∑ x ∈ states n m, ρ x * φ i j * p x i j * v (T x i j) := by
              simp_rw [hpair]
            _ = _ := by
              symm
              rw [sum_comm]
              apply sum_congr rfl
              intro x hx
              rw [sum_comm]
        have flow_balance : ∀ (p : (Fin n → ℕ) → Fin n → Fin n → ℝ)
            (ρ : (Fin n → ℕ) → ℝ), IsPolicy n m p → IsStationary n m φ p ρ →
            ∀ k, (∑ x ∈ states n m, ∑ i, ρ x * φ i k * p x i k) =
              ∑ x ∈ states n m, ∑ j, ρ x * φ k j * p x k j := by
          intro p ρ hp hρ k
          have he := test_eq p ρ hp hρ (fun x => (x k : ℝ))
          have hterm : ∀ x ∈ states n m, ∀ i j,
              ρ x * φ i j * p x i j * (T x i j k : ℝ) =
              ρ x * φ i j * p x i j * (x k : ℝ) +
                (if j = k then ρ x * φ i j * p x i j else 0) -
                (if i = k then ρ x * φ i j * p x i j else 0) := by
            intro x hx i j
            by_cases hi : 0 < x i
            · have hcast : (T x i j k : ℝ) = (x k : ℝ) +
                  (if j = k then 1 else 0) - (if i = k then 1 else 0) := by
                by_cases hij : i = j
                · subst j; simp [T]
                · by_cases hki : k = i
                  · subst k; simp [T, hij, moveState, Ne.symm hij, Nat.cast_sub hi]
                  · by_cases hkj : k = j
                    · subst k; simp [T, hij, moveState]
                    · simp [T, hij, moveState, hki, hkj, Ne.symm hki, Ne.symm hkj]
              rw [hcast]
              split_ifs <;> ring
            · have hz := (hp x hx i j).2.2 (by omega)
              simp [hz]
          have hsum : (∑ x ∈ states n m, ∑ i, ∑ j, ρ x * φ i j * p x i j * (T x i j k : ℝ)) =
              (∑ x ∈ states n m, ∑ i, ∑ j, ρ x * φ i j * p x i j * (x k : ℝ)) +
              (∑ x ∈ states n m, ∑ i, ρ x * φ i k * p x i k) -
              (∑ x ∈ states n m, ∑ j, ρ x * φ k j * p x k j) := by
            calc
              _ = ∑ x ∈ states n m, ∑ i, ∑ j,
                  (ρ x * φ i j * p x i j * (x k : ℝ) +
                    (if j = k then ρ x * φ i j * p x i j else 0) -
                    (if i = k then ρ x * φ i j * p x i j else 0)) := by
                apply sum_congr rfl
                intro x hx
                apply sum_congr rfl
                intro i _
                apply sum_congr rfl
                intro j _
                exact hterm x hx i j
              _ = _ := by
                simp [sum_sub_distrib, sum_add_distrib]
          linarith
        let qb : Fin n → ℝ := fun i => ∑ x ∈ states n m, π x * q x i
        have hqb : IsRelaxFeasible φ (pointQuantile qb) := by
          constructor
          · intro i j
            constructor
            · exact sum_nonneg fun x hx => mul_nonneg (hπ.1 x) (hq x hx i j).1
            · calc
                _ ≤ ∑ x ∈ states n m, π x * 1 := by
                  apply sum_le_sum
                  intro x hx
                  exact mul_le_mul_of_nonneg_left (hq x hx i j).2.1 (hπ.1 x)
                _ = 1 := by simpa using hπ.2.2.1
          · intro k
            have he := flow_balance (pointPolicy q) π hq hπ k
            simp only [pointPolicy] at he
            simp only [pointQuantile, qb]
            simp_rw [mul_sum]
            rw [sum_comm, sum_comm (s := univ) (t := states n m)]
            convert he using 1 <;> apply sum_congr rfl <;> intro x hx <;>
              apply sum_congr rfl <;> intro i hi <;> ring
        have hjensen : obj n m φ I (pointPolicy q) π ≤ elevObj φ I (pointQuantile qb) := by
          have hj : ∀ i j, (∑ x ∈ states n m, π x * rewardCurve I i j (q x i)) ≤
              rewardCurve I i j (qb i) := by
            intro i j
            simpa only [smul_eq_mul] using (hR i j).le_map_sum
              (fun x (_ : x ∈ states n m) => hπ.1 x) hπ.2.2.1
              (fun x hx => show q x i ∈ Set.Icc (0 : ℝ) 1 from
                ⟨(hq x hx i j).1, (hq x hx i j).2.1⟩)
          calc
            _ = ∑ i, ∑ j, φ i j * ∑ x ∈ states n m, π x * rewardCurve I i j (q x i) := by
              unfold obj pointPolicy
              simp_rw [mul_sum]
              rw [sum_comm]
              apply sum_congr rfl
              intro i hi
              rw [sum_comm]
              apply sum_congr rfl
              intro j hj
              apply sum_congr rfl
              intro x hx
              ring
            _ ≤ _ := sum_le_sum fun i _ => sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left (hj i j) (hφ i j)
        have hupper : obj n m φ I (pointPolicy q) π ≤ elevObj φ I (pointQuantile qt) :=
          hjensen.trans (hopt.2 qb hqb)
        by_cases hm : m = 0
        · subst m
          have hz : ∀ x ∈ states n 0, ∀ i, x i = 0 := by
            intro x hx i
            have hs := memS.mp hx
            have := single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin n))) => Nat.zero_le (x j)) (mem_univ i)
            omega
          have ho : obj n 0 φ I (toPolicy (pointQuantile qt)) πt = 0 := by
            apply sum_eq_zero
            intro x hx
            simp [toPolicy, hz x hx, rewardCurve]
          simp [ho]
        have hSne : (states n m).Nonempty := by
          by_contra h
          have hs := hπt.2.2.1
          rw [not_nonempty_iff_eq_empty.mp h, sum_empty] at hs
          norm_num at hs
        have hn : 0 < n := by
          obtain ⟨x, hx⟩ := hSne
          by_contra h
          have hn0 : n = 0 := by omega
          have hs := memS.mp hx
          subst n
          simp at hs
          exact hm hs.symm
        have hden : 0 < (m : ℝ) + n - 1 := by
          have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        have hfac : 0 ≤ (m : ℝ) / ((m : ℝ) + n - 1) := div_nonneg (Nat.cast_nonneg _) hden.le
        by_cases hqtzero : ∀ i, qt i = 0
        · have he : elevObj φ I (pointQuantile qt) = 0 := by
            simp [elevObj, pointQuantile, hqtzero, rewardCurve]
          have ho : obj n m φ I (toPolicy (pointQuantile qt)) πt = 0 := by
            simp [obj, toPolicy, pointQuantile, hqtzero, rewardCurve]
          rw [he] at hupper
          rw [ho]
          exact mul_nonpos_of_nonneg_of_nonpos hfac hupper
        have hqtpos : ∀ i, 0 < qt i := by
          have hback : ∀ i j, 0 < φ i j → qt j = 0 → qt i = 0 := by
            intro i j hij hj
            have hle := single_le_sum
              (fun k (_ : k ∈ (univ : Finset (Fin n))) => mul_nonneg (hφ k j) (hopt.1.1 k j).1)
              (mem_univ i)
            rw [hopt.1.2 j] at hle
            simp only [pointQuantile, hj, mul_zero, sum_const_zero] at hle
            have hi := (hopt.1.1 i j).1
            dsimp [pointQuantile] at hi
            nlinarith
          intro i
          have hi := (hopt.1.1 i i).1
          dsimp [pointQuantile] at hi
          by_contra h
          have hzi : qt i = 0 := le_antisymm (le_of_not_gt h) hi
          apply hqtzero
          intro j
          have path := hconn j i
          induction path using Relation.ReflTransGen.head_induction_on with
          | refl => exact hzi
          | @head a b hab path ih =>
            exact hback a b (by simpa using hab.2) ih
        let a : Fin n → Fin n → ℝ := fun i j => φ i j * qt i
        have ha : ∀ i j, 0 ≤ a i j := fun i j => mul_nonneg (hφ i j) (hqtpos i).le
        have habal : ∀ j, ∑ i, a i j = ∑ i, a j i := by
          intro j
          exact hopt.1.2 j
        obtain ⟨xm, hxm, hmax⟩ := exists_max_image (states n m) πt hSne
        let M : ℝ := πt xm
        have hmax' : ∀ x ∈ states n m, πt x ≤ M := hmax
        let U : (Fin n → ℕ) → Fin n → Fin n → (Fin n → ℕ) :=
          fun x i j => if i = j then x else moveState x i j
        let b : (Fin n → ℕ) → Fin n → Fin n → ℝ :=
          fun x i j => if 1 ≤ x j then a i j else 0
        have hcap : ∀ x, (∑ i, ∑ j, b x i j) =
            ∑ i, ∑ j, φ i j * toPolicy (pointQuantile qt) x i j := by
          intro x
          rw [sum_comm]
          apply sum_congr rfl
          intro j _
          calc
            (∑ i, b x i j) = if 1 ≤ x j then ∑ i, a i j else 0 := by
              by_cases hj : 1 ≤ x j <;> simp [b, hj]
            _ = if 1 ≤ x j then ∑ i, a j i else 0 := by rw [habal]
            _ = ∑ i, φ j i * toPolicy (pointQuantile qt) x j i := by
              by_cases hj : 1 ≤ x j
              · simp [toPolicy, pointQuantile, show 0 < x j from hj, a, hj]
              · simp [toPolicy, show ¬0 < x j from hj, hj]
        have hin : ∀ x i j, inflowTerm φ (toPolicy (pointQuantile qt)) πt x i j =
            b x i j * πt (U x i j) := by
          intro x i j
          by_cases hij : i = j
          · subst j
            by_cases hi : 1 ≤ x i
            · simp [inflowTerm, b, U, toPolicy, pointQuantile, hi, show 0 < x i from hi, a]
              ring
            · simp [inflowTerm, b, U, toPolicy, hi, show ¬0 < x i from hi]
          · by_cases hj : 1 ≤ x j
            · simp [inflowTerm, b, U, hij, hj, toPolicy, pointQuantile, move_pos, a]
              ring
            · simp [inflowTerm, b, U, hij, hj]
        have max_step : ∀ x ∈ states n m, πt x = M → ∀ i j, i ≠ j →
            0 < φ i j → 1 ≤ x j → πt (moveState x i j) = M := by
          intro x hx hxM i j hij hφij hj
          have hnonneg : ∀ k l, 0 ≤ b x k l * (M - πt (U x k l)) := by
            intro k l
            by_cases hl : 1 ≤ x l
            · apply mul_nonneg
              · simp [b, hl, ha]
              · apply sub_nonneg.mpr
                apply hmax'
                by_cases hkl : k = l
                · simpa [U, hkl] using hx
                · simpa [U, hkl] using move_mem k l hx hkl hl
            · simp [b, hl]
          have hs : (∑ k, ∑ l, b x k l * (M - πt (U x k l))) = 0 := by
            have he := hπt.2.2.2 x hx
            rw [hxM, ← hcap x] at he
            simp_rw [hin] at he
            simp_rw [mul_sub, sum_sub_distrib, ← sum_mul]
            nlinarith [he]
          have hs1 := (sum_eq_zero_iff_of_nonneg (fun k _ => sum_nonneg (fun l _ => hnonneg k l))).mp hs i (mem_univ i)
          have hs2 := (sum_eq_zero_iff_of_nonneg (fun l _ => hnonneg i l)).mp hs1 j (mem_univ j)
          simp only [b, hj, ↓reduceIte, U, hij, a] at hs2
          have hp : 0 < φ i j * qt i := mul_pos hφij (hqtpos i)
          nlinarith
        have inc_comm : ∀ x i j, inc (inc x i) j = inc (inc x j) i := by
          intro x i j
          ext k
          simp only [inc_apply]
          omega
        have some_pos : ∀ (k : ℕ) (x : Fin n → ℕ), (∑ i, x i) = k + 1 → ∃ i, 0 < x i := by
          intro k x hx
          by_contra h
          push Not at h
          have hz : (∑ i, x i) = 0 := sum_eq_zero (fun i _ => by have := h i; omega)
          omega
        have comp_prop : ∀ (k : ℕ) (P : (Fin n → ℕ) → Prop),
            (∃ x, (∑ i, x i) = k ∧ P x) →
            (∀ y, (∑ i, y i) + 1 = k → ∀ i j, P (inc y i) → P (inc y j)) →
            ∀ x, (∑ i, x i) = k → P x := by
          intro k
          induction k with
          | zero =>
            intro P hex hclosed x hx
            obtain ⟨y, hy, hPy⟩ := hex
            have hxy : x = y := by
              ext i
              have hxle := single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin n))) => Nat.zero_le (x j)) (mem_univ i)
              have hyle := single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin n))) => Nat.zero_le (y j)) (mem_univ i)
              omega
            simpa [hxy] using hPy
          | succ k ih =>
            intro P hex hclosed x hx
            obtain ⟨w, hw, hPw⟩ := hex
            obtain ⟨i, hi⟩ := some_pos k w hw
            have hwi : (∑ j, dec w i j) = k := by
              have := sum_dec w i hi
              omega
            have hsmall : ∀ z, (∑ j, z j) = k → P (inc z i) := by
              apply ih (fun z => P (inc z i))
              · exact ⟨dec w i, hwi, by simpa [inc_dec w i hi] using hPw⟩
              · intro y hy u v hPu
                rw [inc_comm y u i] at hPu
                rw [inc_comm y v i]
                apply hclosed (inc y i) (by rw [sum_inc]; omega) u v hPu
            obtain ⟨j, hj⟩ := some_pos k x hx
            have hxj : (∑ l, dec x j l) = k := by
              have := sum_dec x j hj
              omega
            have hp := hclosed (dec x j) (by omega) i j (hsmall _ hxj)
            simpa [inc_dec x j hj] using hp
        have max_transfer : ∀ y, (∑ i, y i) + 1 = m → ∀ i j,
            πt (inc y j) = M → πt (inc y i) = M := by
          intro y hy i j hj
          have path := hconn i j
          induction path using Relation.ReflTransGen.head_induction_on with
          | refl => exact hj
          | @head u v huv path ih =>
            have hxv : inc y v ∈ states n m := memS.mpr (by rw [sum_inc]; exact hy)
            have hv : 1 ≤ inc y v v := by simp [inc]
            have he := max_step (inc y v) hxv ih u v huv.1 (by simpa using huv.2) hv
            simpa [move_inc y u v huv.1] using he
        have huniform : ∀ x ∈ states n m, πt x = M := by
          apply fun x hx => comp_prop m (fun x => πt x = M) ⟨xm, memS.mp hxm, rfl⟩
            (fun y hy i j hi => max_transfer y hy j i hi) x (memS.mp hx)
        have sum_inc_reindex : ∀ (k : ℕ) (i : Fin n) (F : (Fin n → ℕ) → ℝ),
            (∑ x ∈ (states n (k + 1)).filter (fun x => 1 ≤ x i), F x) =
            ∑ y ∈ states n k, F (inc y i) := by
          intro k i F
          symm
          apply sum_bij (fun y _ => inc y i)
          · intro y hy
            refine mem_filter.mpr ⟨memS.mpr ?_, ?_⟩
            · rw [sum_inc, memS.mp hy]
            · simp [inc]
          · intro y hy z hz he
            have := congrArg (fun x => dec x i) he
            simpa only [dec_inc] using this
          · intro x hx
            have hi := (mem_filter.mp hx).2
            refine ⟨dec x i, memS.mpr ?_, inc_dec x i hi⟩
            have hs := sum_dec x i hi
            have ht := memS.mp (mem_filter.mp hx).1
            omega
          · intro y hy
            rfl
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        let B : ℝ := ∑ y ∈ states n k, M
        have hbusy : ∀ i, (∑ x ∈ (states n (k + 1)).filter (fun x => 1 ≤ x i), πt x) = B := by
          intro i
          rw [sum_inc_reindex k i]
          apply sum_congr rfl
          intro y hy
          apply huniform
          apply memS.mpr
          rw [sum_inc, memS.mp hy]
        have hmass : ((k + 1 : ℕ) : ℝ) = ((k : ℝ) + n) * B := by
          calc
            _ = (∑ x ∈ states n (k + 1), πt x) * ((k + 1 : ℕ) : ℝ) := by rw [hπt.2.2.1, one_mul]
            _ = ∑ x ∈ states n (k + 1), πt x * ∑ i, (x i : ℝ) := by
              rw [sum_mul]
              apply sum_congr rfl
              intro x hx
              have hs : (∑ i, (x i : ℝ)) = ((k + 1 : ℕ) : ℝ) := by exact_mod_cast memS.mp hx
              rw [hs]
            _ = ∑ i, ∑ x ∈ (states n (k + 1)).filter (fun x => 1 ≤ x i), M * (x i : ℝ) := by
              simp_rw [mul_sum]
              rw [sum_comm]
              apply sum_congr rfl
              intro i hi
              rw [sum_filter]
              apply sum_congr rfl
              intro x hx
              rw [huniform x hx]
              by_cases hi : 1 ≤ x i
              · simp [hi]
              · have hz : x i = 0 := by omega
                simp [hz]
            _ = ∑ i, ∑ y ∈ states n k, M * ((y i : ℝ) + 1) := by
              apply sum_congr rfl
              intro i hi
              rw [sum_inc_reindex k i]
              apply sum_congr rfl
              intro y hy
              simp [inc]
            _ = ∑ y ∈ states n k, M * ((k : ℝ) + n) := by
              rw [sum_comm]
              apply sum_congr rfl
              intro y hy
              rw [← mul_sum]
              have hs : (∑ i, (y i : ℝ)) = (k : ℝ) := by exact_mod_cast memS.mp hy
              simp [sum_add_distrib, hs]
            _ = ((k : ℝ) + n) * B := by
              simp [B, mul_comm]
              ring
        have hB : B = ((k + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) + n - 1) := by
          apply (eq_div_iff (ne_of_gt hden)).mpr
          have hd : (((k + 1 : ℕ) : ℝ) + n - 1) = (k : ℝ) + n := by push_cast; ring
          rw [hd]
          nlinarith [hmass]
        have ho : obj n (k + 1) φ I (toPolicy (pointQuantile qt)) πt =
            B * elevObj φ I (pointQuantile qt) := by
          simp only [obj, elevObj]
          simp_rw [mul_sum]
          rw [sum_comm]
          apply sum_congr rfl
          intro i hi
          rw [sum_comm]
          apply sum_congr rfl
          intro j hj
          calc
            _ = (∑ x ∈ (states n (k + 1)).filter (fun x => 1 ≤ x i), πt x) *
                (φ i j * rewardCurve I i j (qt i)) := by
              rw [sum_mul, sum_filter]
              apply sum_congr rfl
              intro x hx
              by_cases hi : 1 ≤ x i
              · simp [toPolicy, pointQuantile, hi, show 0 < x i from hi]
              · simp [toPolicy, hi, show ¬0 < x i from hi, rewardCurve]
            _ = _ := by rw [hbusy]; rfl
        rw [ho, hB]
        exact mul_le_mul_of_nonneg_left hupper hfac
