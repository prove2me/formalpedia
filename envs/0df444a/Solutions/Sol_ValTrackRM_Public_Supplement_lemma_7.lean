-- Prove2me | solution 1 for ValTrackRM.Public.Supplement.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:32:47.783101+00:00
-- url     : https://prove2.me/submissions/23bf3ed6-c3cc-447f-95d7-eb2e710cd501

import Mathlib
import Definitions.Def_ValTrackRM_Public_Supplement_Sampling

open ValTrackRM
open ValTrackRM.Public
open ValTrackRM.Public.Supplement

theorem solution
    (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ)
    (hr0 : r 0 = 0) (hr : ∀ j < m, r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : isMin sel)
    (ν : ℕ → PMF (Fin (m + 1))) (C : ℕ) (hC : 1 ≤ C) (T t : ℕ)
    (ht : 1 ≤ t) (htT : t ≤ T) :
    firstFailureMass r sel ν C T t ≤ 1 / (Real.exp 1 * (C : ℝ) * (t : ℝ) ^ 2) := by
      classical
      have av_branch {α β : Type} (xs : List (α × ℝ)) (f : α → List (β × ℝ))
          (g : β → ℝ) : average (branch xs f) g = average xs (fun x => average (f x) g) := by
        induction xs with
        | nil => simp [branch, average]
        | cons x xs ih =>
          simp only [branch, List.flatMap_cons, List.map_append, List.sum_append,
            average, List.map_cons, List.sum_cons] at *
          rw [ih]
          congr 1
          simp only [List.map_map, Function.comp_def, mul_assoc, List.sum_map_mul_left]
      have av_nonneg {α : Type} (xs : List (α × ℝ))
          (hx : ∀ x ∈ xs, 0 ≤ x.2) (f : α → ℝ) (hf : ∀ x ∈ xs, 0 ≤ f x.1) :
          0 ≤ average xs f := by
        apply List.sum_nonneg
        intro y hy
        obtain ⟨x, hx', rfl⟩ := List.mem_map.mp hy
        exact mul_nonneg (hx x hx') (hf x hx')
      have av_mono {α : Type} (xs : List (α × ℝ))
          (hx : ∀ x ∈ xs, 0 ≤ x.2) (f g : α → ℝ) (hfg : ∀ x ∈ xs, f x.1 ≤ g x.1) :
          average xs f ≤ average xs g := by
        apply List.sum_le_sum
        intro x hx'
        exact mul_le_mul_of_nonneg_left (hfg x hx') (hx x hx')
      have av_congr {α : Type} (xs : List (α × ℝ)) (f g : α → ℝ)
          (hfg : ∀ x ∈ xs, f x.1 = g x.1) : average xs f = average xs g := by
        unfold average
        congr 1
        exact List.map_congr_left (fun x hx => congrArg (x.2 * ·) (hfg x hx))
      have av_const {α : Type} (xs : List (α × ℝ)) (c : ℝ) :
          average xs (fun _ => c) = average xs (fun _ => 1) * c := by
        simp [average, List.sum_map_mul_right]
      have av_zero {α : Type} (xs : List (α × ℝ)) : average xs (fun _ => 0) = 0 := by
        simp [average]
      have av_constant {α : Type} (xs : List (α × ℝ)) (hx : average xs (fun _ => 1) = 1)
          (c : ℝ) : average xs (fun _ => c) = c := by
        rw [av_const, hx, one_mul]
      have av_sum {α ι : Type} [Fintype ι] (xs : List (α × ℝ)) (f : ι → α → ℝ) :
          average xs (fun x => ∑ i, f i x) = ∑ i, average xs (f i) := by
        induction xs with
        | nil => simp [average]
        | cons x xs ih => simpa [average, mul_add, Finset.mul_sum,
            Finset.sum_add_distrib] using congrArg (fun z => (∑ i, x.2 * f i x.1) + z) ih
      have draw_av (w : Price m → ℝ) (f : Price m → ℝ) :
          average (priceDraw w) f = ∑ p, w p * f p := by
        simp [average, priceDraw, List.map_map, ← List.ofFn_id, List.map_ofFn,
          List.sum_ofFn, Fin.sum_univ_succ]
      have value_av (n : ℕ) (f : Fin (m+1) → ℝ) :
          average (valueDraw (ν n)) f = ∑ v, (ν n v).toReal * f v := by
        exact draw_av (fun v => (ν n v).toReal) f
      have val_norm (n : ℕ) : ∑ v : Fin (m+1), (ν n v).toReal = 1 := by
        rw [← ENNReal.toReal_sum (fun v _ => PMF.apply_ne_top (ν n) v)]
        have hh := (ν n).tsum_coe
        rw [tsum_fintype] at hh
        rw [hh, ENNReal.toReal_one]
      have rpos : ∀ j, 1 ≤ j → j ≤ m → 0 < r j := by
        intro j hj hjm
        have mono : StrictMonoOn r (Set.Iic m) := by
          intro a ha b hb hab
          exact (strictMonoOn_Iic_of_lt_succ (fun i hi => hr i hi)) ha hb hab
        rw [← hr0]
        exact mono (by simp) hjm (by omega)
      have qpos : ∀ j, 1 ≤ j → j ≤ m → 0 < qj r j := by
        intro j hj hjm
        unfold qj
        apply sub_pos.mpr
        apply (div_lt_one (rpos j hj hjm)).mpr
        have := hr (j-1) (by omega)
        simpa [Nat.sub_add_cancel hj] using this
      have qtpos : ∀ l, l < m → 0 < qTot r m l := by
        intro l hl
        apply Finset.sum_pos
        · intro j hj
          exact qpos j (by have := (Finset.mem_Ioc.mp hj).1; omega)
            (Finset.mem_Ioc.mp hj).2
        · exact ⟨l+1, by simp; omega⟩
      have price_norm (L : Fin k → Fin (m+1)) (s : Fin k → Bool) :
          (∀ p, 0 ≤ unitPrice r sel L s p) ∧ ∑ p, unitPrice r sel L s p = 1 := by
        unfold unitPrice
        split_ifs with h
        · have hq := qtpos (L (sel L)).val h.2
          constructor
          · intro p
            split_ifs with hp
            · exact le_of_lt (div_pos (qpos _ (by omega) (by omega)) hq)
            · rfl
          · have heq : (∑ p : Fin (m+1), if (L (sel L)).val < p.val+1 ∧ p.val < m
                  then offerProb r m (L (sel L)).val (p.val+1) else 0) =
                ∑ j ∈ Finset.Ioc (L (sel L)).val m, offerProb r m (L (sel L)).val j := by
              rw [← Finset.sum_filter]
              apply Finset.sum_bij (fun p hp => p.val+1)
              · intro p hp
                simp only [Finset.mem_univ, true_and, Finset.mem_filter] at hp
                exact Finset.mem_Ioc.mpr ⟨hp.1, by omega⟩
              · intro p hp q hq hpq
                exact Fin.ext (by omega)
              · intro j hj
                have hj' := Finset.mem_Ioc.mp hj
                refine ⟨⟨j-1, by omega⟩, ?_, ?_⟩
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                · omega
                · dsimp; omega
              · intro p hp
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
                simp [hp]
            rw [heq]
            simp only [offerProb, ← Finset.sum_div]
            change qTot r m (L (sel L)).val / qTot r m (L (sel L)).val = 1
            exact div_self (ne_of_gt hq)
        · constructor
          · intro p
            unfold reject
            positivity
          · have he (p : Price m) : p.val = m ↔ p = ⟨m, by omega⟩ := by
              simp only [Fin.ext_iff]
            simp [reject, he]
      have av_add {α : Type} (xs : List (α × ℝ)) (f g : α → ℝ) :
          average xs (fun x => f x + g x) = average xs f + average xs g := by
        simp [average, mul_add, List.sum_map_add]
      have av_mul {α : Type} (xs : List (α × ℝ)) (c : ℝ) (f : α → ℝ) :
          average xs (fun x => c * f x) = c * average xs f := by
        simp [average, ← List.sum_map_mul_left, mul_left_comm, mul_assoc]
      have av_mul_right {α : Type} (xs : List (α × ℝ)) (c : ℝ) (f : α → ℝ) :
          average xs (fun x => f x * c) = average xs f * c := by
        simpa only [mul_comm] using av_mul xs c f
      have branch_nonneg {α β : Type} (xs : List (α × ℝ)) (f : α → List (β × ℝ))
          (hx : ∀ x ∈ xs, 0 ≤ x.2) (hf : ∀ x ∈ xs, ∀ y ∈ f x.1, 0 ≤ y.2) :
          ∀ y ∈ branch xs f, 0 ≤ y.2 := by
        intro y hy
        obtain ⟨x, hx', hy'⟩ := List.mem_flatMap.mp hy
        obtain ⟨z, hz, heq⟩ := List.mem_map.mp hy'
        cases heq
        exact mul_nonneg (hx x hx') (hf x hx' z hz)
      have branch_norm {α β : Type} (xs : List (α × ℝ)) (f : α → List (β × ℝ))
          (hx : average xs (fun _ => 1) = 1)
          (hf : ∀ x ∈ xs, average (f x.1) (fun _ => 1) = 1) :
          average (branch xs f) (fun _ => 1) = 1 := by
        rw [av_branch]
        exact (av_congr _ _ _ hf).trans hx
      have singleton_av {α : Type} (x : α) (f : α → ℝ) : average [(x,1)] f = f x := by
        simp [average]
      have av_map {α β : Type} (xs : List (α × ℝ)) (f : α → β) (g : β → ℝ) :
          average (xs.map (fun x => (f x.1, x.2))) g = average xs (fun x => g (f x)) := by
        simp [average, List.map_map, Function.comp_def]
      have draw_nonneg (w : Price m → ℝ) (hw : ∀ p, 0 ≤ w p) :
          ∀ x ∈ priceDraw w, 0 ≤ x.2 := by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        exact hw p
      have value_nonneg (n : ℕ) : ∀ x ∈ valueDraw (ν n), 0 ≤ x.2 :=
        draw_nonneg _ (fun _ => ENNReal.toReal_nonneg)
      have value_norm (n : ℕ) : average (valueDraw (ν n)) (fun _ => 1) = 1 := by
        simpa only [value_av, mul_one] using val_norm n
      have unit_norm (L : Fin k → Fin (m+1)) (s : Fin k → Bool) :
          average (priceDraw (unitPrice r sel L s)) (fun _ => 1) = 1 := by
        simpa only [draw_av, mul_one] using (price_norm L s).2
      have sim_valid (n : ℕ) : (∀ x ∈ simulate r sel ν n, 0 ≤ x.2) ∧
          average (simulate r sel ν n) (fun _ => 1) = 1 := by
        induction n with
        | zero => simp [simulate, average]
        | succ n ih =>
          constructor
          · apply branch_nonneg _ _ ih.1
            intro x hx
            apply branch_nonneg _ _ (draw_nonneg _ (price_norm _ _).1)
            intro p hp
            apply branch_nonneg _ _ (value_nonneg _)
            intro v hv y hy
            simp only [List.mem_singleton] at hy
            rw [hy]
            norm_num
          · apply branch_norm _ _ ih.2
            intro x hx
            apply branch_norm _ _ (unit_norm _ _)
            intro p hp
            apply branch_norm _ _ (value_norm _)
            intro v hv
            simp [average]
      let P (n a : ℕ) : ℝ := average (simulate r sel ν n)
        (fun st => if inventory st.sold = a then 1 else 0)
      have p_bounds (n a : ℕ) : 0 ≤ P n a ∧ P n a ≤ 1 := by
        constructor
        · apply av_nonneg _ (sim_valid n).1
          intro x hx
          split_ifs <;> norm_num
        · change average _ _ ≤ 1
          calc
            _ ≤ average (simulate r sel ν n) (fun _ => 1) := by
              apply av_mono _ (sim_valid n).1
              intro x hx
              split_ifs <;> norm_num
            _ = 1 := (sim_valid n).2
      have inv_bound (s : Fin k → Bool) : inventory s ≤ k := by
        exact (Finset.card_filter_le _ _).trans (by simp)
      let I (st : SimFrame m k) : Fin (k+1) := ⟨inventory st.sold, by have := inv_bound st.sold; omega⟩
      have av_group {α : Type} (xs : List (α × ℝ)) (i : α → Fin (k+1))
          (f : Fin (k+1) → ℝ) :
          average xs (fun x => f (i x)) =
            ∑ a : Fin (k+1), average xs (fun x => if i x = a then 1 else 0) * f a := by
        simp only [← av_mul_right]
        rw [← av_sum]
        apply av_congr
        intro x hx
        simp
      have av_sub {α : Type} (xs : List (α × ℝ)) (f g : α → ℝ) :
          average xs (fun x => f x - g x) = average xs f - average xs g := by
        have he : (fun x => f x - g x) = (fun x => f x + (-1) * g x) := by
          funext x; ring
        rw [he, av_add, av_mul]
        ring
      have av_ite {α : Type} (xs : List (α × ℝ)) (b : α → Prop) [DecidablePred b] (f : α → ℝ) (c : ℝ) :
          average xs (fun x => if b x then f x else c) =
            average xs (fun x => if b x then f x else 0) +
              (average xs (fun _ => 1) - average xs (fun x => if b x then 1 else 0)) * c := by
        rw [← av_sub, ← av_mul_right, ← av_add]
        apply av_congr
        intro x hx
        split_ifs <;> ring
      let H (p : ℝ) : ℕ → ℝ := Nat.rec 0 (fun _ z => 1 + (1-p)*z)
      have h_nonneg (p : ℝ) (hp : p ≤ 1) (n : ℕ) : 0 ≤ H p n := by
        induction n with
        | zero => exact le_refl 0
        | succ n ih => change 0 ≤ 1 + (1-p)*H p n; positivity
      have h_identity (p : ℝ) (n : ℕ) : (1-p)^n + H p n * p = 1 := by
        induction n with
        | zero => simp [H]
        | succ n ih =>
          change (1-p)^(n+1) + (1+(1-p)*H p n)*p = 1
          rw [pow_succ]
          calc
            _ = (1-p)*((1-p)^n + H p n*p) + p := by ring
            _ = 1 := by rw [ih]; ring
      have trial_av (n a fuel : ℕ) (g : Option (SimFrame m k) → ℝ) :
          average (trials r sel ν n a fuel) (fun result => g result.matched) =
            (1-P n a)^fuel * g none + H (P n a) fuel *
              average (simulate r sel ν n) (fun st => if inventory st.sold = a then g (some st) else 0) := by
        induction fuel with
        | zero => simp [trials, average, H]
        | succ fuel ih =>
          rw [trials, av_branch]
          calc
            _ = average (simulate r sel ν n) (fun st => if inventory st.sold = a
                  then g (some st) else average (trials r sel ν n a fuel) (fun result => g result.matched)) := by
              apply av_congr
              intro x hx
              split_ifs <;> simp only [av_branch, singleton_av]
            _ = average (simulate r sel ν n) (fun st => if inventory st.sold = a then g (some st) else 0) +
                (1-P n a) * average (trials r sel ν n a fuel) (fun result => g result.matched) := by
              have hh := av_ite (simulate r sel ν n) (fun st => inventory st.sold = a)
                (fun st => g (some st)) (average (trials r sel ν n a fuel)
                  (fun result => g result.matched))
              rw [(sim_valid n).2] at hh
              exact hh
            _ = _ := by
              rw [ih]
              change _ = (1-P n a)^(fuel+1)*g none +
                (1+(1-P n a)*H (P n a) fuel) * _
              rw [pow_succ]
              ring
      have trial_valid (n a fuel : ℕ) :
          (∀ x ∈ trials r sel ν n a fuel, 0 ≤ x.2) ∧
          average (trials r sel ν n a fuel) (fun _ => 1) = 1 := by
        constructor
        · induction fuel with
          | zero => simp [trials]
          | succ fuel ih =>
            apply branch_nonneg _ _ (sim_valid n).1
            intro x hx
            split_ifs
            · simp
            · apply branch_nonneg _ _ ih
              intro y hy z hz
              simp only [List.mem_singleton] at hz
              rw [hz]
              norm_num
        · have hh := trial_av n a fuel (fun _ => 1)
          simp only [mul_one] at hh
          exact hh.trans (h_identity (P n a) fuel)
      let rejectCode : Price m := ⟨m, by omega⟩
      have reject_av (f : Price m → ℝ) : average (priceDraw reject) f = f rejectCode := by
        rw [draw_av]
        have he (p : Price m) : p.val = m ↔ p = rejectCode := by
          simp only [Fin.ext_iff, rejectCode]
        simp [reject, he]
      have sample_av (u a : ℕ) (f : Bool → Price m → ℝ) :
          average (samplePrice r sel ν C u a false) (fun ch => f ch.failed ch.price) =
          (1-P (u-1) a)^(C*(k+1)*u^2) * f true rejectCode +
          H (P (u-1) a) (C*(k+1)*u^2) * average (simulate r sel ν (u-1))
            (fun st => if inventory st.sold = a then
              average (priceDraw (unitPrice r sel st.level st.sold)) (f false) else 0) := by
        unfold samplePrice
        rw [av_branch]
        have he : average (trials r sel ν (u-1) a (C*(k+1)*u^2))
          (fun result => average
            (match result.matched with
             | some st => (priceDraw (unitPrice r sel st.level st.sold)).map (fun pw =>
                (RoundChoice.mk false pw.1 (result.operations + selectorWork k +
                  offerWork m (st.level (sel st.level)).val + 10) result.transitions, pw.2))
             | none => (priceDraw reject).map (fun pw =>
                (RoundChoice.mk true pw.1 (result.operations+10) result.transitions, pw.2)))
            (fun ch => f ch.failed ch.price)) =
            average (trials r sel ν (u-1) a (C*(k+1)*u^2))
              (fun result => match result.matched with
              | some st => average (priceDraw (unitPrice r sel st.level st.sold)) (f false)
              | none => f true rejectCode) := by
          apply av_congr
          intro x hx
          cases x.1.matched with
          | none =>
            simp only
            convert reject_av (f true) using 1 <;> simp [average, List.map_map, Function.comp_def]
          | some st => simp [average, List.map_map, Function.comp_def]
        convert he.trans
          (trial_av (u-1) a (C*(k+1)*u^2) (fun res => match res with
            | some st => average (priceDraw (unitPrice r sel st.level st.sold)) (f false)
            | none => f true rejectCode)) using 1 <;>
          simp [average, List.map_map, Function.comp_def]
        all_goals rfl
      have sample_valid (u a : ℕ) :
          (∀ x ∈ samplePrice r sel ν C u a false, 0 ≤ x.2) ∧
          average (samplePrice r sel ν C u a false) (fun _ => 1) = 1 := by
        constructor
        · apply branch_nonneg _ _ (trial_valid _ _ _).1
          intro x hx
          cases hmch : x.1.matched with
          | none =>
            simp only [hmch, Bool.false_eq_true, ↓reduceIte]
            intro y hy
            obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
            exact draw_nonneg _ (fun p => by unfold reject; positivity) z hz
          | some st =>
            simp only [hmch]
            intro y hy
            obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
            exact draw_nonneg _ (price_norm _ _).1 z hz
        · have hh := sample_av u a (fun _ _ => 1)
          simp only [unit_norm, mul_one] at hh
          exact hh.trans (h_identity _ _)
      have inv_update (s : Fin k → Bool) (i : Fin k) (hs : s i = false) :
          inventory (Function.update s i true) = inventory s - 1 := by
        have he : (Finset.univ.filter (fun j => Function.update s i true j = false)) =
            (Finset.univ.filter (fun j => s j = false)).erase i := by
          ext j
          by_cases hj : j = i
          · subst j; simp
          · simp [Function.update_of_ne hj, hj]
        unfold inventory
        rw [he, Finset.card_erase_of_mem (by simp [hs])]
      have stock_step (st : SimFrame m k) (p : Price m) (v : Fin (m+1))
          (f : ℕ → ℝ) :
          unitPrice r sel st.level st.sold p *
            f (inventory (if buys r (inventory st.sold) p v then
              Function.update st.sold (sel st.level) true else st.sold)) =
          unitPrice r sel st.level st.sold p * f (nextStock r (inventory st.sold) p v) := by
        by_cases hb : buys r (inventory st.sold) p v = true
        · by_cases hs : st.sold (sel st.level) = false
          · simp only [hb, ↓reduceIte, nextStock, inv_update _ _ hs]
          · have hp : p.val < m := (of_decide_eq_true hb).2.1
            have hz : unitPrice r sel st.level st.sold p = 0 := by
              simp [unitPrice, hs, reject, show p.val ≠ m by omega]
            simp [hz]
        · have hb' : buys r (inventory st.sold) p v = false := Bool.eq_false_iff.mpr hb
          simp [hb', nextStock]
      have sim_step (n : ℕ) (f : ℕ → ℝ) :
          average (simulate r sel ν (n+1)) (fun st => f (inventory st.sold)) =
          average (simulate r sel ν n) (fun st =>
            average (priceDraw (unitPrice r sel st.level st.sold)) (fun p =>
              average (valueDraw (ν (n+1))) (fun v => f (nextStock r (inventory st.sold) p v)))) := by
        rw [simulate, av_branch]
        apply av_congr
        intro x hx
        rw [av_branch, draw_av, draw_av]
        apply Finset.sum_congr rfl
        intro p hp
        rw [av_branch]
        simp only [singleton_av, value_av, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        simpa only [mul_left_comm] using congrArg ((ν (n+1) v).toReal * ·)
          (stock_step x.1 p v f)
      let U (n : ℕ) (ex : Execution m) (ch : RoundChoice m) (v : Fin (m+1)) : Execution m :=
        ⟨ex.observations ++ [⟨ch.failed, ch.price, v⟩], nextStock r ex.stock ch.price v,
          ex.revenue + payment r ex.stock ch.price v,
          ex.operations + ch.operations + 10*(n+k+m+1),
          ex.simulatedTransitions + ch.transitions⟩
      have run_step (n : ℕ) (f : Execution m → ℝ) :
          average (publicRun r sel ν C false (n+1)) f =
          average (publicRun r sel ν C false n) (fun ex =>
            average (samplePrice r sel ν C (n+1) ex.stock false) (fun ch =>
              average (valueDraw (ν (n+1))) (fun v => f (U n ex ch v)))) := by
        rw [publicRun, av_branch]
        apply av_congr
        intro x hx
        rw [av_branch]
        apply av_congr
        intro ch hch
        rw [av_branch]
        apply av_congr
        intro v hv
        exact singleton_av _ _
      have branch_support {α β : Type} (xs : List (α × ℝ)) (f : α → List (β × ℝ))
          (Q : β → Prop) (hf : ∀ x ∈ xs, ∀ y ∈ f x.1, Q y.1) :
          ∀ y ∈ branch xs f, Q y.1 := by
        intro y hy
        obtain ⟨x, hx, hy⟩ := List.mem_flatMap.mp hy
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
        exact hf x hx z hz
      have run_support (n : ℕ) : ∀ x ∈ publicRun r sel ν C false n,
          x.1.observations.length = n ∧ x.1.stock ≤ k := by
        induction n with
        | zero => simp [publicRun]
        | succ n ih =>
          rw [publicRun]
          apply branch_support _ _ (fun ex : Execution m => ex.observations.length = n+1 ∧ ex.stock ≤ k)
          intro x hx
          apply branch_support _ _ (fun ex : Execution m => ex.observations.length = n+1 ∧ ex.stock ≤ k)
          intro ch hch
          apply branch_support _ _ (fun ex : Execution m => ex.observations.length = n+1 ∧ ex.stock ≤ k)
          intro v hv y hy
          simp only [List.mem_singleton] at hy
          rw [hy]
          have hh := ih x hx
          constructor
          · simpa only [List.length_append, List.length_singleton] using congrArg (· + 1) hh.1
          · exact (Nat.sub_le _ _).trans hh.2
      have run_valid (n : ℕ) :
          (∀ x ∈ publicRun r sel ν C false n, 0 ≤ x.2) ∧
          average (publicRun r sel ν C false n) (fun _ => 1) = 1 := by
        induction n with
        | zero => simp [publicRun, average]
        | succ n ih =>
          constructor
          · apply branch_nonneg _ _ ih.1
            intro x hx
            apply branch_nonneg _ _ (sample_valid _ _).1
            intro ch hch
            apply branch_nonneg _ _ (value_nonneg _)
            intro v hv y hy
            simp only [List.mem_singleton] at hy
            rw [hy]
            norm_num
          · rw [run_step]
            calc
              _ = average (publicRun r sel ν C false n) (fun _ => 1) := by
                apply av_congr
                intro x hx
                rw [av_constant _ (value_norm _), (sample_valid _ _).2]
              _ = 1 := ih.2
      let Good (ex : Execution m) : Prop := ∀ o ∈ ex.observations, o.failed = false
      have good_u (n : ℕ) (ex : Execution m) (ch : RoundChoice m) (v : Fin (m+1)) :
          Good (U n ex ch v) ↔ Good ex ∧ ch.failed = false := by
        simp [Good, U, List.mem_append, or_imp, forall_and]
      let A (n a : ℕ) (f : ℕ → ℝ) : ℝ := average (simulate r sel ν n)
        (fun st => if inventory st.sold = a then
          average (priceDraw (unitPrice r sel st.level st.sold)) (fun p =>
            average (valueDraw (ν (n+1))) (fun v => f (nextStock r a p v))) else 0)
      have a_nonneg (n a : ℕ) (f : ℕ → ℝ) (hf : ∀ a, 0 ≤ f a) : 0 ≤ A n a f := by
        apply av_nonneg _ (sim_valid n).1
        intro x hx
        split_ifs
        · apply av_nonneg _ (draw_nonneg _ (price_norm _ _).1)
          intro p hp
          apply av_nonneg _ (value_nonneg _)
          intro v hv
          exact hf _
        · rfl
      have good_step (n : ℕ) (f : ℕ → ℝ) :
          average (publicRun r sel ν C false (n+1)) (fun ex => if Good ex then f ex.stock else 0) =
          average (publicRun r sel ν C false n) (fun ex => if Good ex then
            H (P n ex.stock) (C*(k+1)*(n+1)^2) * A n ex.stock f else 0) := by
        rw [run_step]
        apply av_congr
        intro x hx
        by_cases hg : Good x.1
        · simp only [hg, ↓reduceIte]
          calc
            _ = average (samplePrice r sel ν C (n+1) x.1.stock false)
                (fun ch => if ch.failed = false then average (valueDraw (ν (n+1)))
                  (fun v => f (nextStock r x.1.stock ch.price v)) else 0) := by
              apply av_congr
              intro ch hch
              by_cases hc : ch.1.failed = false
              · simp only [good_u, hg, hc, and_self, ↓reduceIte]
                rfl
              · simp [good_u, hg, hc, av_zero]
            _ = _ := by
              have hh := sample_av (n+1) x.1.stock (fun b p => if b = false then
                average (valueDraw (ν (n+1))) (fun v => f (nextStock r x.1.stock p v)) else 0)
              simpa only [Nat.add_sub_cancel, Bool.true_eq_false, ↓reduceIte, mul_zero,
                zero_add, Bool.false_eq_true, A] using hh
        · simp only [hg, ↓reduceIte]
          calc
            _ = average (samplePrice r sel ν C (n+1) x.1.stock false) (fun _ => 0) := by
              apply av_congr
              intro ch hch
              simp only [good_u, hg, false_and, ↓reduceIte, av_zero]
            _ = 0 := by simp [average]
      have group_sim (n : ℕ) (f : ℕ → ℝ) :
          average (simulate r sel ν n) (fun st => f (inventory st.sold)) =
            ∑ a : Fin (k+1), P n a.val * f a.val := by
        have hh := av_group (simulate r sel ν n) I (fun a => f a.val)
        simpa only [I, Fin.ext_iff, P] using hh
      have a_partition (n : ℕ) (f : ℕ → ℝ) :
          (∑ a : Fin (k+1), A n a.val f) =
            average (simulate r sel ν (n+1)) (fun st => f (inventory st.sold)) := by
        unfold A
        rw [← av_sum, sim_step]
        apply av_congr
        intro x hx
        rw [Finset.sum_eq_single (I x.1)]
        · simp only [I, ↓reduceIte]
        · intro a ha hne
          have hh : inventory x.1.sold ≠ a.val := by
            intro he
            apply hne
            exact Fin.ext he.symm
          simp [hh]
        · simp
      have domination (n : ℕ) (f : ℕ → ℝ) (hf : ∀ a, 0 ≤ f a) :
          average (publicRun r sel ν C false n) (fun ex => if Good ex then f ex.stock else 0) ≤
          average (simulate r sel ν n) (fun st => f (inventory st.sold)) := by
        induction n generalizing f with
        | zero => simp [publicRun, simulate, average, Good, inventory]
        | succ n ih =>
          rw [good_step]
          let g (a : ℕ) := H (P n a) (C*(k+1)*(n+1)^2) * A n a f
          have hg : ∀ a, 0 ≤ g a := by
            intro a
            exact mul_nonneg (h_nonneg _ (p_bounds n a).2 _) (a_nonneg n a f hf)
          calc
            _ ≤ average (simulate r sel ν n) (fun st => g (inventory st.sold)) := ih g hg
            _ = ∑ a : Fin (k+1), P n a.val * g a.val := group_sim n g
            _ ≤ ∑ a : Fin (k+1), A n a.val f := by
              apply Finset.sum_le_sum
              intro a ha
              have hp := p_bounds n a.val
              have hh := h_identity (P n a.val) (C*(k+1)*(n+1)^2)
              have hh' : H (P n a.val) (C*(k+1)*(n+1)^2) * P n a.val ≤ 1 := by
                have := pow_nonneg (sub_nonneg.mpr hp.2) (C*(k+1)*(n+1)^2)
                linarith
              dsimp [g]
              calc
                _ = (H (P n a.val) (C*(k+1)*(n+1)^2) * P n a.val) * A n a.val f := by ring
                _ ≤ 1 * A n a.val f := mul_le_mul_of_nonneg_right hh' (a_nonneg _ _ f hf)
                _ = _ := one_mul _
            _ = _ := a_partition n f
      have hist_inj : Function.Injective (fun h : FirstHistory m t =>
          List.ofFn (fun i => (⟨false, (h i).1, (h i).2⟩ : Observation m))) := by
        intro h₁ h₂ he
        have he' := List.ofFn_injective he
        funext i
        have hi := congrFun he' i
        exact Prod.ext (congrArg Observation.price hi) (congrArg Observation.value hi)
      have matches_unique (ex : Execution m) (h₁ h₂ : FirstHistory m t)
          (h₁m : matchesFirst ex t h₁) (h₂m : matchesFirst ex t h₂) : h₁ = h₂ :=
        hist_inj (h₁m.2.2.1.symm.trans h₂m.2.2.1)
      let F (ex : Execution m) : ℝ := ∑ h : FirstHistory m t, if matchesFirst ex t h then 1 else 0
      have match_stable (n : ℕ) (ex : Execution m) (hlen : t ≤ ex.observations.length)
          (ch : RoundChoice m) (v : Fin (m+1)) (h : FirstHistory m t) :
          matchesFirst (U n ex ch v) t h ↔ matchesFirst ex t h := by
        have hb : t-1 < ex.observations.length := by omega
        have hc : t-1 ≤ ex.observations.length := by omega
        simp only [matchesFirst, U, List.length_append, List.length_singleton,
          List.take_append_of_le_length hc, List.getElem?_append_left hb]
        simp only [show t ≤ ex.observations.length+1 by omega, hlen,
          show t ≤ ex.observations.length+1+1 by omega, ↓reduceIte, true_and]
      have f_stable (n : ℕ) (ex : Execution m) (hlen : t ≤ ex.observations.length)
          (ch : RoundChoice m) (v : Fin (m+1)) : F (U n ex ch v) = F ex := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [propext (match_stable n ex hlen ch v h)]
      have f_horizon (N : ℕ) (hN : t ≤ N) :
          average (publicRun r sel ν C false N) F = average (publicRun r sel ν C false t) F := by
        induction N, hN using Nat.le_induction with
        | base => rfl
        | succ n hn ih =>
          rw [run_step]
          calc
            _ = average (publicRun r sel ν C false n) F := by
              apply av_congr
              intro x hx
              have hlen : t ≤ x.1.observations.length := by rw [(run_support n x hx).1]; exact hn
              calc
                _ = average (samplePrice r sel ν C (n+1) x.1.stock false) (fun _ => F x.1) := by
                  apply av_congr
                  intro ch hch
                  rw [av_congr _ _ (fun _ => F x.1) (fun v hv => f_stable n x.1 hlen ch.1 v.1)]
                  exact av_constant _ (value_norm _) _
                _ = F x.1 := av_constant _ (sample_valid _ _).2 _
            _ = _ := ih
      have f_at_failure (n : ℕ) (hn : t = n+1) (ex : Execution m)
          (hlen : ex.observations.length = n) (ch : RoundChoice m) (v : Fin (m+1)) :
          F (U n ex ch v) ≤ if Good ex ∧ ch.failed = true then 1 else 0 := by
        by_cases he : ∃ h : FirstHistory m t, matchesFirst (U n ex ch v) t h
        · obtain ⟨h, hh⟩ := he
          have hsum : F (U n ex ch v) = 1 := by
            unfold F
            rw [Finset.sum_eq_single h]
            · simp [hh]
            · intro h' hh' hne
              have hh' : ¬ matchesFirst (U n ex ch v) t h' := by
                intro hm'
                exact hne (matches_unique _ _ _ hm' hh)
              simp [hh']
            · simp
          have htake : (U n ex ch v).observations.take (t-1) = ex.observations := by
            dsimp [U]
            rw [hn, Nat.add_sub_cancel, ← hlen, List.take_left]
          have hprefix : ex.observations = List.ofFn
              (fun i => (⟨false, (h i).1, (h i).2⟩ : Observation m)) :=
            htake.symm.trans hh.2.2.1
          have hg : Good ex := by
            intro o ho
            rw [hprefix] at ho
            obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ho
            rfl
          have hc : ch.failed = true := by
            have hflag := hh.2.2.2
            simpa [U, hn, ← hlen, List.getElem?_append_right] using hflag
          simp [hsum, hg, hc]
        · have hh : F (U n ex ch v) = 0 := by
            unfold F
            apply Finset.sum_eq_zero
            intro h hh
            simp [show ¬ matchesFirst (U n ex ch v) t h from fun hm => he ⟨h,hm⟩]
          rw [hh]
          split_ifs <;> norm_num
      have sample_fail (u a : ℕ) :
          average (samplePrice r sel ν C u a false) (fun ch => if ch.failed = true then 1 else 0) =
            (1-P (u-1) a)^(C*(k+1)*u^2) := by
        have hh := sample_av u a (fun b _ => if b = true then 1 else 0)
        simpa only [Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte,
          av_zero, mul_zero, mul_one, add_zero, ite_self] using hh
      have fail_step (n : ℕ) (hn : t = n+1) :
          average (publicRun r sel ν C false (n+1)) F ≤
          average (publicRun r sel ν C false n) (fun ex => if Good ex then
            (1-P n ex.stock)^(C*(k+1)*(n+1)^2) else 0) := by
        rw [run_step]
        apply av_mono _ (run_valid n).1
        intro x hx
        have hlen := (run_support n x hx).1
        calc
          _ ≤ average (samplePrice r sel ν C (n+1) x.1.stock false)
              (fun ch => if Good x.1 ∧ ch.failed = true then 1 else 0) := by
            apply av_mono _ (sample_valid _ _).1
            intro ch hch
            calc
              _ ≤ average (valueDraw (ν (n+1)))
                  (fun _ => if Good x.1 ∧ ch.1.failed = true then 1 else 0) := by
                apply av_mono _ (value_nonneg _)
                intro v hv
                exact f_at_failure n hn x.1 hlen ch.1 v.1
              _ = _ := av_constant _ (value_norm _) _
          _ = _ := by
            by_cases hg : Good x.1
            · simp only [hg, true_and, ↓reduceIte]
              simpa only [Nat.add_sub_cancel] using sample_fail (n+1) x.1.stock
            · simp only [hg, false_and, ↓reduceIte, av_zero]
      have analytic (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) (hN : 0 < N) :
          p*(1-p)^N ≤ 1/(Real.exp 1 * (N : ℝ)) := by
        have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
        have he : 0 < Real.exp 1 := Real.exp_pos _
        have hpow : (1-p)^N ≤ Real.exp (-(N*p)) := by
          have hh : 1-p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
          have hh' := pow_le_pow_left₀ (sub_nonneg.mpr hp1) hh N
          simpa only [← Real.exp_nat_mul, mul_neg] using hh'
        apply (le_div_iff₀ (mul_pos he hNr)).mpr
        calc
          _ ≤ p * Real.exp (-(N*p)) * (Real.exp 1 * N) := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hp0)
              (le_of_lt (mul_pos he hNr))
          _ = ((N:ℝ)*p * Real.exp (-((N:ℝ)*p))) * Real.exp 1 := by ring
          _ ≤ Real.exp (-1) * Real.exp 1 :=
            mul_le_mul_of_nonneg_right (Real.mul_exp_neg_le_exp_neg_one _) (le_of_lt he)
          _ = 1 := by rw [← Real.exp_add]; norm_num
      have hN : 0 < C*(k+1)*t^2 := by positivity
      have bound : (∑ a : Fin (k+1), P (t-1) a.val *
          (1-P (t-1) a.val)^(C*(k+1)*t^2)) ≤
          1/(Real.exp 1 * (C:ℝ) * (t:ℝ)^2) := by
        calc
          _ ≤ ∑ _a : Fin (k+1), 1/(Real.exp 1 * ((C*(k+1)*t^2:ℕ):ℝ)) := by
            apply Finset.sum_le_sum
            intro a ha
            exact analytic _ (p_bounds _ _).1 (p_bounds _ _).2 _ hN
          _ = _ := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
            have hc : (C:ℝ) ≠ 0 := by positivity
            have ht' : (t:ℝ) ≠ 0 := by positivity
            have hk' : (k:ℝ)+1 ≠ 0 := by positivity
            field_simp
            <;> ring
      calc
        firstFailureMass r sel ν C T t = average (publicRun r sel ν C false T) F := by
          unfold firstFailureMass firstMass F
          rw [av_sum]
        _ = average (publicRun r sel ν C false t) F := f_horizon T htT
        _ ≤ average (publicRun r sel ν C false (t-1)) (fun ex => if Good ex then
              (1-P (t-1) ex.stock)^(C*(k+1)*t^2) else 0) := by
          have hh := fail_step (t-1) (by omega)
          simpa only [Nat.sub_add_cancel ht] using hh
        _ ≤ average (simulate r sel ν (t-1)) (fun st =>
              (1-P (t-1) (inventory st.sold))^(C*(k+1)*t^2)) := by
          apply domination (t-1) (fun a => (1-P (t-1) a)^(C*(k+1)*t^2))
          intro a
          exact pow_nonneg (sub_nonneg.mpr (p_bounds _ _).2) _
        _ = ∑ a : Fin (k+1), P (t-1) a.val *
              (1-P (t-1) a.val)^(C*(k+1)*t^2) := group_sim (t-1) (fun a => (1-P (t-1) a)^(C*(k+1)*t^2))
        _ ≤ _ := bound
