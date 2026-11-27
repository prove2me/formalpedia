-- Prove2me | solution 1 for ValTrackRM.Public.Supplement.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:32:01.018696+00:00
-- url     : https://prove2.me/submissions/b9790b16-75a0-4c72-9a1a-2c3634d68a10

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
    (ht : 1 ≤ t) (htT : t ≤ T) (h : FirstHistory m t) :
    conditionalRevenue r sel ν C T true t h - conditionalRevenue r sel ν C T false t h ≤
      expectedOpt r k ν T := by
        classical
        have havg_branch {α β : Type} (xs : List (α × ℝ)) (f : α → List (β × ℝ))
            (g : β → ℝ) : average (branch xs f) g = average xs (fun a => average (f a) g) := by
          induction xs with
          | nil => simp [branch, average]
          | cons x xs ih =>
            simp only [branch, List.flatMap_cons, List.map_append, List.sum_append,
              average, List.map_cons, List.sum_cons] at *
            rw [← ih]
            congr 1
            simp only [List.map_map, Function.comp_def, mul_assoc]
            exact (List.sum_map_mul_left (f x.1) (fun y : β × ℝ => y.2 * g y.1) x.2)
        have havg_price (w : Price m → ℝ) (f : Price m → ℝ) :
            average (priceDraw w) f = ∑ p, w p * f p := by
          simp [average, priceDraw, List.map_map, ← List.ofFn_eq_map, List.sum_ofFn, Fin.sum_univ_succ]
        have havg_value (u : PMF (Fin (m + 1))) (f : Fin (m + 1) → ℝ) :
            average (valueDraw u) f = ∑ v, (u v).toReal * f v := by
          simp [average, valueDraw, List.map_map, ← List.ofFn_eq_map, List.sum_ofFn, Fin.sum_univ_succ]
        have hrmono : ∀ a b, a ≤ b → b ≤ m → r a ≤ r b := by
          intro a b hab hbm
          induction b with
          | zero => have : a = 0 := by omega
                    simp [this]
          | succ b ih =>
            rcases Nat.eq_or_lt_of_le hab with he | he
            · simp [he]
            · exact le_trans (ih (by omega) (by omega)) (le_of_lt (hr b (by omega)))
        have hrpos : ∀ j, 0 < j → j ≤ m → 0 < r j := by
          intro j hj hjm
          have h01 := hr 0 (by omega)
          have h1j := hrmono 1 j hj hjm
          simpa [hr0] using lt_of_lt_of_le h01 h1j
        have hqpos : ∀ j, 0 < j → j ≤ m → 0 < qj r j := by
          intro j hj hjm
          have hp := hrpos j hj hjm
          have hh := hr (j - 1) (by omega)
          have he : j - 1 + 1 = j := by omega
          rw [he] at hh
          exact sub_pos.mpr ((div_lt_one hp).mpr hh)
        have hqtpos : ∀ ℓ, ℓ < m → 0 < qTot r m ℓ := by
          intro ℓ hℓ
          apply Finset.sum_pos
          · intro j hj
            exact hqpos j (by have := (Finset.mem_Ioc.mp hj).1; omega) (Finset.mem_Ioc.mp hj).2
          · exact ⟨m, Finset.mem_Ioc.mpr ⟨hℓ, le_rfl⟩⟩
        have hunit : ∀ (L : Fin k → Fin (m + 1)) (s : Fin k → Bool),
            (∀ p, 0 ≤ unitPrice r sel L s p) ∧ ∑ p, unitPrice r sel L s p = 1 := by
          intro L s
          by_cases ha : s (sel L) = false ∧ (L (sel L)).val < m
          · constructor
            · intro p
              simp only [unitPrice, if_pos ha]
              split_ifs with hp
              · exact le_of_lt (div_pos (hqpos _ (by omega) (by omega)) (hqtpos _ ha.2))
              · exact le_rfl
            · simp only [unitPrice, if_pos ha]
              have he : (∑ p : Fin (m + 1),
                  if (L (sel L)).val < p.val + 1 ∧ p.val < m then qj r (p.val + 1) else 0) =
                  qTot r m (L (sel L)).val := by
                rw [qTot]
                apply Finset.sum_bij_ne_zero (fun p _ _ => p.val + 1)
                · intro p hp hn
                  split_ifs at hn with hh
                  · exact Finset.mem_Ioc.mpr ⟨hh.1, by omega⟩
                  · contradiction
                · intro p hp hn q hq hqn heq
                  exact Fin.ext (by omega)
                · intro j hj hn
                  refine ⟨⟨j - 1, by have := (Finset.mem_Ioc.mp hj).2; omega⟩, Finset.mem_univ _, ?_, ?_⟩
                  · simp only
                    rw [if_pos (by have := Finset.mem_Ioc.mp hj; omega)]
                    simpa only [show j - 1 + 1 = j by have := Finset.mem_Ioc.mp hj; omega] using hn
                  · have := Finset.mem_Ioc.mp hj
                    dsimp
                    omega
                · intro p hp hn
                  split_ifs with hh
                  · rfl
                  · exfalso
                    exact hn (if_neg hh)
              calc
                _ = (∑ p : Fin (m + 1), if (L (sel L)).val < p.val + 1 ∧ p.val < m then
                    qj r (p.val + 1) else 0) / qTot r m (L (sel L)).val := by
                  rw [Finset.sum_div]
                  apply Finset.sum_congr rfl
                  intro p hp
                  split_ifs <;> simp [offerProb]
                _ = 1 := by rw [he, div_self (ne_of_gt (hqtpos _ ha.2))]
          · simp only [unitPrice, if_neg ha, reject]
            constructor
            · intro p
              split_ifs <;> norm_num
            · have he : ∀ p : Price m, p.val = m ↔ p = ⟨m, by omega⟩ := fun p => ⟨fun hp => Fin.ext hp, fun hp => congrArg Fin.val hp⟩
              simp only [he]
              simp
        have hreject : (∀ p : Price m, 0 ≤ reject p) ∧ ∑ p : Price m, reject p = 1 := by
          constructor
          · intro p; unfold reject; split_ifs <;> norm_num
          · have he : ∀ p : Price m, p.val = m ↔ p = ⟨m, by omega⟩ :=
              fun p => ⟨fun hp => Fin.ext hp, fun hp => congrArg Fin.val hp⟩
            simp only [reject, he]
            simp
        have hval (u : PMF (Fin (m + 1))) : ∑ v, (u v).toReal = 1 := by
          have hs := u.tsum_coe
          rw [tsum_fintype] at hs
          have ht' := congrArg ENNReal.toReal hs
          simpa [ENNReal.toReal_sum, u.apply_ne_top] using ht'
        have hweight {n : ℕ} (W : Fin n → Fin (m + 1)) : 0 ≤ valuationWeight ν W := by
          unfold valuationWeight
          exact Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)
        have hlaw : ∀ W : List (Fin (m + 1)), ∀ s, 0 ≤ soldLaw r sel W s := by
          have hx : ∀ W : List (Fin (m + 1)), ∀ s, 0 ≤ soldLawRev r sel W s := by
            intro W
            induction W with
            | nil => intro s; simp only [soldLawRev]; split_ifs <;> norm_num
            | cons v W ih =>
              intro s
              simp only [soldLawRev, lawStep]
              apply Finset.sum_nonneg
              intro z hz
              apply mul_nonneg (ih z)
              by_cases ha : z (sel (levels sel W.reverse)) = false ∧
                  (levels sel W.reverse (sel (levels sel W.reverse))).val < m
              · rw [if_pos ha]
                apply Finset.sum_nonneg
                intro j hj
                have hj' := Finset.mem_Ioc.mp hj
                have ho : 0 ≤ offerProb r m (levels sel W.reverse (sel (levels sel W.reverse))).val j :=
                  le_of_lt (div_pos (hqpos _ (by omega) hj'.2) (hqtpos _ (by omega)))
                split_ifs <;> positivity
              · rw [if_neg ha]
                split_ifs <;> norm_num
          intro W s
          exact hx W.reverse s
        have ha1 : ∀ W a, (∀ p, 0 ≤ a1Joint r sel W a p) ∧
            0 ≤ a1Stock r sel W a ∧ (∑ p, a1Joint r sel W a p) = a1Stock r sel W a := by
          intro W a
          refine ⟨?_, ?_, ?_⟩
          · intro p
            unfold a1Joint
            apply Finset.sum_nonneg
            intro s hs
            apply mul_nonneg (hlaw W s)
            split_ifs
            · exact (hunit _ _).1 p
            · exact le_rfl
          · unfold a1Stock
            apply Finset.sum_nonneg
            intro s hs
            split_ifs <;> simp_all [hlaw]
          · unfold a1Joint a1Stock
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro s hs
            rw [← Finset.mul_sum]
            congr 1
            by_cases he : inventory s = a
            · simp only [if_pos he]
              exact (hunit _ _).2
            · simp [he]
        have hjoint : ∀ n a, (∀ p, 0 ≤ jointA1Price r sel ν n a p) ∧
            0 ≤ jointA1Stock r sel ν n a ∧
            (∑ p, jointA1Price r sel ν n a p) = jointA1Stock r sel ν n a := by
          intro n a
          refine ⟨?_, ?_, ?_⟩
          · intro p
            exact Finset.sum_nonneg (fun W _ => mul_nonneg (hweight W) ((ha1 _ _).1 p))
          · exact Finset.sum_nonneg (fun W _ => mul_nonneg (hweight W) (ha1 _ _).2.1)
          · unfold jointA1Price jointA1Stock
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro W hW
            rw [← Finset.mul_sum, (ha1 _ _).2.2]
        have hexp : ∀ n a, (∀ p, 0 ≤ expKernel r sel ν n a p) ∧
            (∑ p, expKernel r sel ν n a p) = 1 := by
          intro n a
          unfold expKernel
          split_ifs with he
          · exact hreject
          · constructor
            · intro p
              exact div_nonneg ((hjoint _ _).1 p) (hjoint _ _).2.1
            · rw [← Finset.sum_div, (hjoint _ _).2.2, div_self (by tauto)]
        have havg_map {α β : Type} (xs : List (α × ℝ)) (f : α → β) (g : β → ℝ) :
            average (xs.map (fun x => (f x.1, x.2))) g = average xs (fun x => g (f x)) := by
          simp [average, List.map_map, Function.comp_def]
        have havg_add {α : Type} (xs : List (α × ℝ)) (f g : α → ℝ) :
            average xs (fun a => f a + g a) = average xs f + average xs g := by
          simp [average, mul_add, List.sum_map_add]
        have havg_smul {α : Type} (xs : List (α × ℝ)) (c : ℝ) (f : α → ℝ) :
            average xs (fun a => c * f a) = c * average xs f := by
          simp only [average, mul_left_comm _ c]
          exact List.sum_map_mul_left _ _ _
        have havg_mono {α : Type} (xs : List (α × ℝ))
            (hx : ∀ x ∈ xs, 0 ≤ x.2) (f g : α → ℝ) (hfg : ∀ x ∈ xs, f x.1 ≤ g x.1) :
            average xs f ≤ average xs g := by
          unfold average
          apply List.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hfg i hi) (hx i hi)
        have havg_nonneg {α : Type} (xs : List (α × ℝ))
            (hx : ∀ x ∈ xs, 0 ≤ x.2) (f : α → ℝ) (hf : ∀ x ∈ xs, 0 ≤ f x.1) :
            0 ≤ average xs f := by
          unfold average
          exact List.sum_nonneg (fun x hx' => by
            obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx'
            exact mul_nonneg (hx a ha) (hf a ha))
        let Good : {α : Type} → List (α × ℝ) → Prop :=
          fun {_} xs => (∀ x ∈ xs, 0 ≤ x.2) ∧ average xs (fun _ => 1) = 1
        have hgood_const {α : Type} (xs : List (α × ℝ)) (hx : Good xs) (c : ℝ) :
            average xs (fun _ => c) = c := by
          simpa only [mul_one, hx.2] using havg_smul xs c (fun _ => 1)
        have hgood_single {α : Type} (a : α) : Good [(a, 1)] := by
          simp [Good, average]
        have hgood_map {α β : Type} (xs : List (α × ℝ)) (hx : Good xs) (f : α → β) :
            Good (xs.map fun x => (f x.1, x.2)) := by
          constructor
          · intro x hxm
            obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hxm
            exact hx.1 y hy
          · simpa only [havg_map] using hx.2
        have hgood_branch {α β : Type} (xs : List (α × ℝ)) (hx : Good xs)
            (f : α → List (β × ℝ)) (hf : ∀ a, Good (f a)) : Good (branch xs f) := by
          constructor
          · intro x hxm
            obtain ⟨a, ha, hxa⟩ := List.mem_flatMap.mp hxm
            obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hxa
            exact mul_nonneg (hx.1 a ha) ((hf a.1).1 b hb)
          · rw [havg_branch]
            simpa only [funext (fun a => (hf a).2)] using hx.2
        have hgood_price (w : Price m → ℝ) (hw : (∀ p, 0 ≤ w p) ∧ ∑ p, w p = 1) :
            Good (priceDraw w) := by
          constructor
          · intro x hx
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
            exact hw.1 p
          · simpa only [havg_price, mul_one] using hw.2
        have hgood_value (u : PMF (Fin (m + 1))) : Good (valueDraw u) := by
          constructor
          · intro x hx
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
            exact ENNReal.toReal_nonneg
          · simpa only [havg_value, mul_one] using hval u
        have hgood_sim : ∀ n, Good (simulate r sel ν n) := by
          intro n
          induction n with
          | zero => exact hgood_single _
          | succ n ih =>
            apply hgood_branch _ ih
            intro st
            apply hgood_branch _ (hgood_price _ (hunit _ _))
            intro p
            apply hgood_branch _ (hgood_value _)
            intro v
            exact hgood_single _
        have hgood_trials : ∀ n a fuel, Good (trials r sel ν n a fuel) := by
          intro n a fuel
          induction fuel with
          | zero => exact hgood_single _
          | succ fuel ih =>
            apply hgood_branch _ (hgood_sim n)
            intro st
            split_ifs
            · exact hgood_single _
            · apply hgood_branch _ ih
              intro rest
              exact hgood_single _
        have hgood_sample : ∀ n a b, Good (samplePrice r sel ν C n a b) := by
          intro n a b
          apply hgood_branch _ (hgood_trials _ _ _)
          intro res
          cases he : res.matched with
          | none =>
            dsimp only
            refine hgood_map _ ?_ (fun p : Price m =>
              (⟨true, p, res.operations + 10, res.transitions⟩ : RoundChoice m))
            apply hgood_price
            cases b
            · exact hreject
            · exact hexp _ _
          | some st =>
            dsimp only
            exact hgood_map _ (hgood_price _ (hunit _ _)) (fun p : Price m =>
              (⟨false, p, res.operations + selectorWork k +
                offerWork m (st.level (sel st.level)).val + 10, res.transitions⟩ : RoundChoice m))
        have hgood_run : ∀ n b, Good (publicRun r sel ν C b n) := by
          intro n b
          induction n with
          | zero => exact hgood_single _
          | succ n ih =>
            apply hgood_branch _ ih
            intro ex
            apply hgood_branch _ (hgood_sample _ _ _)
            intro ch
            apply hgood_branch _ (hgood_value _)
            intro v
            exact hgood_single _
        have hopt_le (a : ℕ) (V : List (Fin (m + 1))) (S : Finset (Fin V.length)) (hS : S.card ≤ a) :
            (∑ i ∈ S, r (V.get i)) ≤ opt r a V := by
          unfold opt
          exact Finset.le_sup' (s := Finset.univ.filter (fun S : Finset (Fin V.length) => S.card ≤ a))
            (fun S => ∑ i ∈ S, r (V.get i)) (b := S) (by simpa using hS)
        have hopt_nonneg (a : ℕ) (V : List (Fin (m + 1))) : 0 ≤ opt r a V := by
          simpa using hopt_le a V ∅ (by simp)
        have hopt_mono (a b : ℕ) (hab : a ≤ b) (V : List (Fin (m + 1))) :
            opt r a V ≤ opt r b V := by
          apply Finset.sup'_le
          intro S hS
          apply hopt_le
          exact le_trans (Finset.mem_filter.mp hS).2 hab
        have hopt_cons (a : ℕ) (v : Fin (m + 1)) (V : List (Fin (m + 1))) :
            opt r a V ≤ opt r a (v :: V) := by
          apply Finset.sup'_le
          intro S hS
          have hb := hopt_le a (v :: V) (S.map (Fin.succEmb V.length)) (by
            simpa using (Finset.mem_filter.mp hS).2)
          simpa using hb
        have hopt_buy (a : ℕ) (ha : 0 < a) (v : Fin (m + 1)) (V : List (Fin (m + 1))) :
            r v + opt r (a - 1) V ≤ opt r a (v :: V) := by
          obtain ⟨S, hS, he⟩ := Finset.exists_mem_eq_sup'
            (s := Finset.univ.filter (fun S : Finset (Fin V.length) => S.card ≤ a - 1))
            ⟨∅, by simp⟩ (fun S => ∑ i ∈ S, r (V.get i))
          change opt r (a - 1) V = _ at he
          have hz : (0 : Fin (v :: V).length) ∉ S.map (Fin.succEmb V.length) := by simp
          have hb := hopt_le a (v :: V) (insert 0 (S.map (Fin.succEmb V.length))) (by
            rw [Finset.card_insert_of_notMem hz, Finset.card_map]
            have := (Finset.mem_filter.mp hS).2
            omega)
          rw [Finset.sum_insert hz] at hb
          simpa [he] using hb
        have hpay_nonneg (a : ℕ) (p : Price m) (v : Fin (m + 1)) : 0 ≤ payment r a p v := by
          unfold payment
          by_cases hb : buys r a p v = true
          · have hp : 0 < a ∧ p.val < m ∧ r (p.val + 1) ≤ r v := by simpa [buys] using hb
            simp only [hb, ↓reduceIte]
            exact le_of_lt (hrpos _ (by omega) (by omega))
          · simp [hb]
        have hopt_step (a : ℕ) (p : Price m) (v : Fin (m + 1)) (V : List (Fin (m + 1))) :
            payment r a p v + opt r (nextStock r a p v) V ≤ opt r a (v :: V) := by
          by_cases hb : buys r a p v = true
          · have hp : 0 < a ∧ p.val < m ∧ r (p.val + 1) ≤ r v := by simpa [buys] using hb
            simp only [payment, nextStock, hb, ↓reduceIte]
            exact (add_le_add hp.2.2 (le_refl _)).trans (hopt_buy a hp.1 v V)
          · simpa [payment, nextStock, hb] using hopt_cons a v V
        let seq : ℕ → ℕ → List (List (Fin (m + 1)) × ℝ) :=
          Nat.rec (fun _ => [([], 1)]) (fun _ rec n =>
            branch (valueDraw (ν (n + 1))) (fun v =>
              (rec (n + 1)).map (fun x => (v :: x.1, x.2))))
        have hseq : ∀ d n, Good (seq d n) := by
          intro d
          induction d with
          | zero => intro n; exact hgood_single _
          | succ d ih =>
            intro n
            apply hgood_branch _ (hgood_value _)
            intro v
            exact hgood_map _ (ih _) _
        let U : ℕ → ℕ → ℕ → ℝ := fun d n a => average (seq d n) (opt r a)
        have hU_nonneg (d n a : ℕ) : 0 ≤ U d n a :=
          havg_nonneg _ (hseq d n).1 _ (fun _ _ => hopt_nonneg _ _)
        have hU_mono (d n a b : ℕ) (hab : a ≤ b) : U d n a ≤ U d n b :=
          havg_mono _ (hseq d n).1 _ _ (fun _ _ => hopt_mono a b hab _)
        have hopt_nil (a : ℕ) : opt r a ([] : List (Fin (m + 1))) = 0 := by
          apply le_antisymm _ (hopt_nonneg _ _)
          apply Finset.sup'_le
          intro S hS
          have he : S = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro i hi
            have := i.isLt
            simp at this
          simp [he]
        have hU_zero (n a : ℕ) : U 0 n a = 0 := by
          simpa [U, seq, average] using hopt_nil a
        have hU_eq (d n a : ℕ) : U (d + 1) n a =
            average (valueDraw (ν (n + 1))) (fun v =>
              average (seq d (n + 1)) (fun V => opt r a (v :: V))) := by
          exact (havg_branch _ _ _).trans (congrArg (average _) (funext (fun v => havg_map _ _ _)))
        have hU_prefix (d n a : ℕ) : U d (n + 1) a ≤ U (d + 1) n a := by
          rw [hU_eq]
          calc
            _ = average (valueDraw (ν (n + 1))) (fun _ => U d (n + 1) a) :=
              (hgood_const _ (hgood_value _) _).symm
            _ ≤ _ := havg_mono _ (hgood_value _).1 _ _ (fun x hx =>
              havg_mono _ (hseq _ _).1 _ _ (fun y hy => hopt_cons a x.1 y.1))
        have hU_start : ∀ n d a, U d n a ≤ U (n + d) 0 a := by
          intro n
          induction n with
          | zero => intro d a; simp
          | succ n ih =>
            intro d a
            exact (hU_prefix d n a).trans (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (d + 1) a)
        have hU_step (d n a : ℕ) (p : Price m) :
            average (valueDraw (ν (n + 1))) (fun v =>
              payment r a p v + U d (n + 1) (nextStock r a p v)) ≤ U (d + 1) n a := by
          rw [hU_eq]
          apply havg_mono _ (hgood_value _).1
          intro x hx
          calc
            _ = average (seq d (n + 1)) (fun V =>
                payment r a p x.1 + opt r (nextStock r a p x.1) V) := by
              rw [havg_add, hgood_const _ (hseq _ _)]
            _ ≤ _ := havg_mono _ (hseq _ _).1 _ _ (fun y hy => hopt_step _ _ _ _)
        have hseq_sum : ∀ d n (f : List (Fin (m + 1)) → ℝ),
            average (seq d n) f = ∑ W : Fin d → Fin (m + 1),
              (∏ i : Fin d, (ν (n + i.val + 1) (W i)).toReal) * f (List.ofFn W) := by
          intro d
          induction d with
          | zero => intro n f; simp [seq, average]
          | succ d ih =>
            intro n f
            change average (branch _ _) f = _
            rw [havg_branch, havg_value]
            have hmap (v : Fin (m + 1)) :
                average ((seq d (n + 1)).map (fun x => (v :: x.1, x.2))) f =
                average (seq d (n + 1)) (fun V => f (v :: V)) := havg_map _ (fun V => v :: V) _
            change (∑ v : Fin (m + 1), (ν (n + 1) v).toReal *
              average ((seq d (n + 1)).map (fun x => (v :: x.1, x.2))) f) = _
            simp_rw [hmap, ih]
            rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => Fin (m + 1))).sum_comp]
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro v hv
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro W hW
            simp [Fin.consEquiv, Fin.prod_univ_succ, List.ofFn_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, mul_assoc]
        have hU_opt : U T 0 k = expectedOpt r k ν T := by
          simpa [U, expectedOpt, valuationWeight] using hseq_sum T 0 (opt r k)
        have havg_congr {α : Type} (xs : List (α × ℝ)) (f g : α → ℝ)
            (he : ∀ x ∈ xs, f x.1 = g x.1) : average xs f = average xs g := by
          unfold average
          congr 1
          apply List.map_congr_left
          intro x hx
          rw [he x hx]
        have havg_ite {α : Type} (xs : List (α × ℝ)) (P : Prop) (f g : α → ℝ) :
            average xs (fun x => if P then f x else g x) =
              if P then average xs f else average xs g := by
          by_cases hp : P <;> simp [hp]
        have hbranch_all {α β : Type} (xs : List (α × ℝ)) (f : α → List (β × ℝ)) (P : β → Prop)
            (hp : ∀ x ∈ xs, ∀ y ∈ f x.1, P y.1) : ∀ y ∈ branch xs f, P y.1 := by
          intro y hy
          obtain ⟨x, hx, hz⟩ := List.mem_flatMap.mp hy
          obtain ⟨z, hzf, rfl⟩ := List.mem_map.mp hz
          exact hp x hx z hzf
        let advance : ℕ → Execution m → RoundChoice m → Fin (m + 1) → Execution m :=
          fun n ex ch v => ⟨ex.observations ++ [(⟨ch.failed, ch.price, v⟩ : Observation m)],
            nextStock r ex.stock ch.price v, ex.revenue + payment r ex.stock ch.price v,
            ex.operations + ch.operations + 10 * (n + k + m + 1),
            ex.simulatedTransitions + ch.transitions⟩
        have hrun_step (n : ℕ) (b : Bool) (f : Execution m → ℝ) :
            average (publicRun r sel ν C b (n + 1)) f =
            average (publicRun r sel ν C b n) (fun ex =>
              average (samplePrice r sel ν C (n + 1) ex.stock b) (fun ch =>
                average (valueDraw (ν (n + 1))) (fun v => f (advance n ex ch v)))) := by
          rw [publicRun, havg_branch]
          congr 1
          funext ex
          rw [havg_branch]
          congr 1
          funext ch
          rw [havg_branch]
          congr 1
          funext v
          simp [average, advance]
        let ev : List (Observation m) → ℕ × ℝ := fun O =>
          O.foldl (fun z o => (nextStock r z.1 o.price o.value,
            z.2 + payment r z.1 o.price o.value)) (k, 0)
        have hev (O : List (Observation m)) (o : Observation m) :
            ev (O ++ [o]) = (nextStock r (ev O).1 o.price o.value,
              (ev O).2 + payment r (ev O).1 o.price o.value) := by
          simp [ev, List.foldl_append]
        have hrun_inv : ∀ n b x, x ∈ publicRun r sel ν C b n →
            x.1.observations.length = n ∧ x.1.stock ≤ k ∧
            x.1.stock = (ev x.1.observations).1 ∧ x.1.revenue = (ev x.1.observations).2 := by
          intro n b
          induction n with
          | zero =>
            intro x hx
            simp only [publicRun, List.mem_singleton] at hx
            subst x
            simp [ev]
          | succ n ih =>
            rw [publicRun]
            refine hbranch_all _ _ (fun ex : Execution m => ex.observations.length = n + 1 ∧
              ex.stock ≤ k ∧ ex.stock = (ev ex.observations).1 ∧ ex.revenue = (ev ex.observations).2) ?_
            intro ex hex
            refine hbranch_all _ _ (fun ex : Execution m => ex.observations.length = n + 1 ∧
              ex.stock ≤ k ∧ ex.stock = (ev ex.observations).1 ∧ ex.revenue = (ev ex.observations).2) ?_
            intro ch hch
            refine hbranch_all _ _ (fun ex : Execution m => ex.observations.length = n + 1 ∧
              ex.stock ≤ k ∧ ex.stock = (ev ex.observations).1 ∧ ex.revenue = (ev ex.observations).2) ?_
            intro v hv x hx
            simp only [List.mem_singleton] at hx
            subst x
            obtain ⟨hlen, hstock, hs, hr'⟩ := ih ex hex
            refine ⟨by simpa using hlen, ?_, ?_, ?_⟩
            · exact le_trans (Nat.sub_le _ _) hstock
            · simpa only [hev, hs]
            · simpa only [hev, hs, hr']
        let H : List (Observation m) := List.ofFn (fun i => (⟨false, (h i).1, (h i).2⟩ : Observation m))
        have hHlen : H.length = t - 1 := by simp [H]
        let B : Execution m → Prop := fun ex => matchesFirst ex t h
        have hB_next (n : ℕ) (ex : Execution m) (hlen : ex.observations.length = n)
            (hn : t ≤ n) (ch : RoundChoice m) (v : Fin (m + 1)) :
            B (advance n ex ch v) ↔ B ex := by
          have htake : (ex.observations ++ [(⟨ch.failed, ch.price, v⟩ : Observation m)]).take (t - 1) =
              ex.observations.take (t - 1) := List.take_append_of_le_length (by omega)
          have hget : (ex.observations ++ [(⟨ch.failed, ch.price, v⟩ : Observation m)])[t - 1]? =
              ex.observations[t - 1]? := List.getElem?_append_left (by omega)
          simp only [B, matchesFirst, advance, List.length_append, List.length_singleton,
            htake, hget, hlen, if_pos hn, if_pos (show t ≤ n + 1 by omega), ht,
            show t ≤ n + 1 by omega, show t ≤ n + 1 + 1 by omega, true_and, if_true]
        have hB_boundary (ex : Execution m) (hlen : ex.observations.length = t - 1)
            (ch : RoundChoice m) (v : Fin (m + 1)) :
            B (advance (t - 1) ex ch v) ↔ ex.observations = H ∧ ch.failed = true := by
          have htake : (ex.observations ++ [(⟨ch.failed, ch.price, v⟩ : Observation m)]).take (t - 1) =
              ex.observations := by
            rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
          have hget : (ex.observations ++ [(⟨ch.failed, ch.price, v⟩ : Observation m)])[t - 1]? =
              some (⟨ch.failed, ch.price, v⟩ : Observation m) := by
            rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]
            rfl
          simp only [B, matchesFirst, advance, List.length_append, List.length_singleton,
            htake, hget, hlen, Option.map_some, Option.getD_some]
          have he : t ≤ t - 1 + 1 := by omega
          simp [ht, he, H]
        have hsample_clear (n a : ℕ) (f : Price m → ℝ) :
            average (samplePrice r sel ν C n a true)
                (fun ch => if ch.failed = false then f ch.price else 0) =
            average (samplePrice r sel ν C n a false)
                (fun ch => if ch.failed = false then f ch.price else 0) := by
          simp only [samplePrice, havg_branch]
          congr 1
          funext res
          cases he : res.matched with
          | none =>
            dsimp only
            simp only [havg_price, average, List.map_map, Function.comp_def]
            simp
          | some st => rfl
        have hsample_fail (n a : ℕ) :
            average (samplePrice r sel ν C n a true) (fun ch => if ch.failed = true then 1 else 0) =
            average (samplePrice r sel ν C n a false) (fun ch => if ch.failed = true then 1 else 0) := by
          simp only [samplePrice, havg_branch]
          congr 1
          funext res
          cases he : res.matched with
          | none =>
            dsimp only
            have ht' := hgood_map _ (hgood_price _ (hexp n a))
              (fun p : Price m => (⟨true, p, res.operations + 10, res.transitions⟩ : RoundChoice m))
            have hf' := hgood_map _ (hgood_price _ hreject)
              (fun p : Price m => (⟨true, p, res.operations + 10, res.transitions⟩ : RoundChoice m))
            simpa [average, List.map_map, Function.comp_def] using ht'.2.trans hf'.2.symm
          | some st => rfl
        have hcv (n : ℕ) (c : ℝ) : average (valueDraw (ν n)) (fun _ => c) = c :=
          hgood_const _ (hgood_value _) _
        have hcs (n a : ℕ) (b : Bool) (c : ℝ) :
            average (samplePrice r sel ν C n a b) (fun _ => c) = c :=
          hgood_const _ (hgood_sample _ _ _) _
        let clear : List (Observation m) → Prop := fun O => ∀ o ∈ O, o.failed = false
        have hclear_append (O : List (Observation m)) (o : Observation m) :
            clear (O ++ [o]) ↔ clear O ∧ o.failed = false := by
          constructor
          · intro hc
            exact ⟨fun z hz => hc z (List.mem_append_left _ hz), hc o (by simp)⟩
          · rintro ⟨hc, ho⟩ z hz
            rcases List.mem_append.mp hz with hz | hz
            · exact hc z hz
            · simpa only [List.mem_singleton.mp hz] using ho
        have hHclear : clear H := by
          intro o ho
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp ho
          rw [← hi]
        have hclear_common : ∀ n (f : List (Observation m) → ℝ),
            average (publicRun r sel ν C true n) (fun ex => if clear ex.observations then f ex.observations else 0) =
            average (publicRun r sel ν C false n) (fun ex => if clear ex.observations then f ex.observations else 0) := by
          intro n
          induction n with
          | zero => intro f; rfl
          | succ n ih =>
            intro f
            let F : List (Observation m) → ℝ := fun O =>
              average (samplePrice r sel ν C (n + 1) (ev O).1 false) (fun ch =>
                if ch.failed = false then
                  average (valueDraw (ν (n + 1))) (fun v =>
                    f (O ++ [(⟨false, ch.price, v⟩ : Observation m)])) else 0)
            have hrec (b : Bool) :
                average (publicRun r sel ν C b (n + 1))
                    (fun ex => if clear ex.observations then f ex.observations else 0) =
                average (publicRun r sel ν C b n)
                    (fun ex => if clear ex.observations then F ex.observations else 0) := by
              rw [hrun_step]
              apply havg_congr
              intro x hx
              have hs := (hrun_inv n b x hx).2.2.1
              dsimp only [advance]
              rw [hs]
              by_cases hc : clear x.1.observations
              · simp only [hclear_append, hc, true_and, if_true]
                have hi (ch : RoundChoice m) :
                    average (valueDraw (ν (n + 1))) (fun v =>
                      if ch.failed = false then
                        f (x.1.observations ++ [(⟨ch.failed, ch.price, v⟩ : Observation m)]) else 0) =
                    if ch.failed = false then average (valueDraw (ν (n + 1))) (fun v =>
                      f (x.1.observations ++ [(⟨false, ch.price, v⟩ : Observation m)])) else 0 := by
                  by_cases hf : ch.failed = false <;> simp [hf, hcv]
                simp_rw [hi]
                cases b
                · rfl
                · simpa only [F] using hsample_clear (n + 1) (ev x.1.observations).1
                    (fun p => average (valueDraw (ν (n + 1))) (fun v =>
                      f (x.1.observations ++ [(⟨false, p, v⟩ : Observation m)])))
              · simp only [hclear_append, hc, false_and, if_false, hcv, hcs]
            rw [hrec true, hrec false]
            exact ih F
        let M : Bool → ℕ → ℝ := fun b n =>
          average (publicRun r sel ν C b n) (fun ex => if B ex then 1 else 0)
        have hM_nonneg (b : Bool) (n : ℕ) : 0 ≤ M b n := by
          apply havg_nonneg _ (hgood_run _ _).1
          intro x hx
          split_ifs <;> norm_num
        have hM_step (b : Bool) (n : ℕ) (hn : t ≤ n) : M b (n + 1) = M b n := by
          unfold M
          rw [hrun_step]
          apply havg_congr
          intro x hx
          have he := (hrun_inv n b x hx).1
          simp_rw [hB_next n x.1 he hn]
          rw [hcv, hcs]
        have hM_constant (b : Bool) : ∀ n, t ≤ n → M b n = M b t := by
          intro n hn
          induction n, hn using Nat.le_induction with
          | base => rfl
          | succ n hn ih => rw [hM_step b n hn, ih]
        have hM_boundary (b : Bool) : M b t =
            average (publicRun r sel ν C b (t - 1)) (fun ex =>
              if ex.observations = H then
                average (samplePrice r sel ν C t (ev ex.observations).1 false)
                  (fun ch => if ch.failed = true then 1 else 0) else 0) := by
          have he : t - 1 + 1 = t := by omega
          unfold M
          conv_lhs => rw [← he]
          rw [hrun_step]
          apply havg_congr
          intro x hx
          have hl := (hrun_inv (t - 1) b x hx).1
          have hs := (hrun_inv (t - 1) b x hx).2.2.1
          simp_rw [hB_boundary x.1 hl]
          rw [he, hs]
          by_cases hp : x.1.observations = H
          · simp only [hp, true_and, if_true]
            simp_rw [hcv]
            cases b
            · rfl
            · exact hsample_fail _ _
          · simp only [hp, false_and, if_false, hcv, hcs]
        have hM_equal : M true t = M false t := by
          rw [hM_boundary true, hM_boundary false]
          let f : List (Observation m) → ℝ := fun O =>
            if O = H then average (samplePrice r sel ν C t (ev O).1 false)
              (fun ch => if ch.failed = true then 1 else 0) else 0
          have he (ex : Execution m) : f ex.observations =
              if clear ex.observations then f ex.observations else 0 := by
            by_cases hp : ex.observations = H
            · simp [hp, hHclear]
            · simp [f, hp]
          change average (publicRun r sel ν C true (t - 1)) (fun ex => f ex.observations) =
            average (publicRun r sel ν C false (t - 1)) (fun ex => f ex.observations)
          calc
            _ = average (publicRun r sel ν C true (t - 1))
                (fun ex => if clear ex.observations then f ex.observations else 0) :=
              havg_congr _ _ _ (fun x _ => he x.1)
            _ = _ := hclear_common _ f
            _ = _ := (havg_congr _ _ _ (fun x _ => he x.1)).symm
        let R : ℝ := (ev H).2
        let Q : ℝ := U (T - (t - 1)) (t - 1) k
        let N : Bool → ℕ → ℝ := fun b n =>
          average (publicRun r sel ν C b n) (fun ex => if B ex then ex.revenue else 0)
        have hev_mono (O D : List (Observation m)) : (ev O).2 ≤ (ev (O ++ D)).2 := by
          induction D using List.reverseRecOn with
          | nil => simp
          | append_singleton D o ih =>
            rw [← List.append_assoc, hev]
            exact ih.trans (le_add_of_nonneg_right (hpay_nonneg _ _ _))
        have hN_lower (b : Bool) (n : ℕ) : R * M b n ≤ N b n := by
          unfold M N
          rw [← havg_smul]
          apply havg_mono _ (hgood_run _ _).1
          intro x hx
          by_cases hb : B x.1
          · simp only [if_pos hb, mul_one]
            have hpre : x.1.observations.take (t - 1) = H := hb.2.2.1
            rw [(hrun_inv n b x hx).2.2.2]
            calc
              R = (ev (x.1.observations.take (t - 1))).2 := by rw [hpre]
              _ ≤ (ev (x.1.observations.take (t - 1) ++ x.1.observations.drop (t - 1))).2 := hev_mono _ _
              _ = _ := by rw [List.take_append_drop]
          · simp [hb]
        let P : Bool → ℕ → ℝ := fun b n =>
          average (publicRun r sel ν C b n) (fun ex =>
            if B ex then ex.revenue + U (T - n) n ex.stock else 0)
        have hP_step (b : Bool) (n : ℕ) (hn : t ≤ n) (hnT : n < T) : P b (n + 1) ≤ P b n := by
          unfold P
          rw [hrun_step]
          apply havg_mono _ (hgood_run _ _).1
          intro x hx
          have he := (hrun_inv n b x hx).1
          simp_rw [hB_next n x.1 he hn]
          by_cases hb : B x.1
          · simp only [if_pos hb]
            calc
              _ ≤ average (samplePrice r sel ν C (n + 1) x.1.stock b)
                  (fun _ => x.1.revenue + U (T - n) n x.1.stock) := by
                apply havg_mono _ (hgood_sample _ _ _).1
                intro ch hch
                dsimp only [advance]
                simp_rw [add_assoc]
                rw [havg_add, hcv]
                apply add_le_add le_rfl
                have hd : T - n = T - (n + 1) + 1 := by omega
                rw [hd]
                exact hU_step _ _ _ _
              _ = _ := hcs _ _ _ _
          · simp only [if_neg hb, hcv, hcs, le_refl]
        have hP_bound (b : Bool) : ∀ n, t ≤ n → n ≤ T → P b n ≤ P b t := by
          intro n hn
          induction n, hn using Nat.le_induction with
          | base => intro _; exact le_rfl
          | succ n hn ih =>
            intro hnT
            exact (hP_step b n hn (by omega)).trans (ih (by omega))
        have hP_boundary (b : Bool) : P b t ≤ (R + Q) * M b t := by
          have he : t - 1 + 1 = t := by omega
          unfold P M
          conv_lhs => rw [← he]
          conv_rhs => arg 2; rw [← he]
          rw [hrun_step, hrun_step, ← havg_smul]
          apply havg_mono _ (hgood_run _ _).1
          intro x hx
          obtain ⟨hlen, hsk, hs, hr'⟩ := hrun_inv (t - 1) b x hx
          simp_rw [hB_boundary x.1 hlen]
          rw [he]
          by_cases hp : x.1.observations = H
          · have hrev : x.1.revenue = R := by simpa only [hp] using hr'
            simp only [hp, true_and]
            simp_rw [hcv]
            rw [← havg_smul]
            apply havg_mono _ (hgood_sample _ _ _).1
            intro ch hch
            by_cases hf : ch.1.failed = true
            · simp only [if_pos hf, mul_one]
              dsimp only [advance]
              rw [hrev]
              simp_rw [add_assoc]
              rw [havg_add, hcv]
              apply add_le_add le_rfl
              have hbell := hU_step (T - t) (t - 1) x.1.stock ch.1.price
              rw [he] at hbell
              have hd : T - t + 1 = T - (t - 1) := by omega
              rw [hd] at hbell
              exact hbell.trans (hU_mono _ _ _ _ hsk)
            · simp only [if_neg hf, hcv, mul_zero, le_refl]
          · simp only [hp, false_and, if_false, hcv, hcs, mul_zero, le_refl]
        have hN_upper (b : Bool) : N b T ≤ (R + Q) * M b T := by
          have he : P b T = N b T := by simp only [P, N, Nat.sub_self, hU_zero, add_zero]
          rw [← he, hM_constant b T htT]
          exact (hP_bound b T htT le_rfl).trans (hP_boundary b)
        have hQ : Q ≤ expectedOpt r k ν T := by
          have hh := hU_start (t - 1) (T - (t - 1)) k
          have he : t - 1 + (T - (t - 1)) = T := by omega
          simpa only [he, hU_opt] using hh
        have heq : M true T = M false T := by
          rw [hM_constant true T htT, hM_constant false T htT, hM_equal]
        have hopt0 : 0 ≤ expectedOpt r k ν T := by
          rw [← hU_opt]
          exact hU_nonneg _ _ _
        change N true T / M true T - N false T / M false T ≤ expectedOpt r k ν T
        by_cases hz : M true T = 0
        · rw [← heq, hz]
          simpa using hopt0
        · have hpos : 0 < M true T := lt_of_le_of_ne (hM_nonneg true T) (Ne.symm hz)
          have hu : N true T / M true T ≤ R + Q := by
            apply (div_le_iff₀ hpos).mpr
            simpa only [mul_comm] using hN_upper true
          have hl : R ≤ N false T / M true T := by
            apply (le_div_iff₀ hpos).mpr
            rw [heq]
            exact hN_lower false T
          rw [← heq]
          linarith
