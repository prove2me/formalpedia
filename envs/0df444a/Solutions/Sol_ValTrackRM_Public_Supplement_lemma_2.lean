-- Prove2me | solution 1 for ValTrackRM.Public.Supplement.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:31:34.206449+00:00
-- url     : https://prove2.me/submissions/97ec246b-fc5f-4fb5-8112-f02fc2d8f02f

import Mathlib
import Definitions.Def_ValTrackRM_Public_Supplement_Inventory

open ValTrackRM
open ValTrackRM.Public
open ValTrackRM.Public.Supplement

theorem solution
    (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ)
    (hr0 : r 0 = 0) (hr : ∀ j < m, r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : isMin sel)
    (V : List (Fin (m + 1))) :
    (∀ (t : ℕ), 1 ≤ t → t ≤ V.length → ∀ (a : Fin (k + 1)),
      0 < fixedStock r k (primeKernel r sel V) V (t - 1) a.val → ∀ p : Price m,
      fixedConditional r k (primeKernel r sel V) V t a.val p =
        a1Joint r sel (V.take (t - 1)) a.val p / a1Stock r sel (V.take (t - 1)) a.val) ∧
    (∀ (t : ℕ), t ≤ V.length → ∀ a : Fin (k + 1),
      fixedStock r k (primeKernel r sel V) V t a.val = a1Stock r sel (V.take t) a.val) := by
        have hrnn : ∀ p, p ≤ m → 0 ≤ r p := by
          intro p
          induction p with
          | zero => intro _; rw [hr0]
          | succ n ih => intro h; have := hr n (by omega); linarith [ih (by omega)]
        have hqj : ∀ p, 1 ≤ p → p ≤ m → 0 ≤ qj r p := by
          intro p h1 h2
          have hlt : r (p - 1) < r p := by
            have := hr (p - 1) (by omega); rwa [Nat.sub_add_cancel h1] at this
          have hpos : 0 < r p := lt_of_le_of_lt (hrnn (p-1) (by omega)) hlt
          unfold qj
          have : r (p - 1) / r p ≤ 1 := div_le_one_of_le₀ hlt.le hpos.le
          linarith
        have hoff : ∀ ℓ p, ℓ < p → p ≤ m → 0 ≤ offerProb r m ℓ p := by
          intro ℓ p h1 h2
          unfold offerProb
          apply div_nonneg (hqj p (by omega) h2)
          unfold qTot
          apply Finset.sum_nonneg
          intro q hq
          rw [Finset.mem_Ioc] at hq
          exact hqj q (by omega) hq.2
        have hμ : ∀ W : List (Fin (m+1)), ∀ s, 0 ≤ soldLaw r sel W s := by
          intro W
          unfold soldLaw
          generalize W.reverse = R
          induction R with
          | nil => intro s; simp only [soldLawRev]; split_ifs <;> norm_num
          | cons j R ih =>
            intro s'
            dsimp only [soldLawRev, lawStep]
            apply Finset.sum_nonneg
            intro s _
            apply mul_nonneg (ih s)
            split
            · apply Finset.sum_nonneg
              intro p hp
              rw [Finset.mem_Ioc] at hp
              apply mul_nonneg (hoff _ _ hp.1 hp.2)
              split_ifs <;> norm_num
            · split <;> norm_num
        have hinv_le : ∀ s : Fin k → Bool, inventory s ≤ k := by
          intro s; unfold inventory
          calc _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_filter_le _ _
            _ = k := by simp
        have hinv_pos : ∀ (s : Fin k → Bool) (i : Fin k), s i = false → 1 ≤ inventory s := by
          intro s i hi; unfold inventory
          apply Finset.card_pos.mpr
          exact ⟨i, by simp [hi]⟩
        have hinv_upd : ∀ (s : Fin k → Bool) (i : Fin k), s i = false →
            inventory (Function.update s i true) = inventory s - 1 := by
          intro s i hi; unfold inventory
          have : Finset.univ.filter (fun j => Function.update s i true j = false)
              = (Finset.univ.filter fun j => s j = false).erase i := by
            ext j; by_cases hj : j = i
            · subst hj; simp
            · simp [hj]
          rw [this, Finset.card_erase_of_mem (by simp [hi])]
        have hdecomp : ∀ (W : List (Fin (m+1))) (a : ℕ) (p : Price m),
            a1Stock r sel W a = (∑ s, soldLaw r sel W s *
                if inventory s = a ∧ s (sel (levels sel W)) = true then 1 else 0) +
              (∑ s, soldLaw r sel W s *
                if inventory s = a ∧ s (sel (levels sel W)) = false then 1 else 0) ∧
            a1Joint r sel W a p = (∑ s, soldLaw r sel W s *
                if inventory s = a ∧ s (sel (levels sel W)) = true then 1 else 0) * reject p +
              (∑ s, soldLaw r sel W s *
                if inventory s = a ∧ s (sel (levels sel W)) = false then 1 else 0) *
              (if (levels sel W (sel (levels sel W))).val < m then
                (if (levels sel W (sel (levels sel W))).val < p.val + 1 ∧ p.val < m then
                  offerProb r m (levels sel W (sel (levels sel W))).val (p.val+1) else 0)
               else reject p) ∧
            (a = 0 → (∑ s, soldLaw r sel W s *
                if inventory s = a ∧ s (sel (levels sel W)) = false then 1 else 0) = 0) := by
          intro W a p
          refine ⟨?_, ?_, ?_⟩
          · simp only [a1Stock, ← Finset.sum_add_distrib, ← mul_add]
            apply Finset.sum_congr rfl; intro s _; congr 1
            cases h : s (sel (levels sel W)) <;> by_cases ha : inventory s = a <;> simp [ha]
          · simp only [a1Joint, Finset.sum_mul, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro s _
            rw [mul_assoc, mul_assoc, ← mul_add]; congr 1
            unfold unitPrice
            cases h : s (sel (levels sel W)) <;> by_cases ha : inventory s = a <;> simp [h, ha]
          · intro ha; apply Finset.sum_eq_zero; intro s _
            rw [if_neg]; · simp
            rintro ⟨h1, h2⟩; have := hinv_pos s _ h2; omega
        have hP1 : ∀ (t a : ℕ) (p : Price m), a1Stock r sel (V.take (t-1)) a ≠ 0 →
            primeKernel r sel V t a p =
              a1Joint r sel (V.take (t-1)) a p / a1Stock r sel (V.take (t-1)) a := by
          intro t a p hA
          obtain ⟨h1, h2, h3⟩ := hdecomp (V.take (t-1)) a p
          unfold primeKernel soldConditional
          simp only []
          rw [h2, h1]; rw [h1] at hA
          generalize (∑ s, soldLaw r sel (V.take (t-1)) s *
                if inventory s = a ∧ s (sel (levels sel (V.take (t-1)))) = true then 1 else 0) = B at *
          generalize (∑ s, soldLaw r sel (V.take (t-1)) s *
                if inventory s = a ∧ s (sel (levels sel (V.take (t-1)))) = false then 1 else 0) = C at *
          have hℓ := (levels sel (V.take (t-1)) (sel (levels sel (V.take (t-1))))).isLt
          generalize ((levels sel (V.take (t-1)) (sel (levels sel (V.take (t-1))))).val) = ℓ at *
          have hpm := p.isLt
          by_cases ha : a = 0
          · rw [h3 ha] at hA ⊢; simp only [ha, true_or, if_true]; field_simp; ring
          by_cases hl : ℓ = m
          · simp only [hl, or_true, if_true, lt_irrefl, if_false]; field_simp
          have hlm : ℓ < m := by omega
          simp only [ha, hA, hl, false_or, if_false, hlm, if_true]
          unfold reject
          by_cases hp : p.val = m
          · simp only [hp, if_true, lt_irrefl, and_false, if_false]; field_simp; ring
          · simp only [hp, if_false]
            by_cases hq : ℓ < p.val + 1
            · have : p.val < m := by omega
              simp only [hq, this, and_self, if_true]; field_simp; ring
            · simp only [hq, false_and, if_false]; ring
        have hI : ∀ (t a : ℕ) (p : Price m),
            a1Stock r sel (V.take (t-1)) a * primeKernel r sel V t a p =
              a1Joint r sel (V.take (t-1)) a p := by
          intro t a p
          by_cases hA : a1Stock r sel (V.take (t-1)) a = 0
          · rw [hA, zero_mul]
            obtain ⟨h1, h2, h3⟩ := hdecomp (V.take (t-1)) a p
            rw [h2]; rw [h1] at hA
            have hB : 0 ≤ (∑ s, soldLaw r sel (V.take (t-1)) s *
                if inventory s = a ∧ s (sel (levels sel (V.take (t-1)))) = true then 1 else 0) := by
              apply Finset.sum_nonneg; intro s _
              apply mul_nonneg (hμ _ s); split_ifs <;> norm_num
            have hC : 0 ≤ (∑ s, soldLaw r sel (V.take (t-1)) s *
                if inventory s = a ∧ s (sel (levels sel (V.take (t-1)))) = false then 1 else 0) := by
              apply Finset.sum_nonneg; intro s _
              apply mul_nonneg (hμ _ s); split_ifs <;> norm_num
            have hB0 : (∑ s, soldLaw r sel (V.take (t-1)) s *
                if inventory s = a ∧ s (sel (levels sel (V.take (t-1)))) = true then 1 else 0) = 0 := by
              linarith
            have hC0 : (∑ s, soldLaw r sel (V.take (t-1)) s *
                if inventory s = a ∧ s (sel (levels sel (V.take (t-1)))) = false then 1 else 0) = 0 := by
              linarith
            rw [hB0, hC0]; ring
          · rw [hP1 t a p hA]; field_simp
        have hII : ∀ (W : List (Fin (m+1))) (v : Fin (m+1)) (b : ℕ),
            a1Stock r sel (W ++ [v]) b = ∑ a : Fin (k+1), ∑ p : Price m,
              a1Joint r sel W a.val p * if nextStock r a.val p v = b then 1 else 0 := by
          intro W v b
          have hstep : soldLaw r sel (W ++ [v]) = lawStep r sel (levels sel W) v (soldLaw r sel W) := by
            simp [soldLaw, soldLawRev]
          unfold a1Stock a1Joint
          rw [hstep]
          have hrhs : (∑ a : Fin (k+1), ∑ p : Price m, (∑ s, soldLaw r sel W s *
              (if inventory s = a.val then unitPrice r sel (levels sel W) s p else 0)) *
                if nextStock r a.val p v = b then 1 else 0) =
              ∑ s, soldLaw r sel W s * ∑ p : Price m, unitPrice r sel (levels sel W) s p *
                if nextStock r (inventory s) p v = b then 1 else 0 := by
            simp only [Finset.sum_mul]
            calc _ = ∑ a : Fin (k+1), ∑ s, ∑ p : Price m, soldLaw r sel W s *
                  (if inventory s = a.val then unitPrice r sel (levels sel W) s p else 0) *
                    (if nextStock r a.val p v = b then 1 else 0) := by
                  apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm]
              _ = ∑ s, ∑ a : Fin (k+1), ∑ p : Price m, soldLaw r sel W s *
                  (if inventory s = a.val then unitPrice r sel (levels sel W) s p else 0) *
                    (if nextStock r a.val p v = b then 1 else 0) := Finset.sum_comm
              _ = _ := by
                  apply Finset.sum_congr rfl; intro s _
                  rw [Finset.sum_eq_single ⟨inventory s, by have := hinv_le s; omega⟩]
                  · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; simp
                  · intro c _ hc; apply Finset.sum_eq_zero; intro p _; rw [if_neg]; · simp
                    intro h; apply hc; ext; simp [h]
                  · simp
          rw [hrhs]
          dsimp only [lawStep]
          simp only [Finset.sum_mul]; rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro s _
          rw [Finset.sum_congr rfl (fun _ _ => mul_assoc _ _ _), ← Finset.mul_sum]
          congr 1
          unfold unitPrice
          set i := sel (levels sel W) with hi
          set ℓ := (levels sel W i).val with hℓ
          by_cases hc : s i = false ∧ ℓ < m
          · simp only [if_pos hc]
            have hsi := hinv_pos s i hc.1
            have hupd := hinv_upd s i hc.1
            trans ∑ q ∈ Finset.Ioc ℓ m, offerProb r m ℓ q * (if r q ≤ r v then
                (if inventory s - 1 = b then (1:ℝ) else 0) else (if inventory s = b then 1 else 0))
            · simp only [Finset.sum_mul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro q _
              by_cases hq : r q ≤ r v
              · simp only [if_pos hq]
                rw [Finset.sum_eq_single (Function.update s i true)]
                · simp [hupd]
                · intro x _ hx; simp [hx]
                · simp
              · simp only [if_neg hq]
                rw [Finset.sum_eq_single s]
                · simp
                · intro x _ hx; simp [hx]
                · simp
            · have hIoc : Finset.Ioc ℓ m = (Finset.range (m+1)).filter (fun q => ℓ < q) := by
                ext q; simp; omega
              rw [hIoc, Finset.sum_filter, Finset.sum_range_succ']
              rw [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
              simp only [Nat.not_lt_zero, if_false, add_zero, lt_irrefl, and_false, zero_mul]
              simp only [dite_eq_ite, ite_self, add_zero]
              apply Finset.sum_congr rfl; intro x hx; rw [Finset.mem_range] at hx
              rw [dif_pos (show x < m + 1 by omega)]
              simp only [nextStock, buys, hx, and_true, true_and]
              have h0 : 0 < inventory s := hsi
              by_cases hlx : ℓ < x + 1
              · simp only [hlx, if_true]; by_cases hrv : r (x+1) ≤ r v <;> simp [hrv, h0]
              · simp [hlx]
          · simp only [if_neg hc]
            simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
            rw [Finset.sum_eq_single (Fin.last m)]
            · simp [reject, nextStock, buys]
            · intro p _ hp; simp only [reject]; rw [if_neg]; · simp
              intro h; exact hp (Fin.ext (by simp [h]))
            · simp
        have part2 : ∀ t, t ≤ V.length → ∀ b : ℕ,
            fixedStock r k (primeKernel r sel V) V t b = a1Stock r sel (V.take t) b := by
          intro t
          induction t with
          | zero =>
            intro _ b
            simp only [fixedStock, List.take_zero]
            unfold a1Stock soldLaw
            simp only [List.reverse_nil, soldLawRev, ite_mul, one_mul, zero_mul]
            rw [Finset.sum_ite_eq']
            have : inventory (fun _ : Fin k => false) = k := by simp [inventory]
            simp only [Finset.mem_univ, if_true, this, eq_comm]
          | succ n ih =>
            intro hn b
            rw [fixedStock]
            have hv : V.take (n+1) = V.take n ++ [valIdx V (n+1)] := by
              unfold valIdx
              rw [List.take_add_one]
              simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show n < V.length by omega)]
            rw [hv, hII]
            apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro p _
            rw [ih (by omega) a.val]
            have := hI (n+1) a.val p
            simp only [Nat.add_sub_cancel] at this
            rw [this]
        refine ⟨?_, fun t ht a => part2 t ht a.val⟩
        intro t ht1 ht a hpos p
        have h2 := part2 (t-1) (by omega) a.val
        unfold fixedConditional
        rw [mul_div_right_comm, div_self hpos.ne', one_mul]
        exact hP1 t a.val p (by rw [← h2]; exact hpos.ne')
