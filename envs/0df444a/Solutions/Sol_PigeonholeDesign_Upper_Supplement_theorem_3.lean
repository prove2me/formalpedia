-- Prove2me | solution 1 for PigeonholeDesign.Upper.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:35:09.378678+00:00
-- url     : https://prove2.me/submissions/50e07a4e-76bc-41bc-8910-722ba540ddea

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting
import Definitions.Def_PigeonholeDesign_Upper_Supplement_MatchedPair

open PigeonholeDesign
open PigeonholeDesign.Upper
open PigeonholeDesign.Upper.Supplement

theorem solution (q : ℕ) (hq : 1 ≤ q) (S : Fin q → Finset ℝ) (hS : ∀ i, (S i : Set ℝ) ⊆ Set.Icc 0 1)
    (hne : ∀ i, (S i).Nonempty)
    (h2 : ∃ i, 2 ≤ (S i).card) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      (∀ x : Fin T → MultiDim.Cov q 0, MultiDim.Admissible S x →
          PigeonholeDesign.Upper.phdExp (MultiDim.gridHole (q := q) (p := 0) 1) x ≤ C) ∧
      (∃ x : Fin T → MultiDim.Cov q 0, MultiDim.Admissible S x ∧
          c ≤ PigeonholeDesign.Upper.phdExp (MultiDim.gridHole (q := q) (p := 0) 1) x) := by
            classical
            -- the design, as a function
            have main : ∀ (ι : Type) [DecidableEq ι] (T : ℕ) (cell : ℕ → ι) (coin : ℕ → Bool)
                (Cs : Finset ι), Even T → (∀ n < T, cell n ∈ Cs) →
                ∃ v : ℕ → Bool, (∀ n, PigeonholeDesign.Upper.prefixAssign T cell coin n
                    = (List.range n).map v) ∧
                  ((Finset.range T).filter (fun t => v t = false)).card = T / 2 ∧
                  ((Finset.range T).filter (fun t => v t = true)).card = T / 2 ∧
                  ∀ s, |(((Finset.range T).filter (fun t => cell t = s ∧ v t = false)).card : ℤ)
                    - ((Finset.range T).filter (fun t => cell t = s ∧ v t = true)).card| ≤ 1 + Cs.card := by
              intro ι _ T cell coin Cs hT hCs
              have hlen : ∀ n, (PigeonholeDesign.Upper.prefixAssign T cell coin n).length = n := by
                intro n
                induction n with
                | zero => simp [PigeonholeDesign.Upper.prefixAssign]
                | succ n ih => simp [PigeonholeDesign.Upper.prefixAssign, ih]
              obtain ⟨v, hv⟩ : ∃ v : ℕ → Bool, v = fun t =>
                (PigeonholeDesign.Upper.prefixAssign T cell coin (t+1)).getD t false := ⟨_, rfl⟩
              have hmap : ∀ n, PigeonholeDesign.Upper.prefixAssign T cell coin n
                    = (List.range n).map v := by
                intro n
                induction n with
                | zero => simp [PigeonholeDesign.Upper.prefixAssign]
                | succ n ih =>
                  rw [List.range_succ, List.map_append, ← ih]
                  have h1 : v n = (PigeonholeDesign.Upper.prefixAssign T cell coin (n+1)).getD n false := by
                    rw [hv]
                  simp only [PigeonholeDesign.Upper.prefixAssign] at h1 ⊢
                  rw [List.getD_append_right _ _ _ _ (by rw [hlen])] at h1
                  simp only [hlen, Nat.sub_self, List.getD_cons_zero] at h1
                  simp only [List.map_cons, List.map_nil, h1]
              have hcnt : ∀ n (b : Bool), ((List.range n).map v).count b
                  = ((Finset.range n).filter (fun t => v t = b)).card := by
                intro n b
                induction n with
                | zero => simp
                | succ n ih =>
                  rw [List.range_succ, List.map_append, List.count_append, ih, Finset.range_add_one,
                    Finset.filter_insert]
                  by_cases h : v n = b <;> simp [h]
              have hcnt2 : ∀ n (c : ι) (b : Bool), ((List.range n).zip ((List.range n).map v)).countP
                    (fun sb => cell sb.1 = c ∧ sb.2 = b)
                  = ((Finset.range n).filter (fun t => cell t = c ∧ v t = b)).card := by
                intro n c b
                induction n with
                | zero => simp
                | succ n ih =>
                  rw [List.range_succ, List.map_append, List.zip_append (by simp), List.countP_append, ih,
                    Finset.range_add_one, Finset.filter_insert]
                  by_cases h : cell n = c ∧ v n = b <;> simp [h]
              obtain ⟨a, ha⟩ : ∃ a : ℕ → ℕ, ∀ n, a n = ((Finset.range n).filter (fun t => v t = false)).card :=
                ⟨_, fun _ => rfl⟩
              obtain ⟨b, hb⟩ : ∃ b : ℕ → ℕ, ∀ n, b n = ((Finset.range n).filter (fun t => v t = true)).card :=
                ⟨_, fun _ => rfl⟩
              obtain ⟨A, hA⟩ : ∃ A : ℕ → ι → ℕ, ∀ n s, A n s =
                ((Finset.range n).filter (fun t => cell t = s ∧ v t = false)).card := ⟨_, fun _ _ => rfl⟩
              obtain ⟨B, hB⟩ : ∃ B : ℕ → ι → ℕ, ∀ n s, B n s =
                ((Finset.range n).filter (fun t => cell t = s ∧ v t = true)).card := ⟨_, fun _ _ => rfl⟩
              have hrec : ∀ n, v n = if a n = T / 2 then true else if b n = T / 2 then false
                  else if A n (cell n) < B n (cell n) then false
                  else if B n (cell n) < A n (cell n) then true else coin n := by
                intro n
                have h1 : v n = (PigeonholeDesign.Upper.prefixAssign T cell coin (n+1)).getD n false := by
                    rw [hv]
                simp only [PigeonholeDesign.Upper.prefixAssign] at h1
                rw [List.getD_append_right _ _ _ _ (by rw [hlen])] at h1
                simp only [hlen, Nat.sub_self, List.getD_cons_zero] at h1
                rw [h1]
                simp only [hmap, hcnt, hcnt2, ha, hb, hA, hB]
              have ha1 : ∀ n, a (n+1) = a n + if v n = false then 1 else 0 := by
                intro n
                rw [ha, ha, Finset.range_add_one, Finset.filter_insert]
                by_cases h : v n = false <;> simp [h]
              have hb1 : ∀ n, b (n+1) = b n + if v n = true then 1 else 0 := by
                intro n
                rw [hb, hb, Finset.range_add_one, Finset.filter_insert]
                by_cases h : v n = true <;> simp [h]
              have hA1 : ∀ n s, A (n+1) s = A n s + if cell n = s ∧ v n = false then 1 else 0 := by
                intro n s
                rw [hA, hA, Finset.range_add_one, Finset.filter_insert]
                by_cases h : cell n = s ∧ v n = false <;> simp [h]
              have hB1 : ∀ n s, B (n+1) s = B n s + if cell n = s ∧ v n = true then 1 else 0 := by
                intro n s
                rw [hB, hB, Finset.range_add_one, Finset.filter_insert]
                by_cases h : cell n = s ∧ v n = true <;> simp [h]
              have hab : ∀ n, a n + b n = n := by
                intro n
                induction n with
                | zero => simp [ha, hb]
                | succ n ih =>
                  rw [ha1, hb1]
                  cases h : v n <;> simp <;> omega
              have hasum : ∀ n ≤ T, a n = ∑ s ∈ Cs, A n s := by
                intro n hn
                rw [ha, Finset.card_eq_sum_card_fiberwise (f := cell) (t := Cs)]
                · refine Finset.sum_congr rfl fun s _ => ?_
                  rw [hA, Finset.filter_filter]
                  congr 1
                  ext t; simp [and_comm]
                · intro t ht
                  simp at ht
                  exact hCs t (by omega)
              have hbsum : ∀ n ≤ T, b n = ∑ s ∈ Cs, B n s := by
                intro n hn
                rw [hb, Finset.card_eq_sum_card_fiberwise (f := cell) (t := Cs)]
                · refine Finset.sum_congr rfl fun s _ => ?_
                  rw [hB, Finset.filter_filter]
                  congr 1
                  ext t; simp [and_comm]
                · intro t ht
                  simp at ht
                  exact hCs t (by omega)
              obtain ⟨m, hm⟩ := hT
              have hm2 : T / 2 = m := by omega
              rw [hm2] at hrec
              have hinv : ∀ n ≤ T, a n ≤ m ∧ b n ≤ m ∧
                  ((∀ s, |(A n s : ℤ) - B n s| ≤ 1) ∨
                   (a n = m ∧ ∀ s, |(A n s : ℤ) - B n s| ≤ 1 + ((b n : ℤ) - (m - Cs.card))) ∨
                   (b n = m ∧ ∀ s, |(A n s : ℤ) - B n s| ≤ 1 + ((a n : ℤ) - (m - Cs.card)))) := by
                intro n
                induction n with
                | zero =>
                  intro _
                  have h1 : a 0 = 0 := by simp [ha]
                  have h2 : b 0 = 0 := by simp [hb]
                  refine ⟨by omega, by omega, Or.inl ?_⟩
                  intro s
                  simp [hA, hB]
                | succ n ih =>
                  intro hn
                  obtain ⟨i1, i2, i3⟩ := ih (by omega)
                  have hn1 := hab n
                  have hclose : (∀ s, |(A n s : ℤ) - B n s| ≤ 1) → |(a n : ℤ) - b n| ≤ Cs.card := by
                    intro h
                    rw [hasum n (by omega), hbsum n (by omega)]
                    push_cast
                    rw [← Finset.sum_sub_distrib]
                    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
                    refine (Finset.sum_le_sum (fun s _ => h s)).trans ?_
                    simp
                  have hr := hrec n
                  by_cases c1 : a n = m
                  · have hvn : v n = true := by rw [hr, if_pos c1]
                    have hblt : b n < m := by omega
                    have e1 : a (n+1) = a n := by rw [ha1]; simp [hvn]
                    have e2 : b (n+1) = b n + 1 := by rw [hb1]; simp [hvn]
                    refine ⟨by omega, by omega, Or.inr (Or.inl ⟨by omega, ?_⟩)⟩
                    have key : ∀ s, |(A n s : ℤ) - B n s| ≤ 1 + ((b n : ℤ) - (m - Cs.card)) := by
                      rcases i3 with h | h | h
                      · have := abs_le.1 (hclose h)
                        intro s
                        have := h s
                        omega
                      · exact h.2
                      · omega
                    intro s
                    have hk := abs_le.1 (key s)
                    have hA' := hA1 n s
                    have hB' := hB1 n s
                    rw [abs_le]
                    simp only [hvn] at hA' hB'
                    by_cases hc : cell n = s <;> simp [hc] at hA' hB' <;> omega
                  · by_cases c2 : b n = m
                    · have hvn : v n = false := by rw [hr, if_neg c1, if_pos c2]
                      have hblt : a n < m := by omega
                      have e1 : a (n+1) = a n + 1 := by rw [ha1]; simp [hvn]
                      have e2 : b (n+1) = b n := by rw [hb1]; simp [hvn]
                      refine ⟨by omega, by omega, Or.inr (Or.inr ⟨by omega, ?_⟩)⟩
                      have key : ∀ s, |(A n s : ℤ) - B n s| ≤ 1 + ((a n : ℤ) - (m - Cs.card)) := by
                        rcases i3 with h | h | h
                        · have := abs_le.1 (hclose h)
                          intro s
                          have := h s
                          omega
                        · omega
                        · exact h.2
                      intro s
                      have hk := abs_le.1 (key s)
                      have hA' := hA1 n s
                      have hB' := hB1 n s
                      rw [abs_le]
                      simp only [hvn] at hA' hB'
                      by_cases hc : cell n = s <;> simp [hc] at hA' hB' <;> omega
                    · rw [if_neg c1, if_neg c2] at hr
                      have h0 : ∀ s, |(A n s : ℤ) - B n s| ≤ 1 := by
                        rcases i3 with h | h | h
                        · exact h
                        · omega
                        · omega
                      have e1 := ha1 n
                      have e2 := hb1 n
                      refine ⟨by split_ifs at e1 <;> omega, by split_ifs at e2 <;> omega, Or.inl ?_⟩
                      intro s
                      have hk := abs_le.1 (h0 s)
                      have hA' := hA1 n s
                      have hB' := hB1 n s
                      rw [abs_le]
                      by_cases hc : cell n = s
                      · rw [hc] at hr
                        cases hvn : v n <;> simp [hc, hvn] at hA' hB' <;> rw [hvn] at hr <;>
                          split_ifs at hr <;> omega
                      · simp [hc] at hA' hB'
                        omega
              obtain ⟨f1, f2, f3⟩ := hinv T le_rfl
              have f4 := hab T
              refine ⟨v, hmap, by rw [← ha]; omega, by rw [← hb]; omega, ?_⟩
              intro s
              rw [← hA, ← hB]
              rcases f3 with h | h | h
              · have := h s; omega
              · have := h.2 s; omega
              · have := h.2 s; omega
            -- matching lemma
            have matching : ∀ (α β ι : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
                [DecidableEq ι] (f : α → ι) (g : β → ι) (Cs : Finset ι) (N : ℕ),
                Nonempty (α ≃ β) → (∀ a, f a ∈ Cs) →
                (∀ s, (Finset.univ.filter (fun a => f a = s)).card
                  ≤ (Finset.univ.filter (fun b => g b = s)).card + N) →
                ∃ e : α ≃ β, (Finset.univ.filter (fun a => f a ≠ g (e a))).card ≤ Cs.card * N := by
              intro α β ι _ _ _ _ _ f g Cs N hE hf hN
              obtain ⟨e, he⟩ := Finite.exists_min
                (fun e : α ≃ β => (Finset.univ.filter (fun a => f a ≠ g (e a))).card)
              refine ⟨e, ?_⟩
              have hswap : ∀ a a', f a ≠ g (e a) → f a' ≠ g (e a') → f a ≠ g (e a') := by
                intro a a' h h' heq
                have hne' : a ≠ a' := by rintro rfl; exact h heq
                obtain ⟨e', he'⟩ : ∃ e' : α ≃ β, ∀ t, e' t = e (Equiv.swap a a' t) :=
                  ⟨(Equiv.swap a a').trans e, fun _ => rfl⟩
                have := he e'
                refine absurd this (not_le.2 (Finset.card_lt_card ?_))
                refine (Finset.ssubset_iff_of_subset ?_).2 ⟨a, by simp [h], by
                  rw [Finset.mem_filter, he', Equiv.swap_apply_left]; exact fun hh => hh.2 heq⟩
                intro t ht
                rw [Finset.mem_filter, he'] at ht
                rw [Finset.mem_filter]
                refine ⟨Finset.mem_univ _, ?_⟩
                replace ht := ht.2
                by_cases h1 : t = a
                · subst h1; exact h
                · by_cases h2 : t = a'
                  · subst h2; exact h'
                  · rwa [Equiv.swap_apply_of_ne_of_ne h1 h2] at ht
              rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := Cs) (fun a _ => hf a), ← smul_eq_mul]
              refine Finset.sum_le_card_nsmul _ _ _ fun s _ => ?_
              rw [Finset.filter_filter]
              rcases Finset.eq_empty_or_nonempty
                (Finset.univ.filter (fun a => f a ≠ g (e a) ∧ f a = s)) with h | ⟨a, has⟩
              · rw [h]; simp
              · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at has
                have hb : (Finset.univ.filter (fun b => g b = s)).card
                    ≤ (Finset.univ.filter (fun a => f a = g (e a) ∧ f a = s)).card := by
                  refine Finset.card_le_card_of_injOn e.symm ?_ e.symm.injective.injOn
                  intro b hb
                  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
                  rw [Equiv.apply_symm_apply, hb, and_self]
                  by_contra hc
                  refine hswap a (e.symm b) has.1 ?_ ?_
                  · rw [Equiv.apply_symm_apply, hb]; exact hc
                  · rw [Equiv.apply_symm_apply, hb]; exact has.2
                have hs := hN s
                have hsplit : (Finset.univ.filter (fun a => f a = s)).card
                    = (Finset.univ.filter (fun a => f a = g (e a) ∧ f a = s)).card
                    + (Finset.univ.filter (fun a => f a ≠ g (e a) ∧ f a = s)).card := by
                  rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun a => f a = s))
                    (fun a => f a = g (e a)), Finset.filter_filter, Finset.filter_filter]
                  congr 2 <;> ext t <;> simp [and_comm]
                omega
            -- transfer of cards
            have hfin : ∀ (T : ℕ) (P : ℕ → Prop) [DecidablePred P],
                ((Finset.univ : Finset (Fin T)).filter (fun t : Fin T => P t)).card
                  = ((Finset.range T).filter P).card := by
              intro T P _
              rw [Finset.card_filter, Finset.card_filter, Finset.sum_range]
            obtain ⟨ιC, hιC⟩ : ∃ D : Finset (Option ((Fin q → ℝ) × (Fin 0 → ℕ))),
                D = (Fintype.piFinset S).image (fun f => some (f, fun i => i.elim0)) := ⟨_, rfl⟩
            have hgrid : ∀ z z' : MultiDim.Cov q 0, MultiDim.gridHole (q := q) (p := 0) 1 z
                = MultiDim.gridHole (q := q) (p := 0) 1 z' → z = z' := by
              intro z z' h
              ext i
              rcases i with i | i
              · exact congrFun (congrArg Prod.fst h) i
              · exact i.elim0
            -- structure of the assignments
            have hassign : ∀ (T : ℕ), Even T → ∀ x : Fin T → MultiDim.Cov q 0, MultiDim.Admissible S x →
                ∀ coin : Fin T → Bool, ∃ w : Fin T → Bool,
                  w = PigeonholeDesign.Upper.assign (MultiDim.gridHole (q := q) (p := 0) 1) x coin ∧
                  Nonempty ({t // w t = false} ≃ {t // w t = true}) ∧
                  ∃ e : {t // w t = false} ≃ {t // w t = true},
                    (Finset.univ.filter (fun a : {t // w t = false} => x a ≠ x (e a))).card
                      ≤ ιC.card * (1 + ιC.card) := by
              intro T hT x hx coin
              have hcell : ∀ n (hn : n < T), PigeonholeDesign.Upper.cellOf
                  (MultiDim.gridHole (q := q) (p := 0) 1) x n
                  = some (MultiDim.gridHole (q := q) (p := 0) 1 (x ⟨n, hn⟩)) := by
                intro n hn
                simp [PigeonholeDesign.Upper.cellOf, hn]
              have hmem : ∀ n < T, PigeonholeDesign.Upper.cellOf
                  (MultiDim.gridHole (q := q) (p := 0) 1) x n ∈ ιC := by
                intro n hn
                rw [hcell n hn, hιC, Finset.mem_image]
                refine ⟨fun i => x ⟨n, hn⟩ (Sum.inl i), ?_, ?_⟩
                · rw [Fintype.mem_piFinset]; exact fun i => hx.1 _ i
                · congr 1
                  refine Prod.ext rfl ?_
                  funext i; exact i.elim0
              obtain ⟨v, hv1, hv2, hv3, hv4⟩ := main _ T (PigeonholeDesign.Upper.cellOf
                  (MultiDim.gridHole (q := q) (p := 0) 1) x) (PigeonholeDesign.Upper.coinOf coin) ιC hT hmem
              have hw : (fun t : Fin T => v t) =
                  PigeonholeDesign.Upper.assign (MultiDim.gridHole (q := q) (p := 0) 1) x coin := by
                funext t
                simp only [PigeonholeDesign.Upper.assign]
                rw [hv1 T]
                simp [List.getD_eq_getElem?_getD]
              have hE : Nonempty ({t : Fin T // v t = false} ≃ {t : Fin T // v t = true}) := by
                rw [← Fintype.card_eq, Fintype.card_subtype, Fintype.card_subtype,
                  hfin T (fun t => v t = false), hfin T (fun t => v t = true), hv2, hv3]
              refine ⟨fun t => v t, hw, hE, ?_⟩
              have hsub : ∀ (s : Option ((Fin q → ℝ) × (Fin 0 → ℕ))) (b : Bool),
                  (Finset.univ.filter (fun a : {t : Fin T // v t = b} => PigeonholeDesign.Upper.cellOf
                  (MultiDim.gridHole (q := q) (p := 0) 1) x a.1 = s)).card =
                  ((Finset.range T).filter (fun t => PigeonholeDesign.Upper.cellOf
                  (MultiDim.gridHole (q := q) (p := 0) 1) x t = s ∧ v t = b)).card := by
                intro s b
                rw [← hfin T (fun t => PigeonholeDesign.Upper.cellOf
                  (MultiDim.gridHole (q := q) (p := 0) 1) x t = s ∧ v t = b)]
                refine Finset.card_bij (fun a _ => a.1) ?_ ?_ ?_
                · intro a ha
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
                  exact ⟨ha, a.2⟩
                · intro a _ b _ h
                  exact Subtype.ext h
                · intro t ht
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
                  exact ⟨⟨t, ht.2⟩, by simpa using ht.1, rfl⟩
              obtain ⟨e, he⟩ := matching {t : Fin T // v t = false} {t : Fin T // v t = true} _
                (fun a => PigeonholeDesign.Upper.cellOf (MultiDim.gridHole (q := q) (p := 0) 1) x a.1)
                (fun a => PigeonholeDesign.Upper.cellOf (MultiDim.gridHole (q := q) (p := 0) 1) x a.1)
                ιC (1 + ιC.card) hE (fun a => hmem _ a.1.2) (by
                  intro s
                  rw [hsub, hsub]
                  have := abs_le.1 (hv4 s)
                  omega)
              refine ⟨e, le_trans (Finset.card_le_card ?_) he⟩
              intro a ha
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
              intro h
              rw [hcell _ a.1.2, hcell _ (e a).1.2] at h
              exact ha (hgrid _ _ (Option.some.inj h))
            have hdist : ∀ z z' : MultiDim.Cov q 0, (∀ i, z (Sum.inl i) ∈ S i) → (∀ i, z' (Sum.inl i) ∈ S i) →
                dist z z' ≤ Real.sqrt q := by
              intro z z' hz hz'
              rw [EuclideanSpace.dist_eq]
              refine Real.sqrt_le_sqrt ?_
              rw [Fintype.sum_sum_type]
              simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
              have : ∀ i ∈ (Finset.univ : Finset (Fin q)), dist (z (Sum.inl i)) (z' (Sum.inl i)) ^ 2 ≤ (1:ℝ) := by
                intro i _
                have h1 := hS i (hz i)
                have h2 := hS i (hz' i)
                rw [Real.dist_eq, sq_abs]
                have := h1.1; have := h1.2; have := h2.1; have := h2.2
                nlinarith
              refine (Finset.sum_le_sum this).trans ?_
              simp
            obtain ⟨i0, hi0⟩ := h2
            obtain ⟨y, hy, y', hy', hyy⟩ := Finset.one_lt_card.1 (by omega : 1 < (S i0).card)
            choose base hbase using hne
            obtain ⟨pt, hpt⟩ : ∃ pt : ℝ → MultiDim.Cov q 0, ∀ r i, pt r (Sum.inl i)
                = Function.update base i0 r i :=
              ⟨fun r => WithLp.toLp 2 (Sum.elim (Function.update base i0 r) (fun i => i.elim0)),
                fun r i => by simp⟩
            have hptS : ∀ r ∈ S i0, ∀ i, pt r (Sum.inl i) ∈ S i := by
              intro r hr i
              rw [hpt]
              by_cases h : i = i0
              · subst h; simpa using hr
              · rw [Function.update_of_ne h]; exact hbase i
            have hd : 0 < dist (pt y) (pt y') := by
              rw [dist_pos]
              intro h
              have : pt y (Sum.inl i0) = pt y' (Sum.inl i0) := by rw [h]
              rw [hpt, hpt] at this
              simp at this
              exact hyy this
            refine ⟨dist (pt y) (pt y'), ((ιC.card * (1 + ιC.card) : ℕ) : ℝ) * Real.sqrt q + 1, hd,
              by positivity, 2, ?_⟩
            intro T hT2 hT
            have hcard : ((Finset.univ : Finset (Fin T → Bool)).card : ℝ) = 2 ^ T := by
              simp
            constructor
            · intro x hx
              unfold PigeonholeDesign.Upper.phdExp
              rw [div_le_iff₀ (by positivity), mul_comm, ← hcard, ← nsmul_eq_mul]
              refine Finset.sum_le_card_nsmul _ _ _ fun coin _ => ?_
              obtain ⟨w, hw, -, e, he⟩ := hassign T hT x hx coin
              rw [← hw]
              unfold PigeonholeDesign.Upper.discrepancy
              refine (ciInf_le (Set.finite_range _).bddBelow e).trans ?_
              have h1 : ∀ a ∈ (Finset.univ : Finset {t // w t = false}), dist (x a) (x (e a))
                  ≤ if x a ≠ x (e a) then Real.sqrt q else 0 := by
                intro a _
                split_ifs with h
                · exact hdist _ _ (fun i => hx.1 _ i) (fun i => hx.1 _ i)
                · simp only [ne_eq, not_not] at h
                  rw [h, dist_self]
              refine (Finset.sum_le_sum h1).trans ?_
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
              have h2 : ((Finset.univ.filter (fun a : {t // w t = false} => x a ≠ x (e a))).card : ℝ)
                      ≤ ((ιC.card * (1 + ιC.card) : ℕ) : ℝ) := by exact_mod_cast he
              have := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg (q:ℝ))
              linarith
            · obtain ⟨x, hxdef⟩ : ∃ x : Fin T → MultiDim.Cov q 0, x = fun t : Fin T =>
                if (t : ℕ) = 0 then pt y else pt y' := ⟨_, rfl⟩
              have hx : MultiDim.Admissible S x := by
                refine ⟨fun t i => ?_, fun t j => j.elim0⟩
                rw [hxdef]
                dsimp only
                split_ifs
                · exact hptS y hy i
                · exact hptS y' hy' i
              refine ⟨x, hx, ?_⟩
              unfold PigeonholeDesign.Upper.phdExp
              rw [le_div_iff₀ (by positivity), mul_comm, ← hcard, ← nsmul_eq_mul]
              refine Finset.card_nsmul_le_sum _ _ _ fun coin _ => ?_
              obtain ⟨w, hw, hE, -⟩ := hassign T hT x hx coin
              rw [← hw]
              unfold PigeonholeDesign.Upper.discrepancy
              refine le_ciInf fun e => ?_
              have hx0 : ∀ t : Fin T, (t:ℕ) = 0 → x t = pt y := by
                intro t ht; rw [hxdef]; simp [ht]
              have hx1 : ∀ t : Fin T, (t:ℕ) ≠ 0 → x t = pt y' := by
                intro t ht; rw [hxdef]; simp [ht]
              obtain ⟨a, ha⟩ : ∃ a : {t // w t = false}, dist (pt y) (pt y') ≤ dist (x a) (x (e a)) := by
                cases hw0 : w ⟨0, by omega⟩
                · refine ⟨⟨_, hw0⟩, ?_⟩
                  rw [hx0 _ rfl, hx1]
                  intro h
                  have h3 := (e ⟨_, hw0⟩).2
                  rw [show (e ⟨_, hw0⟩).1 = ⟨0, by omega⟩ from Fin.ext h, hw0] at h3
                  exact absurd h3 (by simp)
                · refine ⟨e.symm ⟨_, hw0⟩, ?_⟩
                  rw [Equiv.apply_symm_apply, hx0 ⟨0, by omega⟩ rfl, hx1, dist_comm]
                  intro h
                  have h3 := (e.symm ⟨_, hw0⟩).2
                  rw [show (e.symm ⟨_, hw0⟩).1 = ⟨0, by omega⟩ from Fin.ext h, hw0] at h3
                  exact absurd h3 (by simp)
              exact ha.trans (Finset.single_le_sum
                (f := fun a : {t // w t = false} => dist (x a) (x (e a)))
                (fun _ _ => dist_nonneg) (Finset.mem_univ a))
