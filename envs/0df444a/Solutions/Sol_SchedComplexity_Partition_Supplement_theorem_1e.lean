-- Prove2me | solution 1 for SchedComplexity.Partition.Supplement.theorem_1e
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:38:20.667409+00:00
-- url     : https://prove2.me/submissions/11c1f2b0-0319-4dca-8719-12a5cfb0a460

import Mathlib
import Definitions.Def_SchedComplexity_Partition_Supplement_Family

open SchedComplexity
open SchedComplexity.Partition
open SchedComplexity.Partition.Supplement

open CookPvsNP ProjSchedTW.Complexity

theorem solution :
    PolyReducible (language (.fixed 3) .flow ∅ .cmax)
      (language (.fixed 3) .permutation ∅ .cmax) ∧
    PolyReducible (language (.fixed 3) .permutation ∅ .cmax)
      (language (.fixed 3) .flow ∅ .cmax) := by
        have hid : PolyTimeComputable (fun x : List BSym => x) := by
          let M : TM BSym :=
            { Q := Bool, q₀ := true, qaccept := true, qreject := false,
              accept_ne_reject := by decide, δ := fun q _ => (q, none, Move.right) }
          refine ⟨BSym, inferInstance, Function.Embedding.refl _, Function.Embedding.refl _, M, 0, ?_⟩
          intro x
          have hfix : ∀ k, M.run k (M.init (x.map (Function.Embedding.refl BSym))) =
              M.init (x.map (Function.Embedding.refl BSym)) := by
            intro k
            induction k with
            | zero => rfl
            | succ k ih =>
              rw [TM.run, Function.iterate_succ_apply', ← TM.run, ih]
              unfold TM.step
              rw [if_pos (show M.IsHalting _ from Or.inl rfl)]
          refine ⟨?_, ?_⟩
          · unfold TM.HaltsWithin; rw [hfix]; exact Or.inl rfl
          · rw [hfix]
            cases x with
            | nil => rfl
            | cons a t =>
              have : ∀ l : List BSym, ((l.map some).reverse.dropWhile Option.isNone) = (l.map some).reverse := by
                intro l
                rw [← List.map_reverse]
                cases l.reverse with
                | nil => rfl
                | cons b u => simp
              have h2 := this (a :: t)
              simp only [List.map_cons] at h2
              have e1 : ∀ l : List BSym, l.map (Function.Embedding.refl BSym) = l := fun l => by
                induction l with
                | nil => rfl
                | cons b u ih => simp only [List.map_cons, ih]; rfl
              have e2 : ∀ l : List BSym, l.map (some ∘ Function.Embedding.refl BSym) = l.map some := fun l => by
                induction l with
                | nil => rfl
                | cons b u ih => simp only [List.map_cons, ih]; rfl
              simp only [TM.output, TM.init, List.map_cons, List.headD_cons, List.tail_cons, e1, e2]
              show (List.dropWhile Option.isNone (some a :: List.map some t).reverse).reverse =
                some a :: List.map some t
              rw [h2]
              simp
        have core : ∀ (n : ℕ) (Q : SchedComplexity.Shops.ShopInstance n 3),
            (∀ j, (Q.ops j).map Prod.fst = List.ofFn (fun i : Fin 3 => i)) →
            (∀ j, Q.release j = 0) → Q.prec = ∅ →
            ∀ (S : Q.Op → ℕ) (y : ℕ), Q.IsFeasible S → (∀ j, Q.completion S j ≤ y) →
            ∃ S' : Q.Op → ℕ, Q.IsFeasible S' ∧ CommonOrder Q S' ∧ ∀ j, Q.completion S' j ≤ y := by
          intro n Q hflow hrel hprec S y hS hy
          classical
          have hlen : ∀ j, (Q.ops j).length = 3 := fun j => by
            have := congrArg List.length (hflow j); simpa using this
          have hmach : ∀ o : Q.Op, (Q.mach o).val = o.2.val := by
            intro o
            have h1 : ((Q.ops o.1).map Prod.fst)[o.2.val]'(by simp) =
                (List.ofFn (fun i : Fin 3 => i))[o.2.val]'(by simp; have := o.2.isLt; have h := hlen o.1; omega) :=
              List.getElem_of_eq (hflow o.1) _
            simp only [List.getElem_map, List.getElem_ofFn] at h1
            simp only [SchedComplexity.Shops.ShopInstance.mach, List.get_eq_getElem]
            rw [h1]
          obtain ⟨st, hst⟩ : ∃ st : ℕ → Fin n → ℕ, ∀ o : Q.Op, st o.2.val o.1 = S o :=
            ⟨fun r j => if h : r < (Q.ops j).length then S ⟨j, ⟨r, h⟩⟩ else 0,
              fun o => by simp [o.2.isLt]⟩
          obtain ⟨pr, hpr⟩ : ∃ pr : ℕ → Fin n → ℕ, ∀ o : Q.Op, pr o.2.val o.1 = Q.proc o :=
            ⟨fun r j => if h : r < (Q.ops j).length then Q.proc ⟨j, ⟨r, h⟩⟩ else 0,
              fun o => by simp [o.2.isLt]⟩
          have mk : ∀ j (r : ℕ), r < 3 → ∃ o : Q.Op, o.1 = j ∧ o.2.val = r := fun j r hr =>
            ⟨⟨j, ⟨r, by rw [hlen]; exact hr⟩⟩, rfl, rfl⟩
          have chain : ∀ j (r : ℕ), r < 2 → st r j + pr r j ≤ st (r+1) j := by
            intro j r hr
            have := hS.2.1 j ⟨r, by rw [hlen]; omega⟩ ⟨r+1, by rw [hlen]; omega⟩ rfl
            rw [← hst, ← hst, ← hpr] at this
            exact this
          have disj : ∀ (r : ℕ), r < 3 → ∀ j k, j ≠ k →
              st r j + pr r j ≤ st r k ∨ st r k + pr r k ≤ st r j := by
            intro r hr j k hjk
            have := hS.2.2.1 ⟨j, ⟨r, by rw [hlen]; omega⟩⟩ ⟨k, ⟨r, by rw [hlen]; omega⟩⟩
              (fun h => hjk (congrArg Sigma.fst h)) (Fin.ext (by rw [hmach, hmach]))
            rw [← hst, ← hst, ← hpr, ← hpr] at this
            exact this
          have bound : ∀ j, st 2 j + pr 2 j ≤ y := by
            intro j
            have := Finset.le_sup (f := fun r : Fin (Q.ops j).length => S ⟨j, r⟩ + Q.proc ⟨j, r⟩)
              (Finset.mem_univ ⟨2, by rw [hlen]; omega⟩)
            have h2 := hy j
            unfold SchedComplexity.Shops.ShopInstance.completion at h2
            rw [← hst, ← hpr] at this
            exact le_trans this h2
          have c0 : ∀ j, st 0 j + pr 0 j ≤ st 1 j := fun j => chain j 0 (by norm_num)
          have c1 : ∀ j, st 1 j + pr 1 j ≤ st 2 j := fun j => chain j 1 (by norm_num)
          -- interval packing lemma
          have interval : ∀ (A : Finset (Fin n)) (s p : Fin n → ℕ) (L R : ℕ),
              (∀ l ∈ A, L ≤ s l ∧ s l + p l ≤ R) →
              (∀ l ∈ A, ∀ l' ∈ A, l ≠ l' → s l + p l ≤ s l' ∨ s l' + p l' ≤ s l) →
              ∑ l ∈ A, p l ≤ R - L := by
            intro A s p L R hA hd
            have h1 : ∑ l ∈ A, p l = (A.biUnion fun l => Finset.Ico (s l) (s l + p l)).card := by
              rw [Finset.card_biUnion]
              · simp
              · intro a ha b hb hab
                rw [Function.onFun, Finset.disjoint_left]
                intro x hx hx'
                simp only [Finset.mem_Ico] at hx hx'
                rcases hd a ha b hb hab with h | h <;> omega
            rw [h1, ← Nat.card_Ico L R]
            apply Finset.card_le_card
            intro x hx
            simp only [Finset.mem_biUnion, Finset.mem_Ico] at hx ⊢
            obtain ⟨l, hl, h1, h2⟩ := hx
            have := hA l hl
            omega
          -- the order on jobs
          obtain ⟨lt, hirr, htrans, htri, hF1⟩ : ∃ lt : Fin n → Fin n → Prop,
              (∀ j, ¬ lt j j) ∧ (∀ a b c, lt a b → lt b c → lt a c) ∧
              (∀ a b, a ≠ b → lt a b ∨ lt b a) ∧ (∀ a b, lt a b → st 1 a + pr 1 a ≤ st 1 b) := by
            refine ⟨fun j k => st 1 j < st 1 k ∨ (st 1 j = st 1 k ∧
              (st 1 j + pr 1 j < st 1 k + pr 1 k ∨
                (st 1 j + pr 1 j = st 1 k + pr 1 k ∧ j.val < k.val))), ?_, ?_, ?_, ?_⟩
            · intro j; omega
            · intro a b c; omega
            · intro a b hab
              have : a.val ≠ b.val := fun h => hab (Fin.ext h)
              omega
            · intro a b hab
              have hne : a ≠ b := by rintro rfl; omega
              have := disj 1 (by norm_num) a b hne
              omega
          -- the permutation
          obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin n), ∀ a b : Fin n, a < b → lt (π a) (π b) := by
            let rk : Fin n → ℕ := fun j => (Finset.univ.filter (fun l => lt l j)).card
            have rk_lt : ∀ j, rk j < n := by
              intro j
              have : (Finset.univ.filter (fun l => lt l j)) ⊂ Finset.univ :=
                Finset.filter_ssubset.mpr ⟨j, Finset.mem_univ _, hirr j⟩
              have := Finset.card_lt_card this
              simpa [rk] using this
            have rk_mono : ∀ a b, lt a b → rk a < rk b := by
              intro a b hab
              apply Finset.card_lt_card
              have hsub : (Finset.univ.filter (fun l => lt l a)) ⊆ (Finset.univ.filter (fun l => lt l b)) := by
                intro x hx
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
                exact htrans _ _ _ hx hab
              rw [Finset.ssubset_iff_of_subset hsub]
              exact ⟨a, by simp [hab], by simp [hirr a]⟩
            let f : Fin n → Fin n := fun j => ⟨rk j, rk_lt j⟩
            have finj : Function.Injective f := by
              intro a b h
              by_contra hne
              have h' : rk a = rk b := congrArg Fin.val h
              rcases htri a b hne with h1 | h1
              · have := rk_mono _ _ h1; omega
              · have := rk_mono _ _ h1; omega
            let e := Equiv.ofBijective f (Finite.injective_iff_bijective.mp finj)
            refine ⟨e.symm, ?_⟩
            intro a b hab
            have ha : f (e.symm a) = a := e.apply_symm_apply a
            have hb : f (e.symm b) = b := e.apply_symm_apply b
            by_cases hj : e.symm a = e.symm b
            · rw [hj] at ha; rw [ha] at hb; exact absurd hb (ne_of_lt hab)
            · rcases htri _ _ hj with h1 | h1
              · exact h1
              · have := rk_mono _ _ h1
                have h3 : (f (e.symm b)).val < (f (e.symm a)).val := this
                rw [ha, hb] at h3
                exact absurd hab (not_lt.mpr (le_of_lt h3))
          -- the new schedule
          let A0 : Fin n → ℕ := fun j => ∑ l ∈ Finset.univ.filter (fun l => lt l j), pr 0 l
          let B2 : Fin n → ℕ := fun j => ∑ l ∈ Finset.univ.filter (fun l => lt j l), pr 2 l
          have hA0ins : ∀ j, A0 j + pr 0 j = ∑ l ∈ insert j (Finset.univ.filter (fun l => lt l j)), pr 0 l := by
            intro j
            rw [Finset.sum_insert (by simp [hirr j])]
            ring
          have hB2ins : ∀ j, pr 2 j + B2 j = ∑ l ∈ insert j (Finset.univ.filter (fun l => lt j l)), pr 2 l := by
            intro j
            rw [Finset.sum_insert (by simp [hirr j])]
          have F0 : ∀ j, A0 j + pr 0 j ≤ st 1 j := by
            intro j
            rw [hA0ins]
            have := interval (insert j (Finset.univ.filter (fun l => lt l j))) (st 0) (pr 0) 0 (st 1 j) ?_ ?_
            · omega
            · intro l hl
              simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hl
              rcases hl with rfl | hl
              · exact ⟨Nat.zero_le _, c0 l⟩
              · have := c0 l
                have := hF1 l j hl
                exact ⟨Nat.zero_le _, by omega⟩
            · intro l _ l' _ hll'
              exact disj 0 (by norm_num) l l' hll'
          have F2 : ∀ j, st 1 j + pr 1 j + (pr 2 j + B2 j) ≤ y := by
            intro j
            rw [hB2ins]
            have := interval (insert j (Finset.univ.filter (fun l => lt j l))) (st 2) (pr 2)
              (st 1 j + pr 1 j) y ?_ ?_
            · have h1 := c1 j
              have h2 := bound j
              omega
            · intro l hl
              simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hl
              rcases hl with rfl | hl
              · exact ⟨c1 l, bound l⟩
              · have := c1 l
                have := hF1 j l hl
                exact ⟨by omega, bound l⟩
            · intro l _ l' _ hll'
              exact disj 2 (by norm_num) l l' hll'
          let T : ℕ → Fin n → ℕ := fun r j => if r = 0 then A0 j else if r = 1 then st 1 j else
            y - (pr 2 j + B2 j)
          have dir : ∀ r, r < 3 → ∀ j k, lt j k → T r j + pr r j ≤ T r k := by
            intro r hr j k hjk
            rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with rfl | rfl | rfl
            · simp only [T, if_true]
              rw [hA0ins]
              apply Finset.sum_le_sum_of_subset
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
              rcases hx with rfl | hx
              · exact hjk
              · exact htrans _ _ _ hx hjk
            · simp only [T, one_ne_zero, if_false, if_true]
              exact hF1 j k hjk
            · simp only [T, OfNat.ofNat_ne_zero, if_false, OfNat.ofNat_ne_one]
              have h1 : pr 2 k + B2 k ≤ B2 j := by
                rw [hB2ins]
                apply Finset.sum_le_sum_of_subset
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
                rcases hx with rfl | hx
                · exact hjk
                · exact htrans _ _ _ hjk hx
              have h2 := F2 j
              omega
          refine ⟨fun o => T o.2.val o.1, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
          · intro o; rw [hrel]; exact Nat.zero_le _
          · intro j r r' hr'
            rw [← hpr]
            have hr3 : r'.val < 3 := by have := r'.isLt; have := hlen j; omega
            show T r.val j + pr r.val j ≤ T r'.val j
            rw [hr']
            rcases (show r.val = 0 ∨ r.val = 1 by omega) with h | h <;> rw [h]
            · show A0 j + pr 0 j ≤ st 1 j
              exact F0 j
            · show st 1 j + pr 1 j ≤ y - (pr 2 j + B2 j)
              have := F2 j
              omega
          · intro o o' hne hm
            have hr : o.2.val = o'.2.val := by rw [← hmach, ← hmach, hm]
            have hj : o.1 ≠ o'.1 := by
              intro h
              apply hne
              obtain ⟨j, r⟩ := o
              obtain ⟨k, r'⟩ := o'
              simp only at h hr
              subst h
              rw [Fin.ext hr]
            rw [← hpr, ← hpr]
            show T o.2.val o.1 + pr o.2.val o.1 ≤ T o'.2.val o'.1 ∨ T o'.2.val o'.1 + pr o'.2.val o'.1 ≤ T o.2.val o.1
            have hr3 : o.2.val < 3 := by have := o.2.isLt; have := hlen o.1; omega
            rw [← hr]
            rcases htri _ _ hj with h | h
            · exact Or.inl (dir _ hr3 _ _ h)
            · exact Or.inr (dir _ hr3 _ _ h)
          · intro j k hjk
            rw [hprec] at hjk
            simp at hjk
          · refine ⟨π, ?_⟩
            intro a b o o' hab ho ho' hm
            have hr : o.2.val = o'.2.val := by rw [← hmach, ← hmach, hm]
            rw [← hpr]
            show T o.2.val o.1 + pr o.2.val o.1 ≤ T o'.2.val o'.1
            have hr3 : o.2.val < 3 := by have := o.2.isLt; have := hlen o.1; omega
            rw [← hr]
            have := hπ a b hab
            rw [← ho, ← ho'] at this
            exact dir _ hr3 _ _ this
          · intro j
            unfold SchedComplexity.Shops.ShopInstance.completion
            apply Finset.sup_le
            intro r _
            rw [← hpr]
            show T r.val j + pr r.val j ≤ y
            have hr3 : r.val < 3 := by have := r.isLt; have := hlen j; omega
            have h0 := F0 j
            have h2 := F2 j
            rcases (show r.val = 0 ∨ r.val = 1 ∨ r.val = 2 by omega) with h | h | h <;> rw [h]
            · show A0 j + pr 0 j ≤ y
              have := c1 j; have := bound j; omega
            · show st 1 j + pr 1 j ≤ y
              omega
            · show y - (pr 2 j + B2 j) + pr 2 j ≤ y
              omega
        have fwd : ∀ x, x ∈ language (.fixed 3) .flow ∅ .cmax →
            x ∈ language (.fixed 3) .permutation ∅ .cmax := by
          rintro x ⟨hV, n, m, I, y, hm, hsh, hd, hmeet, hx⟩
          obtain ⟨-, rfl⟩ := hm
          have hflow : IsFlow I := by simpa [HasShape] using hsh
          have hd' := hd
          simp [DataRestrictions] at hd'
          obtain ⟨a, S, hF, -, -, -, hval⟩ := hmeet
          have hF2 : I.shop.IsFeasible S := hF
          have hval2 : ∀ j, I.shop.completion S j ≤ y := hval
          obtain ⟨S', hF', hCO, hval'⟩ := core n I.shop hflow hd'.1 hd'.2 S y hF2 hval2
          refine ⟨hV, n, 3, I, y, ⟨by norm_num, rfl⟩, by simpa [HasShape] using hsh, hd, ?_, hx⟩
          refine ⟨a, S', hF', fun _ => hCO, fun h => absurd h (by simp), fun h => absurd h (by simp), hval'⟩
        have bwd : ∀ x, x ∈ language (.fixed 3) .permutation ∅ .cmax →
            x ∈ language (.fixed 3) .flow ∅ .cmax := by
          rintro x ⟨hV, n, m, I, y, hm, hsh, hd, hmeet, hx⟩
          obtain ⟨-, rfl⟩ := hm
          obtain ⟨a, S, hF, -, -, -, hval⟩ := hmeet
          refine ⟨hV, n, 3, I, y, ⟨by norm_num, rfl⟩, by simpa [HasShape] using hsh, hd, ?_, hx⟩
          exact ⟨a, S, hF, fun h => absurd h (by simp), fun h => absurd h (by simp),
            fun h => absurd h (by simp), hval⟩
        exact ⟨⟨fun x => x, hid, fun x => ⟨fwd x, bwd x⟩⟩, ⟨fun x => x, hid, fun x => ⟨bwd x, fwd x⟩⟩⟩
