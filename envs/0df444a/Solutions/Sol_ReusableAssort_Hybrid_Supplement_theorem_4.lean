-- Prove2me | solution 1 for ReusableAssort.Hybrid.Supplement.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:23:43.471533+00:00
-- url     : https://prove2.me/submissions/e26d5937-ebbc-439c-9684-16e4f7de1d9b

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Supplement_HybridII

open ReusableAssort
open ReusableAssort.Hybrid
open ReusableAssort.Hybrid.Supplement

theorem solution {n T : ℕ} [NeZero n] {Z : Type} [Fintype Z] [DecidableEq Z]
    (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) (hy : LPOptimal I y) (hN : Normalized I y)
    (γ : ℝ) (hγ : IsGammaStar (cmin I : ℝ) γ)
    (tb : ℕ → (Fin n → ℕ → ℕ) → Bool) :
    (1 - min (1 / 2) (epsStar (cmin I : ℝ))) * lpObj I y ≤ expRevHybridII I y γ tb ∧
    ∀ t ∈ Finset.Icc 1 (T + 1), ∀ J, ValidStart I t J →
      max (expRev I y (alg2 γ) t J) (expRev I y (alg3 I y) t J) ≤
        expRevHybridIIFrom I y γ tb t J := by
          have hWS : ∀ (φ : Finset (Fin n) → Fin n → ℝ) (feas : Finset (Finset (Fin n))),
              (∀ S ∈ feas, ∀ i j, j ≠ i → insert j S ∈ feas → φ (insert j S) i ≤ φ S i) →
              (∀ S ∈ feas, ∀ S' ⊆ S, S' ∈ feas) →
              ∀ S ∈ feas, ∀ A ⊆ S, ∀ i ∈ A, φ S i ≤ φ A i := by
            intro φ feas h_subst h_down S hS A hAS i hi
            have key : ∀ B : Finset (Fin n), Disjoint A B → A ∪ B ⊆ S → φ (A ∪ B) i ≤ φ A i := by
              intro B
              induction B using Finset.induction_on with
              | empty => intro _ _; simp
              | insert j B hj ih =>
                intro hd hs
                rw [Finset.disjoint_insert_right] at hd
                have e : A ∪ insert j B = insert j (A ∪ B) := by
                  ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
                have hs' : A ∪ B ⊆ S := fun x hx => hs (by rw [e]; exact Finset.mem_insert_of_mem hx)
                refine le_trans ?_ (ih hd.2 hs')
                rw [e]
                apply h_subst _ (h_down S hS _ hs')
                · rintro rfl; exact hd.1 hi
                · rw [← e]; exact h_down S hS _ hs
            have := key (S \ A) Finset.disjoint_sdiff (by
              rw [Finset.union_sdiff_of_subset hAS])
            rwa [Finset.union_sdiff_of_subset hAS] at this
          have hP3 : ∀ (φ : Finset (Fin n) → Fin n → ℝ) (feas : Finset (Finset (Fin n))),
              (∀ i, φ ∅ i = 0) →
              (∀ S ∈ feas, ∀ i j, j ≠ i → insert j S ∈ feas → φ (insert j S) i ≤ φ S i) →
              (∀ S ∈ feas, ∀ S' ⊆ S, S' ∈ feas) →
              (∀ S ∈ feas, ∀ i, 0 ≤ φ S i) →
              (∀ S ∈ feas, ∀ i, i ∉ S → φ S i = 0) →
              ∀ (k : ℕ) (S : Finset (Fin n)) (p : Fin n → ℝ), S.card ≤ k → S ∈ feas →
              (∀ i ∈ S, 0 ≤ p i ∧ p i ≤ φ S i) →
              (∀ U, ¬ U ⊆ S → subAssortAux k φ S p U = 0) ∧
              (∀ U, 0 ≤ subAssortAux k φ S p U) ∧
              (∑ U, subAssortAux k φ S p U = 1) ∧
              ∀ i ∈ S, ∑ U, subAssortAux k φ S p U * φ U i = p i := by
            intro φ feas h_empty h_subst h_down h_nonneg h_supp k
            induction k with
            | zero =>
              intro S p hk hS hp
              have hS0 : S = ∅ := by rw [← Finset.card_eq_zero]; omega
              subst hS0
              simp only [subAssortAux]
              refine ⟨?_, ?_, ?_, ?_⟩
              · intro U hU
                rw [if_neg]; rintro rfl; exact hU (Finset.Subset.refl _)
              · intro U; split_ifs <;> norm_num
              · simp
              · simp
            | succ k ih =>
              intro S p hk hS hp
              by_cases hS0 : S = ∅
              · subst hS0
                simp only [subAssortAux, if_true]
                refine ⟨?_, ?_, ?_, ?_⟩
                · intro U hU
                  rw [if_neg]; rintro rfl; exact hU (Finset.Subset.refl _)
                · intro U; split_ifs <;> norm_num
                · simp
                · simp
              have hm : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS0)
              have hperm : (sortedList φ S p).Perm (S.sort (· ≤ ·)) := by
                unfold sortedList; exact List.mergeSort_perm _ _
              have hlen : (sortedList φ S p).length = S.card := by
                rw [hperm.length_eq, Finset.length_sort]
              have hnd : (sortedList φ S p).Nodup := by
                rw [hperm.nodup_iff]; exact Finset.sort_nodup _ _
              have hmem : ∀ x, x ∈ sortedList φ S p ↔ x ∈ S := by
                intro x; rw [hperm.mem_iff, Finset.mem_sort]
              have hsorted : (sortedList φ S p).Pairwise (fun a b => ratio φ S p b ≤ ratio φ S p a) := by
                have := List.pairwise_mergeSort (le := fun a b => decide (ratio φ S p b ≤ ratio φ S p a))
                  (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; linarith)
                  (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
                  (S.sort (· ≤ ·))
                unfold sortedList
                simpa using this
              have hrat : ∀ i ∈ S, 0 ≤ ratio φ S p i ∧ ratio φ S p i ≤ 1 ∧ φ S i * ratio φ S p i = p i := by
                intro i hi
                obtain ⟨h1, h2⟩ := hp i hi
                unfold ratio
                split_ifs with h
                · rw [h] at h2; refine ⟨by norm_num, le_refl _, ?_⟩; rw [h]; linarith
                · have hpos : 0 < φ S i := lt_of_le_of_ne (h_nonneg S hS i) (Ne.symm h)
                  refine ⟨div_nonneg h1 hpos.le, (div_le_one hpos).mpr h2, ?_⟩
                  field_simp
              -- the sequence of ratios
              obtain ⟨R, hR⟩ : ∃ R : ℕ → ℝ, ∀ j, R j =
                ((sortedList φ S p).map (ratio φ S p)).getD j 0 := ⟨_, fun _ => rfl⟩
              have hRe : ∀ (j : ℕ) (hj : j < (sortedList φ S p).length),
                  R j = ratio φ S p ((sortedList φ S p)[j]) := by
                intro j hj; rw [hR]; simp [List.getD, hj]
              have hR01 : ∀ j, j < S.card → 0 ≤ R j ∧ R j ≤ 1 := by
                intro j hj
                rw [hRe j (by omega)]
                have := hrat _ ((hmem _).mp (List.getElem_mem (l := sortedList φ S p) (n := j) (by omega)))
                exact ⟨this.1, this.2.1⟩
              have hRanti : ∀ j, 1 ≤ j → j < S.card → R j ≤ R (j - 1) := by
                intro j h1 hj
                rw [hRe j (by omega), hRe (j-1) (by omega)]
                exact List.pairwise_iff_getElem.mp hsorted (j-1) j (by omega) (by omega) (by omega)
              have hq0 : qprob φ S p 0 = 1 - R 0 := by simp [qprob, hR]
              have hqm : qprob φ S p S.card = R (S.card - 1) := by
                rw [hR]; unfold qprob; simp only []; rw [if_neg (by omega)]; simp
              have hqj : ∀ j ∈ Finset.Ico 1 S.card, qprob φ S p j = R (j - 1) - R j := by
                intro j hj
                rw [Finset.mem_Ico] at hj
                rw [hR, hR]; unfold qprob; simp only []; rw [if_neg (by omega), if_neg (by omega)]
              have htel : ∀ l, l < S.card →
                  ∑ j ∈ Finset.Ico (l + 1) S.card, (R (j - 1) - R j) = R l - R (S.card - 1) := by
                intro l hl
                have : ∀ N, l + 1 ≤ N → ∑ j ∈ Finset.Ico (l + 1) N, (R (j - 1) - R j) = R l - R (N - 1) := by
                  intro N hN
                  induction N, hN using Nat.le_induction with
                  | base => simp
                  | succ N hN ih2 =>
                    rw [Finset.sum_Ico_succ_top hN, ih2]; simp
                exact this _ (by omega)
              have htk : ∀ j ∈ Finset.Ico 1 S.card, ((sortedList φ S p).take j).toFinset ⊆ S := by
                intro j hj x hx
                rw [List.mem_toFinset] at hx
                exact (hmem x).mp (List.mem_of_mem_take hx)
              have hIH := fun j (hj : j ∈ Finset.Ico 1 S.card) =>
                ih ((sortedList φ S p).take j).toFinset (φ S) (by
                    have h1 := List.toFinset_card_le ((sortedList φ S p).take j)
                    rw [List.length_take] at h1
                    rw [Finset.mem_Ico] at hj; omega)
                  (h_down S hS _ (htk j hj))
                  (fun i hi => ⟨h_nonneg S hS i, hWS φ feas h_subst h_down S hS _ (htk j hj) i hi⟩)
              have hU : ∀ U, subAssortAux (k+1) φ S p U = (1 - R 0) * (if U = ∅ then 1 else 0)
                  + R (S.card - 1) * (if U = S then 1 else 0)
                  + ∑ j ∈ Finset.Ico 1 S.card, (R (j-1) - R j) *
                    subAssortAux k φ ((sortedList φ S p).take j).toFinset (φ S) U := by
                intro U
                simp only [subAssortAux, if_neg hS0]
                rw [hq0, hqm]
                congr 1
                apply Finset.sum_congr rfl
                intro j hj; rw [hqj j hj]
              refine ⟨?_, ?_, ?_, ?_⟩
              · intro U hUS
                rw [hU, if_neg (by rintro rfl; exact hUS (Finset.empty_subset _)),
                  if_neg (by rintro rfl; exact hUS (Finset.Subset.refl _))]
                rw [Finset.sum_eq_zero]
                · simp
                · intro j hj
                  rw [(hIH j hj).1 U (fun h => hUS (h.trans (htk j hj))), mul_zero]
              · intro U
                rw [hU]
                have a1 := hR01 0 (by omega)
                have a2 := hR01 (S.card - 1) (by omega)
                refine add_nonneg (add_nonneg (mul_nonneg (by linarith) ?_) (mul_nonneg a2.1 ?_))
                  (Finset.sum_nonneg ?_)
                · split_ifs <;> norm_num
                · split_ifs <;> norm_num
                · intro j hj
                  have hj' := Finset.mem_Ico.mp hj
                  exact mul_nonneg (by have := hRanti j hj'.1 hj'.2; linarith) ((hIH j hj).2.1 U)
              · simp only [hU]
                rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm]
                have e1 : ∑ j ∈ Finset.Ico 1 S.card, ∑ U, (R (j-1) - R j) *
                    subAssortAux k φ ((sortedList φ S p).take j).toFinset (φ S) U =
                    ∑ j ∈ Finset.Ico (0+1) S.card, (R (j-1) - R j) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [← Finset.mul_sum, (hIH j hj).2.2.1, mul_one]
                rw [e1, htel 0 (by omega)]
                simp
              · intro i hi
                obtain ⟨l, hl, hli⟩ := List.getElem_of_mem ((hmem i).mpr hi)
                simp only [hU, add_mul, Finset.sum_mul]
                rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm]
                have e1 : ∀ j ∈ Finset.Ico 1 S.card, ∑ U, (R (j-1) - R j) *
                    subAssortAux k φ ((sortedList φ S p).take j).toFinset (φ S) U * φ U i =
                    if l + 1 ≤ j then (R (j-1) - R j) * φ S i else 0 := by
                  intro j hj
                  simp only [mul_assoc]
                  rw [← Finset.mul_sum]
                  split_ifs with hlj
                  · rw [(hIH j hj).2.2.2 i]
                    rw [List.mem_toFinset, ← hli, List.mem_take_iff_getElem]
                    exact ⟨l, by omega, rfl⟩
                  · have hni : i ∉ ((sortedList φ S p).take j).toFinset := by
                      rw [List.mem_toFinset, List.mem_take_iff_getElem]
                      rintro ⟨l', hl', he⟩
                      have : l' = l := by
                        apply (List.Nodup.getElem_inj_iff hnd (hi := by omega) (hj := hl)).mp
                        rw [he, hli]
                      omega
                    rw [Finset.sum_eq_zero, mul_zero]
                    intro U _
                    by_cases hUs : U ⊆ ((sortedList φ S p).take j).toFinset
                    · rw [h_supp U (h_down S hS U (hUs.trans (htk j hj))) i (fun h => hni (hUs h)), mul_zero]
                    · rw [(hIH j hj).1 U hUs, zero_mul]
                rw [Finset.sum_congr rfl e1, ← Finset.sum_filter]
                have e2 : (Finset.Ico 1 S.card).filter (fun j => l + 1 ≤ j) = Finset.Ico (l+1) S.card := by
                  ext j; simp only [Finset.mem_filter, Finset.mem_Ico]; omega
                rw [e2, ← Finset.sum_mul, htel l (by omega)]
                have e3 := (hrat i hi).2.2
                have e4 : R l = ratio φ S p i := by rw [hRe l hl, hli]
                simp [Finset.sum_ite_eq, mul_assoc, h_empty]
                rw [← e3, e4]; ring
          have hFinIcc : ∀ f : ℕ → ℝ, f 0 = 0 → ∑ d : Fin (T+1), f d = ∑ d ∈ Finset.Icc 1 T, f d := by
            intro f hf
            rw [Fin.sum_univ_eq_sum_range f (T+1)]
            symm
            apply Finset.sum_subset
            · intro d hd; rw [Finset.mem_Icc] at hd; rw [Finset.mem_range]; omega
            · intro d hd hd'
              rw [Finset.mem_range] at hd; rw [Finset.mem_Icc] at hd'
              have : d = 0 := by omega
              rw [this, hf]
          -- one-step weights
          obtain ⟨w, hw⟩ : ∃ w : ℕ → (Z → Fin n → ℝ) → Step n T Z → ℝ, ∀ t a x, w t a x =
              I.F t x.1 * y t x.1 x.2.1 * (if x.2.1 ∈ I.feas then 1 else 0)
              * ((if x.2.2.1 ⊆ x.2.1 then 1 else 0) * (∏ i ∈ x.2.2.1, a x.1 i) *
                  ∏ i ∈ x.2.1 \ x.2.2.1, (1 - a x.1 i))
              * subAssort (I.phi x.1) x.2.2.1 (fun i => I.phi x.1 x.2.1 i) x.2.2.2.1
              * (match x.2.2.2.2.1 with
                  | some i => if i ∈ x.2.2.2.1 then I.phi x.1 x.2.2.2.1 i else 0
                  | none => 1 - ∑ i ∈ x.2.2.2.1, I.phi x.1 x.2.2.2.1 i)
              * (match x.2.2.2.2.1 with
                  | some i => I.g x.1 i (x.2.2.2.2.2 : ℕ)
                  | none => if (x.2.2.2.2.2 : ℕ) = 0 then 1 else 0) := ⟨_, fun _ _ _ => rfl⟩
          have hSA : ∀ z, ∀ S ∈ I.feas, ∀ A ⊆ S,
              (∀ U, ¬ U ⊆ A → subAssort (I.phi z) A (fun i => I.phi z S i) U = 0) ∧
              (∀ U, 0 ≤ subAssort (I.phi z) A (fun i => I.phi z S i) U) ∧
              (∑ U, subAssort (I.phi z) A (fun i => I.phi z S i) U = 1) ∧
              ∀ i ∈ A, ∑ U, subAssort (I.phi z) A (fun i => I.phi z S i) U * I.phi z U i = I.phi z S i := by
            intro z S hS A hA
            exact hP3 (I.phi z) I.feas (hI.phi_empty z) (hI.weak_subst z) hI.down_closed
              (hI.phi_nonneg z) (hI.phi_support z) A.card A _ le_rfl (hI.down_closed S hS A hA)
              (fun i hi => ⟨hI.phi_nonneg z S hS i,
                hWS (I.phi z) I.feas (hI.weak_subst z) hI.down_closed S hS A hA i hi⟩)
          have hw0 : ∀ t ∈ Finset.Icc 1 T, ∀ a : Z → Fin n → ℝ, (∀ z i, 0 ≤ a z i ∧ a z i ≤ 1) →
              ∀ x, 0 ≤ w t a x := by
            rintro t ht a ha ⟨z, Sh, Sb, U, ch, d⟩
            rw [hw]
            simp only []
            by_cases hS : Sh ∈ I.feas
            swap
            · simp [hS]
            by_cases hB : Sb ⊆ Sh
            swap
            · simp [hB]
            by_cases hU : U ⊆ Sb
            swap
            · rw [(hSA z Sh hS Sb hB).1 U hU]; simp
            have hUf : U ∈ I.feas := hI.down_closed Sh hS U (hU.trans hB)
            rw [if_pos hS, if_pos hB]
            refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ((hSA z Sh hS Sb hB).2.1 U)) ?_) ?_
            · rw [mul_one]; exact mul_nonneg (hI.F_nonneg t z) (hy.1.1 t ht z Sh hS)
            · rw [one_mul]
              exact mul_nonneg (Finset.prod_nonneg fun i _ => (ha z i).1)
                (Finset.prod_nonneg fun i _ => by linarith [(ha z i).2])
            · cases ch with
              | none => simp only []; linarith [hI.phi_sum_le z U hUf]
              | some i => simp only []; split_ifs; exacts [hI.phi_nonneg z U hUf i, le_rfl]
            · cases ch with
              | none => simp only []; split_ifs <;> norm_num
              | some i => exact hI.g_nonneg z i _
          -- general collapse of a step sum
          have hcoll : ∀ t (a : Z → Fin n → ℝ) (f : Z → Option (Fin n) → ℕ → ℝ) (e : Z → Option (Fin n) → ℝ)
              (m : Z → Finset (Fin n) → ℝ) (b : Z → Finset (Fin n) → Finset (Fin n) → ℝ)
              (c : Z → Finset (Fin n) → ℝ),
              (∀ z ch, ∑ d : Fin (T+1), (match ch with
                  | some i => I.g z i (d : ℕ)
                  | none => if (d : ℕ) = 0 then 1 else 0) * f z ch d = e z ch) →
              (∀ z, ∀ U ∈ I.feas, ∑ ch : Option (Fin n), (match ch with
                  | some i => if i ∈ U then I.phi z U i else 0
                  | none => 1 - ∑ i ∈ U, I.phi z U i) * e z ch = m z U) →
              (∀ z, ∀ S ∈ I.feas, ∀ A ⊆ S, ∑ U, subAssort (I.phi z) A (fun i => I.phi z S i) U * m z U
                = b z S A) →
              (∀ z, ∀ S ∈ I.feas, ∑ A ∈ S.powerset, ((∏ i ∈ A, a z i) * ∏ i ∈ S \ A, (1 - a z i)) * b z S A
                = c z S) →
              ∑ x, w t a x * f x.1 x.2.2.2.2.1 (x.2.2.2.2.2 : ℕ) =
                ∑ z, ∑ S ∈ I.feas, I.F t z * y t z S * c z S := by
            intro t a f e m b c he hm hb hc
            simp only [hw, Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro z _
            rw [← Finset.sum_subset (Finset.subset_univ I.feas)]
            swap
            · intro S _ hS; simp [hS]
            apply Finset.sum_congr rfl
            intro S hS
            rw [← hc z S hS, Finset.mul_sum]
            rw [← Finset.sum_subset (Finset.subset_univ S.powerset)]
            swap
            · intro A _ hA; rw [Finset.mem_powerset] at hA; simp [hA]
            apply Finset.sum_congr rfl
            intro A hA
            rw [Finset.mem_powerset] at hA
            rw [← hb z S hS A hA, Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro U _
            by_cases hU : U ⊆ A
            swap
            · rw [(hSA z S hS A hA).1 U hU]; simp
            rw [← hm z U (hI.down_closed S hS U (hU.trans hA)), Finset.mul_sum, Finset.mul_sum,
              Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ch _
            rw [← he z ch, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d _
            rw [if_pos hS, if_pos hA]
            ring
          have hw1 : ∀ t ∈ Finset.Icc 1 T, ∀ a : Z → Fin n → ℝ, ∑ x, w t a x = 1 := by
            intro t ht a
            have := hcoll t a (fun _ _ _ => 1) (fun _ _ => 1) (fun _ _ => 1) (fun _ _ _ => 1)
              (fun _ _ => 1) ?_ ?_ ?_ ?_
            · simp only [mul_one] at this
              rw [this, ← hI.F_sum t ht]
              apply Finset.sum_congr rfl
              intro z _
              rw [← Finset.mul_sum, hN t ht z, mul_one]
            · intro z ch
              cases ch with
              | none =>
                simp only [mul_one]
                rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin (T+1))]
                · simp
                · intro d _ hd; rw [if_neg]; intro h; exact hd (Fin.ext h)
                · simp
              | some i =>
                simp only [mul_one]
                rw [hFinIcc (fun d => I.g z i d) (hI.g_zero z i)]
                exact hI.g_sum z i
            · intro z U _
              rw [Fintype.sum_option]
              simp [Finset.sum_ite_mem]
            · intro z S hS A hA
              simp only [mul_one]
              exact (hSA z S hS A hA).2.2.1
            · intro z S hS
              simp only [mul_one]
              rw [← Finset.prod_add]
              simp
          have hwm : ∀ t ∈ Finset.Icc 1 T, ∀ (a : Z → Fin n → ℝ) (i : Fin n) (u : Z → ℕ → ℝ),
              ∑ x, w t a x * (if x.2.2.2.2.1 = some i then u x.1 (x.2.2.2.2.2 : ℕ) else 0) =
                ∑ z, ∑ S ∈ I.feas, I.F t z * y t z S * (a z i * I.phi z S i *
                  ∑ d ∈ Finset.Icc 1 T, I.g z i d * u z d) := by
            intro t ht a i u
            refine hcoll t a (fun z ch d => if ch = some i then u z d else 0)
              (fun z ch => if ch = some i then ∑ d ∈ Finset.Icc 1 T, I.g z i d * u z d else 0)
              (fun z U => I.phi z U i * ∑ d ∈ Finset.Icc 1 T, I.g z i d * u z d)
              (fun z S A => if i ∈ A then I.phi z S i * ∑ d ∈ Finset.Icc 1 T, I.g z i d * u z d else 0)
              (fun z S => _) ?_ ?_ ?_ ?_
            · intro z ch
              split_ifs with h
              · subst h
                simp only [if_true]
                exact hFinIcc (fun d => I.g z i d * u z d) (by rw [hI.g_zero, zero_mul])
              · simp
            · intro z U hU
              rw [Fintype.sum_option]
              simp only [reduceCtorEq, if_false, mul_zero, zero_add, Option.some.injEq, mul_ite]
              rw [Finset.sum_ite_eq' ]
              simp only [Finset.mem_univ, if_true]
              split_ifs with h
              · rfl
              · rw [hI.phi_support z U hU i h]
            · intro z S hS A hA
              simp only [← mul_assoc]
              rw [← Finset.sum_mul]
              split_ifs with h
              · rw [(hSA z S hS A hA).2.2.2 i h]
              · rw [Finset.sum_eq_zero, zero_mul]
                intro U _
                by_cases hU : U ⊆ A
                · rw [hI.phi_support z U (hI.down_closed S hS U (hU.trans hA)) i (fun h' => h (hU h')), mul_zero]
                · rw [(hSA z S hS A hA).1 U hU, zero_mul]
            · intro z S hS
              by_cases hiS : i ∈ S
              · have h1 : ∀ A ∈ S.powerset, ((∏ j ∈ A, a z j) * ∏ j ∈ S \ A, (1 - a z j)) *
                    (if i ∈ A then I.phi z S i * ∑ d ∈ Finset.Icc 1 T, I.g z i d * u z d else 0) =
                    ((∏ j ∈ A, a z j) * ∏ j ∈ S \ A, (if j = i then 0 else 1 - a z j)) *
                      (I.phi z S i * ∑ d ∈ Finset.Icc 1 T, I.g z i d * u z d) := by
                  intro A hA
                  split_ifs with h
                  · congr 2
                    apply Finset.prod_congr rfl
                    intro j hj
                    rw [if_neg]; rintro rfl; exact (Finset.mem_sdiff.mp hj).2 h
                  · have h0 : ∏ j ∈ S \ A, (if j = i then 0 else 1 - a z j) = 0 :=
                      Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨hiS, h⟩) (if_pos rfl)
                    rw [h0]; ring
                rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← Finset.prod_add]
                have h2 : ∏ j ∈ S, (a z j + if j = i then 0 else 1 - a z j) = a z i := by
                  rw [Finset.prod_eq_single_of_mem i hiS]
                  · simp
                  · intro j _ hj; rw [if_neg hj]; ring
                rw [h2]; ring
              · rw [hI.phi_support z S hS i hiS]
                simp
          clear hcoll hSA hFinIcc hP3 hWS
          have hcard : ∀ (N M : ℕ) (hM : N = M + 1) (p : Fin N → Prop) [DecidablePred p],
              (Finset.univ.filter p).card = (if p ⟨0, by omega⟩ then 1 else 0) +
                (Finset.univ.filter (fun j : Fin M => p ⟨j.1 + 1, by omega⟩)).card := by
            intro N M hM p _
            subst hM
            exact Fin.card_filter_univ_succ' p
          have hone : ∀ (t : ℕ) (v : Fin (T + 1 - t) → Step n T Z) (h0 : 0 < T + 1 - t) (i : Fin n) (s : ℕ),
              (Finset.univ.filter (fun j : Fin (T + 1 - t) =>
                j.1 < 1 ∧ (v j).2.2.2.2.1 = some i ∧ t + j.1 + ((v j).2.2.2.2.2 : ℕ) = s)).card =
              if (v ⟨0, h0⟩).2.2.2.2.1 = some i ∧ t + ((v ⟨0, h0⟩).2.2.2.2.2 : ℕ) = s then 1 else 0 := by
            intro t v h0 i s
            rw [hcard (T + 1 - t) (T + 1 - (t + 1)) (by omega)]
            have hz : (Finset.univ.filter (fun j : Fin (T + 1 - (t + 1)) =>
                j.1 + 1 < 1 ∧ (v ⟨j.1 + 1, by omega⟩).2.2.2.2.1 = some i ∧
                  t + (j.1 + 1) + ((v ⟨j.1 + 1, by omega⟩).2.2.2.2.2 : ℕ) = s)).card = 0 := by
              rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro j _ hj; omega
            simp only [] at hz ⊢
            rw [hz, add_zero]
            apply if_congr _ rfl rfl
            constructor
            · rintro ⟨_, h2, h3⟩; exact ⟨h2, by omega⟩
            · rintro ⟨h2, h3⟩; exact ⟨by omega, h2, by omega⟩
          -- Markov shift of the outstanding-return state
          have hRetShift : ∀ (t₀ : ℕ) (ret : Fin n → ℕ → ℕ) (v : Fin (T + 1 - t₀) → Step n T Z)
              (h0 : 0 < T + 1 - t₀) (k : ℕ),
              retState t₀ ret v (k + 1) =
                retState (t₀ + 1) (retState t₀ ret v 1)
                  (fun j : Fin (T + 1 - (t₀ + 1)) => v ⟨j.1 + 1, by omega⟩) k := by
            intro t₀ ret v h0 k
            funext i s
            unfold retState
            by_cases hs : t₀ + (k + 1) < s
            · have hs1 : t₀ + 1 + k < s := by omega
              have hs2 : t₀ + 1 < s := by omega
              rw [if_pos hs, if_pos hs1, if_pos hs2, add_assoc, hone t₀ v h0]
              congr 1
              rw [hcard (T + 1 - t₀) (T + 1 - (t₀ + 1)) (by omega)]
              congr 1
              · apply if_congr _ rfl rfl
                dsimp only
                constructor
                · rintro ⟨_, h2, h3⟩; exact ⟨h2, by omega⟩
                · rintro ⟨h2, h3⟩; exact ⟨by omega, h2, by omega⟩
              · congr 1
                apply Finset.filter_congr
                intro j _
                dsimp only
                constructor
                · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, by omega⟩
                · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, by omega⟩
            · have hs1 : ¬ t₀ + 1 + k < s := by omega
              rw [if_neg hs, if_neg hs1]
          -- Markov shift of the on-hand inventory, for a start state whose returns lie in `(t₀, t₀+T]`.
          have hOnShift : ∀ (t₀ : ℕ) (ret : Fin n → ℕ → ℕ) (v : Fin (T + 1 - t₀) → Step n T Z)
              (h0 : 0 < T + 1 - t₀), (∀ i s, s ∉ Finset.Ioc t₀ (t₀ + T) → ret i s = 0) →
              ∀ (i : Fin n) (k : ℕ),
              onHand I t₀ ret v i (k + 1) =
                onHand I (t₀ + 1) (retState t₀ ret v 1)
                  (fun j : Fin (T + 1 - (t₀ + 1)) => v ⟨j.1 + 1, by omega⟩) i k := by
            intro t₀ ret v h0 hret i k
            have hd0 : ((v ⟨0, h0⟩).2.2.2.2.2 : ℕ) ≤ T := by
              have := ((v ⟨0, h0⟩).2.2.2.2.2).isLt; omega
            have hA : ∑ s ∈ Finset.Ioc (t₀ + 1 + k) (t₀ + 1 + T), retState t₀ ret v 1 i s =
                ∑ s ∈ Finset.Ioc (t₀ + (k + 1)) (t₀ + T), ret i s +
                  (if (v ⟨0, h0⟩).2.2.2.2.1 = some i ∧ k + 1 < ((v ⟨0, h0⟩).2.2.2.2.2 : ℕ)
                    then 1 else 0) := by
              have h1 : ∀ s ∈ Finset.Ioc (t₀ + 1 + k) (t₀ + 1 + T), retState t₀ ret v 1 i s =
                  ret i s + (if (v ⟨0, h0⟩).2.2.2.2.1 = some i ∧
                    t₀ + ((v ⟨0, h0⟩).2.2.2.2.2 : ℕ) = s then 1 else 0) := by
                intro s hs
                rw [Finset.mem_Ioc] at hs
                unfold retState
                rw [if_pos (by omega)]
                rw [hone t₀ v h0]
              rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
              congr 1
              · symm
                apply Finset.sum_subset
                · intro s hs; rw [Finset.mem_Ioc] at hs ⊢; omega
                · intro s hs hs'
                  apply hret
                  rw [Finset.mem_Ioc] at hs hs' ⊢; omega
              · by_cases hP : (v ⟨0, h0⟩).2.2.2.2.1 = some i
                · simp only [hP, true_and]
                  rw [Finset.sum_ite_eq]
                  apply if_congr _ rfl rfl
                  rw [Finset.mem_Ioc]; omega
                · simp [hP]
            have hB : (Finset.univ.filter (fun j : Fin (T + 1 - t₀) =>
                  j.1 < k + 1 ∧ (v j).2.2.2.2.1 = some i ∧ k + 1 < j.1 + ((v j).2.2.2.2.2 : ℕ))).card =
                (if (v ⟨0, h0⟩).2.2.2.2.1 = some i ∧ k + 1 < ((v ⟨0, h0⟩).2.2.2.2.2 : ℕ)
                    then 1 else 0) +
                (Finset.univ.filter (fun j : Fin (T + 1 - (t₀ + 1)) =>
                  j.1 < k ∧ (v ⟨j.1 + 1, by omega⟩).2.2.2.2.1 = some i ∧
                    k < j.1 + ((v ⟨j.1 + 1, by omega⟩).2.2.2.2.2 : ℕ))).card := by
              rw [hcard (T + 1 - t₀) (T + 1 - (t₀ + 1)) (by omega)]
              congr 1
              · apply if_congr _ rfl rfl
                simp only [Fin.val_mk]
                constructor
                · rintro ⟨_, h2, h3⟩; exact ⟨h2, by omega⟩
                · rintro ⟨h2, h3⟩; exact ⟨by omega, h2, by omega⟩
              · congr 1
                apply Finset.filter_congr
                intro j _
                simp only [Fin.val_mk]
                constructor
                · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, by omega⟩
                · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, by omega⟩
            unfold onHand
            simp only []
            rw [hA, hB]
            omega
          -- Splitting a path sum into the first step and the tail.
          have hSumSplit : ∀ (N M : ℕ) (hM : N = M + 1) (f : (Fin N → Step n T Z) → ℝ),
              ∑ v, f v = ∑ x : Step n T Z, ∑ w : Fin M → Step n T Z,
                f (fun j => if h : j.1 = 0 then x else w ⟨j.1 - 1, by omega⟩) := by
            intro N M hM f
            subst hM
            rw [← (Fin.consEquiv (fun _ : Fin (M + 1) => Step n T Z)).sum_comp, Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro w _
            congr 1
            funext j
            refine Fin.cases ?_ (fun j => ?_) j
            · simp [Fin.consEquiv]
            · simp [Fin.consEquiv, Fin.cons_succ]
          -- Markov keep rules
          obtain ⟨κ, hκ⟩ : ∃ κ : (ℕ → (Fin n → ℕ → ℕ) → Z → Fin n → ℝ) → (t₀ : ℕ) → (Fin n → ℕ → ℕ) →
              Fin (T + 1 - t₀) → (Fin (T + 1 - t₀) → Step n T Z) → Fin n → ℝ, ∀ ψ t₀ ret k v i,
              κ ψ t₀ ret k v i = if onHand I t₀ ret v i k.1 = 0 then 0 else
                ψ (t₀ + k.1) (retState t₀ ret v k.1) (v k).1 i := ⟨_, fun _ _ _ _ _ _ => rfl⟩
          obtain ⟨nx, hnx⟩ : ∃ nx : ℕ → (Fin n → ℕ → ℕ) → Step n T Z → Fin n → ℕ → ℕ, ∀ t J x i s,
              nx t J x i s = if t + 1 < s then J i s + (if x.2.2.2.2.1 = some i ∧
                t + (x.2.2.2.2.2 : ℕ) = s then 1 else 0) else 0 := ⟨_, fun _ _ _ _ _ => rfl⟩
          obtain ⟨act, hact⟩ : ∃ act : (ℕ → (Fin n → ℕ → ℕ) → Z → Fin n → ℝ) → ℕ → (Fin n → ℕ → ℕ) →
              Z → Fin n → ℝ, ∀ ψ t J z i, act ψ t J z i =
                if I.c i - ∑ s ∈ Finset.Ioc t (t + T), J i s = 0 then 0 else ψ t J z i :=
            ⟨_, fun _ _ _ _ _ => rfl⟩
          obtain ⟨win, hwin⟩ : ∃ win : ℕ → (Fin n → ℕ → ℕ) → Prop, ∀ t J, win t J ↔
              ∀ i s, s ∉ Finset.Ioc t (t + T) → J i s = 0 := ⟨_, fun _ _ => Iff.rfl⟩
          have hwinnx : ∀ t J x, win t J → win (t + 1) (nx t J x) := by
            intro t J x h
            rw [hwin] at h ⊢
            intro i s hs
            rw [hnx]
            split_ifs with h1 h2
            · exfalso; apply hs; rw [Finset.mem_Ioc]; have := x.2.2.2.2.2.isLt; omega
            · rw [h i s (by rw [Finset.mem_Ioc] at hs ⊢; omega)]
            · rfl
          have hret1 : ∀ (t : ℕ) (J : Fin n → ℕ → ℕ) (v : Fin (T + 1 - t) → Step n T Z)
              (h0 : 0 < T + 1 - t), retState t J v 1 = nx t J (v ⟨0, h0⟩) := by
            intro t J v h0
            funext i s
            rw [hnx]; unfold retState
            by_cases hs : t + 1 < s
            swap
            · rw [if_neg hs, if_neg hs]
            rw [if_pos hs, if_pos hs]
            congr 1
            rw [hone t v h0]
          have hret0 : ∀ (t : ℕ) (J : Fin n → ℕ → ℕ) (v : Fin (T + 1 - t) → Step n T Z),
              win t J → retState t J v 0 = J := by
            intro t J v h
            rw [hwin] at h
            funext i s
            unfold retState
            by_cases hs : t + 0 < s
            · rw [if_pos hs]; simp
            · rw [if_neg hs, h i s (by rw [Finset.mem_Ioc]; omega)]
          have hon0 : ∀ (t : ℕ) (J : Fin n → ℕ → ℕ) (v : Fin (T + 1 - t) → Step n T Z) (i : Fin n),
              onHand I t J v i 0 = I.c i - ∑ s ∈ Finset.Ioc t (t + T), J i s := by
            intro t J v i
            unfold onHand
            simp
          have hK0 : ∀ ψ (t : ℕ) (J : Fin n → ℕ → ℕ) (v : Fin (T + 1 - t) → Step n T Z)
              (h0 : 0 < T + 1 - t), win t J →
              kernelA I y t (κ ψ t J) v ⟨0, h0⟩ = w t (act ψ t J) (v ⟨0, h0⟩) := by
            intro ψ t J v h0 h
            rw [hw]
            unfold kernelA
            simp only [hκ, hact, hon0, hret0 t J v h, add_zero]
            rcases (v ⟨0, h0⟩).2.2.2.2.1 with _ | i <;> rfl
          have hKS : ∀ ψ (t : ℕ) (J : Fin n → ℕ → ℕ) (v : Fin (T + 1 - t) → Step n T Z)
              (h0 : 0 < T + 1 - t), win t J → ∀ (k : Fin (T + 1 - (t + 1))),
              kernelA I y t (κ ψ t J) v ⟨k.1 + 1, by omega⟩ =
                kernelA I y (t + 1) (κ ψ (t + 1) (nx t J (v ⟨0, h0⟩)))
                  (fun j : Fin (T + 1 - (t + 1)) => v ⟨j.1 + 1, by omega⟩) k := by
            intro ψ t J v h0 h k
            rw [hwin] at h
            rw [← hret1 t J v h0]
            unfold kernelA
            simp only [hκ, hOnShift t J v h0 h, hRetShift t J v h0 k.1,
              show t + (k.1 + 1) = t + 1 + k.1 by omega]
          -- path recursion
          have hprodSplit : ∀ (N M : ℕ) (hM : N = M + 1) (f : Fin N → ℝ),
              ∏ k, f k = f ⟨0, by omega⟩ * ∏ k : Fin M, f ⟨k.1 + 1, by omega⟩ := by
            intro N M hM f
            subst hM
            rw [Fin.prod_univ_succ]; rfl
          have hPP : ∀ ψ (t : ℕ) (J : Fin n → ℕ → ℕ) (h0 : 0 < T + 1 - t), win t J →
              ∀ (x : Step n T Z) (u : Fin (T + 1 - (t + 1)) → Step n T Z),
              pathProbA I y t (κ ψ t J)
                (fun j => if h : j.1 = 0 then x else u ⟨j.1 - 1, by omega⟩) =
              w t (act ψ t J) x * pathProbA I y (t + 1) (κ ψ (t + 1) (nx t J x)) u := by
            intro ψ t J h0 h x u
            unfold pathProbA
            rw [hprodSplit (T + 1 - t) (T + 1 - (t + 1)) (by omega), hK0 ψ t J _ h0 h]
            simp only [dif_pos]
            congr 1
            apply Finset.prod_congr rfl
            intro k _
            rw [hKS ψ t J _ h0 h k]
            simp
          have hrv : ∀ (t : ℕ) (h0 : 0 < T + 1 - t) (i : Fin n)
              (x : Step n T Z) (u : Fin (T + 1 - (t + 1)) → Step n T Z),
              ∑ k ∈ Finset.range (T + 1 - t), revAt I t i k
                (fun j => if h : j.1 = 0 then x else u ⟨j.1 - 1, by omega⟩) =
              (if x.2.2.2.2.1 = some i then I.r x.1 i else 0) +
                ∑ k ∈ Finset.range (T + 1 - (t + 1)), revAt I (t + 1) i k u := by
            intro t h0 i x u
            have e : T + 1 - t = (T + 1 - (t + 1)) + 1 := by omega
            rw [show Finset.range (T + 1 - t) = Finset.range ((T + 1 - (t + 1)) + 1) by rw [← e],
              Finset.sum_range_succ', add_comm]
            congr 1
            · unfold revAt
              rw [dif_pos h0]; simp
            · apply Finset.sum_congr rfl
              intro k hk
              rw [Finset.mem_range] at hk
              unfold revAt
              rw [dif_pos hk, dif_pos (by omega)]
              simp
          have hMass : ∀ ψ (m t : ℕ) (J : Fin n → ℕ → ℕ), 1 ≤ t → T + 1 - t = m → win t J →
              ∑ v, pathProbA I y t (κ ψ t J) v = 1 := by
            intro ψ m
            induction m with
            | zero =>
              intro t J ht hm h
              unfold pathProbA
              have he : IsEmpty (Fin (T + 1 - t)) := by rw [hm]; infer_instance
              simp
            | succ m ih =>
              intro t J ht hm h
              rw [hSumSplit (T + 1 - t) (T + 1 - (t + 1)) (by omega)]
              rw [← hw1 t (by rw [Finset.mem_Icc]; omega) (act ψ t J)]
              apply Finset.sum_congr rfl
              intro x _
              simp only [hPP ψ t J (by omega) h]
              rw [← Finset.mul_sum, ih (t + 1) _ (by omega) (by omega) (hwinnx t J x h), mul_one]
          obtain ⟨Val, hVal⟩ : ∃ Val : (ℕ → (Fin n → ℕ → ℕ) → Z → Fin n → ℝ) → ℕ → (Fin n → ℕ → ℕ) →
              Fin n → ℝ, ∀ ψ t J i, Val ψ t J i = ∑ v, pathProbA I y t (κ ψ t J) v *
                ∑ k ∈ Finset.range (T + 1 - t), revAt I t i k v := ⟨_, fun _ _ _ _ => rfl⟩
          have hVal0 : ∀ ψ J i, Val ψ (T + 1) J i = 0 := by
            intro ψ J i
            rw [hVal]
            apply Finset.sum_eq_zero
            intro v _
            rw [show Finset.range (T + 1 - (T + 1)) = ∅ by simp]
            simp
          have hValR : ∀ ψ t J i, t ∈ Finset.Icc 1 T → win t J → Val ψ t J i =
              ∑ x, w t (act ψ t J) x * ((if x.2.2.2.2.1 = some i then I.r x.1 i else 0) +
                Val ψ (t + 1) (nx t J x) i) := by
            intro ψ t J i ht h
            have ht' := Finset.mem_Icc.mp ht
            rw [hVal, hSumSplit (T + 1 - t) (T + 1 - (t + 1)) (by omega)]
            apply Finset.sum_congr rfl
            intro x _
            simp only [hPP ψ t J (by omega) h, hrv t (by omega)]
            simp only [mul_add, Finset.sum_add_distrib]
            congr 1
            · rw [← Finset.sum_mul, ← Finset.mul_sum,
                hMass ψ _ (t + 1) _ (by omega) rfl (hwinnx t J x h), mul_one]
            · rw [hVal, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro u _
              ring
          obtain ⟨ψr, hψr⟩ : ∃ ψr : (Fin n → Rule Z) → ℕ → (Fin n → ℕ → ℕ) → Z → Fin n → ℝ,
              ∀ rule t J z i, ψr rule t J z i = keep I i (rule i) t z := ⟨_, fun _ _ _ _ _ => rfl⟩
          obtain ⟨ψh, hψh⟩ : ∃ ψh : ℕ → (Fin n → ℕ → ℕ) → Z → Fin n → ℝ,
              ∀ t J z i, ψh t J z i = keep I i ((if useAlg2 I y γ tb t J then alg2 γ else alg3 I y) i) t z :=
            ⟨_, fun _ _ _ _ => rfl⟩
          have hER : ∀ rule t J, expRev I y rule t J = ∑ i, Val (ψr rule) t J i := by
            intro rule t J
            unfold expRev expRevProd
            apply Finset.sum_congr rfl
            intro i _
            rw [hVal]
            apply Finset.sum_congr rfl
            intro v _
            congr 1
            unfold pathProb pathProbA
            apply Finset.prod_congr rfl
            intro k _
            unfold kernel kernelA
            simp only [hκ, hψr]
            rcases (v k).2.2.2.2.1 with _ | i <;> rfl
          have hEH : ∀ t J, expRevHybridIIFrom I y γ tb t J = ∑ i, Val ψh t J i := by
            intro t J
            unfold expRevHybridIIFrom expRevA
            simp only [hVal]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro v _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            congr 1
            unfold pathProbA
            apply Finset.prod_congr rfl
            intro k _
            unfold kernelA hybridIIKeep
            simp only [hκ, hψh]
          clear hRetShift hone hcard hOnShift hSumSplit hret1 hret0 hon0 hK0 hKS hprodSplit hPP hrv hMass hVal hw hκ κ
          have hγ01 := hγ.1
          rw [Set.mem_Icc] at hγ01
          have hkeep2 : ∀ i t z, keep I i (alg2 γ i) t z = 1 - γ := by
            intro i t z; rfl
          have hkeep3 : ∀ i t z, keep I i (alg3 I y i) t z = if P I y i t z ≤ I.r z i then 1 else 0 := by
            intro i t z; rfl
          have hk201 : ∀ i t z, 0 ≤ keep I i (alg2 γ i) t z ∧ keep I i (alg2 γ i) t z ≤ 1 := by
            intro i t z; rw [hkeep2]; constructor <;> linarith [hγ01.1, hγ01.2]
          have hk301 : ∀ i t z, 0 ≤ keep I i (alg3 I y i) t z ∧ keep I i (alg3 I y i) t z ≤ 1 := by
            intro i t z; rw [hkeep3]; split_ifs <;> norm_num
          have hact01 : ∀ (ψ : ℕ → (Fin n → ℕ → ℕ) → Z → Fin n → ℝ),
              (∀ t J z i, 0 ≤ ψ t J z i ∧ ψ t J z i ≤ 1) →
              ∀ t J z i, 0 ≤ act ψ t J z i ∧ act ψ t J z i ≤ 1 := by
            intro ψ h t J z i
            rw [hact]
            split_ifs
            · norm_num
            · exact h t J z i
          have hψ2 : ∀ t J z i, 0 ≤ ψr (alg2 γ) t J z i ∧ ψr (alg2 γ) t J z i ≤ 1 := by
            intro t J z i; rw [hψr]; exact hk201 i t z
          have hψ3 : ∀ t J z i, 0 ≤ ψr (alg3 I y) t J z i ∧ ψr (alg3 I y) t J z i ≤ 1 := by
            intro t J z i; rw [hψr]; exact hk301 i t z
          -- total value recursion
          have hVT : ∀ ψ t J, t ∈ Finset.Icc 1 T → win t J → ∑ i, Val ψ t J i =
              ∑ x, w t (act ψ t J) x * ((∑ i, if x.2.2.2.2.1 = some i then I.r x.1 i else 0) +
                ∑ i, Val ψ (t + 1) (nx t J x) i) := by
            intro ψ t J ht h
            rw [Finset.sum_congr rfl (fun i _ => hValR ψ t J i ht h), Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro x _
            rw [← Finset.mul_sum, Finset.sum_add_distrib]
          have hii : ∀ (m t : ℕ) (J : Fin n → ℕ → ℕ), T + 1 - t = m → t ∈ Finset.Icc 1 (T + 1) → win t J →
              max (∑ i, Val (ψr (alg2 γ)) t J i) (∑ i, Val (ψr (alg3 I y)) t J i) ≤ ∑ i, Val ψh t J i := by
            intro m
            induction m with
            | zero =>
              intro t J hm ht h
              rw [Finset.mem_Icc] at ht
              have : t = T + 1 := by omega
              subst this
              simp [hVal0]
            | succ m ih =>
              intro t J hm ht h
              rw [Finset.mem_Icc] at ht
              have ht' : t ∈ Finset.Icc 1 T := by rw [Finset.mem_Icc]; omega
              have step : ∀ rule, (∀ t J z i, 0 ≤ ψr rule t J z i ∧ ψr rule t J z i ≤ 1) →
                  (∀ J', win (t+1) J' → ∑ i, Val (ψr rule) (t+1) J' i ≤ ∑ i, Val ψh (t+1) J' i) →
                  act ψh t J = act (ψr rule) t J →
                  ∑ i, Val (ψr rule) t J i ≤ ∑ i, Val ψh t J i := by
                intro rule hr hle he
                rw [hVT _ t J ht' h, hVT _ t J ht' h, he]
                apply Finset.sum_le_sum
                intro x _
                apply mul_le_mul_of_nonneg_left _ (hw0 t ht' _ (hact01 _ hr t J) x)
                linarith [hle _ (hwinnx t J x h)]
              have ih' := fun J' (hJ' : win (t+1) J') =>
                ih (t+1) J' (by omega) (by rw [Finset.mem_Icc]; omega) hJ'
              have ihA := fun J' (hJ' : win (t+1) J') => le_trans (le_max_left _ _) (ih' J' hJ')
              have ihB := fun J' (hJ' : win (t+1) J') => le_trans (le_max_right _ _) (ih' J' hJ')
              have hdef : useAlg2 I y γ tb t J =
                  if ∑ i, Val (ψr (alg3 I y)) t J i < ∑ i, Val (ψr (alg2 γ)) t J i then true
                  else if ∑ i, Val (ψr (alg2 γ)) t J i < ∑ i, Val (ψr (alg3 I y)) t J i then false
                  else tb t J := by
                unfold useAlg2
                simp only [hER]
              by_cases hu : useAlg2 I y γ tb t J = true
              · have he : act ψh t J = act (ψr (alg2 γ)) t J := by
                  funext z i; rw [hact, hact, hψh, hψr, if_pos hu]
                have h1 := step _ hψ2 ihA he
                apply max_le h1
                refine le_trans ?_ h1
                rw [hdef] at hu
                split_ifs at hu with c1 c2
                · exact c1.le
                · exact not_lt.mp c2
              · have he : act ψh t J = act (ψr (alg3 I y)) t J := by
                  funext z i; rw [hact, hact, hψh, hψr, if_neg hu]
                have h1 := step _ hψ3 ihB he
                refine max_le ?_ h1
                refine le_trans ?_ h1
                rw [hdef] at hu
                split_ifs at hu with c1 c2
                · simp at hu
                · exact c2.le
                · exact not_lt.mp c1
          have hii' : ∀ t ∈ Finset.Icc 1 (T + 1), ∀ J, ValidStart I t J →
              max (expRev I y (alg2 γ) t J) (expRev I y (alg3 I y) t J) ≤
                expRevHybridIIFrom I y γ tb t J := by
            intro t ht J hJ
            rw [hER, hER, hEH]
            exact hii _ t J rfl ht ((hwin t J).mpr hJ.1)
          clear hii hVT hψh hEH
          have hPot : ∀ ψ, (∀ t J z i, 0 ≤ ψ t J z i ∧ ψ t J z i ≤ 1) → ∀ (i : Fin n)
              (A : ℕ → (ℕ → ℕ) → ℝ), (∀ j, A (T + 1) j ≤ 0) →
              (∀ t J, t ∈ Finset.Icc 1 T → win t J → A t (J i) ≤
                ∑ x, w t (act ψ t J) x * ((if x.2.2.2.2.1 = some i then I.r x.1 i else 0) +
                  A (t + 1) (nx t J x i))) →
              ∀ (m t : ℕ) (J : Fin n → ℕ → ℕ), T + 1 - t = m → t ∈ Finset.Icc 1 (T + 1) → win t J →
                A t (J i) ≤ Val ψ t J i := by
            intro ψ hψ i A hA0 hA m
            induction m with
            | zero =>
              intro t J hm ht h
              rw [Finset.mem_Icc] at ht
              have : t = T + 1 := by omega
              subst this
              rw [hVal0]; exact hA0 _
            | succ m ih =>
              intro t J hm ht h
              rw [Finset.mem_Icc] at ht
              have ht' : t ∈ Finset.Icc 1 T := by rw [Finset.mem_Icc]; omega
              refine le_trans (hA t J ht' h) ?_
              rw [hValR ψ t J i ht' h]
              apply Finset.sum_le_sum
              intro x _
              apply mul_le_mul_of_nonneg_left _ (hw0 t ht' _ (hact01 _ hψ t J) x)
              linarith [ih (t+1) (nx t J x) (by omega) (by rw [Finset.mem_Icc]; omega) (hwinnx t J x h)]
          -- linear functionals of the next state
          have hlin : ∀ (t : ℕ) (J : Fin n → ℕ → ℕ) (x : Step n T Z) (i : Fin n) (f : ℕ → ℝ),
              1 ≤ T → win t J → f (t + 1) = 0 →
              ∑ s ∈ Finset.Ioc (t + 1) (t + 1 + T), (nx t J x i s : ℝ) * f s =
                ∑ s ∈ Finset.Ioc t (t + T), (J i s : ℝ) * f s +
                  (if x.2.2.2.2.1 = some i then
                    (if 1 < (x.2.2.2.2.2 : ℕ) then f (t + (x.2.2.2.2.2 : ℕ)) else 0) else 0) := by
            intro t J x i f hT h hf
            rw [hwin] at h
            have hd := x.2.2.2.2.2.isLt
            have e1 : ∀ s ∈ Finset.Ioc (t + 1) (t + 1 + T), (nx t J x i s : ℝ) * f s =
                (J i s : ℝ) * f s + (if t + (x.2.2.2.2.2 : ℕ) = s then
                  (if x.2.2.2.2.1 = some i then f s else 0) else 0) := by
              intro s hs
              rw [Finset.mem_Ioc] at hs
              rw [hnx, if_pos hs.1]
              by_cases h1 : x.2.2.2.2.1 = some i <;> by_cases h2 : t + (x.2.2.2.2.2 : ℕ) = s <;>
                simp [h1, h2] <;> ring
            rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_ite_eq]
            congr 1
            · have e2 : ∑ s ∈ Finset.Ioc (t + 1) (t + 1 + T), (J i s : ℝ) * f s =
                  ∑ s ∈ Finset.Ioc t (t + 1 + T), (J i s : ℝ) * f s := by
                apply Finset.sum_subset
                · intro s hs; rw [Finset.mem_Ioc] at hs ⊢; omega
                · intro s hs hs'
                  rw [Finset.mem_Ioc] at hs hs'
                  have : s = t + 1 := by omega
                  rw [this, hf, mul_zero]
              rw [e2]
              symm
              apply Finset.sum_subset
              · intro s hs; rw [Finset.mem_Ioc] at hs ⊢; omega
              · intro s hs hs'
                rw [h i s hs']; simp
            · by_cases h1 : 1 < (x.2.2.2.2.2 : ℕ)
              · rw [if_pos (by rw [Finset.mem_Ioc]; omega), if_pos h1]
              · rw [if_neg (by rw [Finset.mem_Ioc]; omega), if_neg h1]; simp
          have hcpos : ∀ i, (1 : ℝ) ≤ (I.c i : ℝ) := by
            intro i; exact_mod_cast hI.one_le_c i
          -- facts on V
          have hV0 : ∀ i t, T < t → V I y i t = 0 := by
            intro i t ht; rw [V, dif_pos ht]
          obtain ⟨D, hD⟩ : ∃ D : Fin n → ℕ → ℝ, ∀ i t, D i t = ∑ z, ∑ S ∈ I.feas,
              I.F t z * y t z S * (I.phi z S i * max (I.r z i - P I y i t z) 0) := ⟨_, fun _ _ => rfl⟩
          have hD0 : ∀ i, ∀ t ∈ Finset.Icc 1 T, 0 ≤ D i t := by
            intro i t ht
            rw [hD]
            refine Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun S hS => ?_
            exact mul_nonneg (mul_nonneg (hI.F_nonneg t z) (hy.1.1 t ht z S hS))
              (mul_nonneg (hI.phi_nonneg z S hS i) (le_max_right _ _))
          have hFy : ∀ t ∈ Finset.Icc 1 T, ∑ z, ∑ S ∈ I.feas, I.F t z * y t z S = 1 := by
            intro t ht
            rw [← hI.F_sum t ht]
            apply Finset.sum_congr rfl
            intro z _
            rw [← Finset.mul_sum, hN t ht z, mul_one]
          have hVrec : ∀ i, ∀ t ∈ Finset.Icc 1 T, V I y i t = V I y i (t + 1) + D i t / I.c i := by
            intro i t ht
            have ht' := Finset.mem_Icc.mp ht
            have hc := hcpos i
            have hc0 : (I.c i : ℝ) ≠ 0 := by positivity
            rw [V, dif_neg (by omega)]
            have e : ∀ z, ∀ S ∈ I.feas, X I y t z S *
              max (V I y i (t + 1))
                ((1 - I.phi z S i) * V I y i (t + 1)
                + I.phi z S i *
                  ((1 / (I.c i : ℝ)) * ∑ d ∈ (Finset.Icc 1 T).attach,
                      I.g z i d.1 * (I.r z i + V I y i (t + d.1))
                    + (((I.c i : ℝ) - 1) / (I.c i : ℝ)) * V I y i (t + 1))) =
                I.F t z * y t z S * V I y i (t + 1) +
                  I.F t z * y t z S * (I.phi z S i * max (I.r z i - P I y i t z) 0) / I.c i := by
              intro z S hS
              rw [Finset.sum_attach (Finset.Icc 1 T) (fun d => I.g z i d * (I.r z i + V I y i (t + d)))]
              have e1 : ∑ d ∈ Finset.Icc 1 T, I.g z i d * (I.r z i + V I y i (t + d)) =
                  I.r z i - P I y i t z + V I y i (t + 1) := by
                unfold P
                simp only [mul_add, Finset.sum_add_distrib]
                rw [← Finset.sum_mul, hI.g_sum]; ring
              rw [e1]
              have e2 : (1 - I.phi z S i) * V I y i (t + 1)
                + I.phi z S i * ((1 / (I.c i : ℝ)) * (I.r z i - P I y i t z + V I y i (t + 1))
                    + (((I.c i : ℝ) - 1) / (I.c i : ℝ)) * V I y i (t + 1)) =
                  V I y i (t + 1) + (I.phi z S i / I.c i) * (I.r z i - P I y i t z) := by
                field_simp; ring
              have e3 : max (V I y i (t + 1)) (V I y i (t + 1) + (I.phi z S i / I.c i) * (I.r z i - P I y i t z))
                  = V I y i (t + 1) + (I.phi z S i / I.c i) * max (I.r z i - P I y i t z) 0 := by
                have h0 : 0 ≤ I.phi z S i / I.c i := div_nonneg (hI.phi_nonneg z S hS i) (by linarith)
                rcases le_total (I.r z i - P I y i t z) 0 with h | h
                · rw [max_eq_right h, max_eq_left]
                  · ring
                  · nlinarith
                · rw [max_eq_left h, max_eq_right]
                  nlinarith
              rw [e2, e3]
              unfold X
              ring
            rw [Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (e z))]
            simp only [Finset.sum_add_distrib]
            simp only [← Finset.sum_mul, ← Finset.sum_div]
            rw [hFy t ht, one_mul, hD]
          have hA3 : ∀ i, (I.c i : ℝ) * V I y i 1 ≤ Val (ψr (alg3 I y)) 1 (fun _ _ => 0) i := by
            intro i
            have := hPot (ψr (alg3 I y)) hψ3 i
              (fun t j => I.c i * V I y i t + ∑ s ∈ Finset.Ioc t (t + T), (j s : ℝ) * (V I y i s - V I y i t))
              ?_ ?_ _ 1 (fun _ _ => 0) rfl (by rw [Finset.mem_Icc]; omega) (by rw [hwin]; intros; rfl)
            · simpa using this
            · intro j
              rw [hV0 i (T+1) (by omega), Finset.sum_eq_zero]
              · simp
              · intro s hs; rw [Finset.mem_Ioc] at hs; rw [hV0 i s (by omega)]; simp
            · intro t J ht h
              have ht' := Finset.mem_Icc.mp ht
              have hl := fun x => hlin t J x i (fun s => V I y i s - V I y i (t + 1)) (by omega) h (by ring)
              simp only [hl]
              have e1 : ∀ x : Step n T Z, w t (act (ψr (alg3 I y)) t J) x *
                  ((if x.2.2.2.2.1 = some i then I.r x.1 i else 0) +
                  (I.c i * V I y i (t + 1) + (∑ s ∈ Finset.Ioc t (t + T), (J i s : ℝ) *
                    (V I y i s - V I y i (t + 1)) +
                  (if x.2.2.2.2.1 = some i then
                    (if 1 < (x.2.2.2.2.2 : ℕ) then V I y i (t + (x.2.2.2.2.2 : ℕ)) - V I y i (t + 1)
                      else 0) else 0)))) =
                  w t (act (ψr (alg3 I y)) t J) x * (I.c i * V I y i (t + 1) +
                    ∑ s ∈ Finset.Ioc t (t + T), (J i s : ℝ) * (V I y i s - V I y i (t + 1))) +
                  w t (act (ψr (alg3 I y)) t J) x * (if x.2.2.2.2.1 = some i then
                    (I.r x.1 i + (if 1 < (x.2.2.2.2.2 : ℕ) then V I y i (t + (x.2.2.2.2.2 : ℕ)) -
                      V I y i (t + 1) else 0)) else 0) := by
                intro x
                by_cases hx : x.2.2.2.2.1 = some i
                · simp only [hx, if_true]; ring
                · simp only [hx, if_false]; ring
              rw [Finset.sum_congr rfl (fun x _ => e1 x), Finset.sum_add_distrib, ← Finset.sum_mul,
                hw1 t ht, one_mul,
                hwm t ht _ i (fun z d => I.r z i + (if 1 < d then V I y i (t + d) - V I y i (t + 1) else 0))]
              have e2 : ∀ z, ∑ d ∈ Finset.Icc 1 T, I.g z i d *
                  (I.r z i + (if 1 < d then V I y i (t + d) - V I y i (t + 1) else 0)) =
                  I.r z i - P I y i t z := by
                intro z
                have : ∀ d ∈ Finset.Icc 1 T, I.g z i d *
                  (I.r z i + (if 1 < d then V I y i (t + d) - V I y i (t + 1) else 0)) =
                  I.g z i d * (I.r z i - V I y i (t + 1)) + I.g z i d * V I y i (t + d) := by
                  intro d hd
                  rw [Finset.mem_Icc] at hd
                  split_ifs with h1
                  · ring
                  · have : d = 1 := by omega
                    subst this; ring
                rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.sum_mul, hI.g_sum]
                unfold P; ring
              simp only [e2]
              have hcast : ∑ s ∈ Finset.Ioc t (t + T), (J i s : ℝ) * (V I y i s - V I y i t) =
                  ∑ s ∈ Finset.Ioc t (t + T), (J i s : ℝ) * (V I y i s - V I y i (t + 1)) -
                  ((∑ s ∈ Finset.Ioc t (t + T), J i s : ℕ) : ℝ) * (D i t / I.c i) := by
                push_cast
                rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro s _
                rw [hVrec i t ht]; ring
              rw [hcast, hVrec i t ht]
              have hDn := hD0 i t ht
              have hc := hcpos i
              have hcD : (I.c i : ℝ) * (D i t / I.c i) = D i t := by field_simp
              by_cases hh : I.c i - ∑ s ∈ Finset.Ioc t (t + T), J i s = 0
              · have hz : ∑ z, ∑ S ∈ I.feas, I.F t z * y t z S * (act (ψr (alg3 I y)) t J z i *
                    I.phi z S i * (I.r z i - P I y i t z)) = 0 := by
                  refine Finset.sum_eq_zero fun z _ => Finset.sum_eq_zero fun S _ => ?_
                  rw [hact, if_pos hh]; ring
                rw [hz]
                have h1 : (I.c i : ℝ) ≤ ((∑ s ∈ Finset.Ioc t (t + T), J i s : ℕ) : ℝ) := by
                  exact_mod_cast Nat.sub_eq_zero_iff_le.mp hh
                have h2 := mul_le_mul_of_nonneg_right h1 (div_nonneg hDn (by linarith : (0:ℝ) ≤ I.c i))
                linarith
              · have hz : ∑ z, ∑ S ∈ I.feas, I.F t z * y t z S * (act (ψr (alg3 I y)) t J z i *
                    I.phi z S i * (I.r z i - P I y i t z)) = D i t := by
                  rw [hD]
                  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun S _ => ?_
                  rw [hact, if_neg hh, hψr, hkeep3]
                  split_ifs with hp
                  · rw [max_eq_left (by linarith)]; ring
                  · rw [max_eq_right (by linarith)]; ring
                rw [hz]
                have h2 : 0 ≤ ((∑ s ∈ Finset.Ioc t (t + T), J i s : ℕ) : ℝ) * (D i t / I.c i) :=
                  mul_nonneg (Nat.cast_nonneg _) (div_nonneg hDn (by linarith))
                linarith
          have hPform : ∀ i t z, P I y i t z = ∑ s ∈ Finset.Icc 1 T, if t < s then
              Gbar I z i (s - t) * (V I y i s - V I y i (s + 1)) else 0 := by
            intro i t z
            have htel : ∀ d, 1 ≤ d → V I y i (t + 1) - V I y i (t + d) =
                ∑ s ∈ Finset.Icc 1 T, if t < s ∧ s < t + d then V I y i s - V I y i (s + 1) else 0 := by
              intro d hd
              induction d, hd using Nat.le_induction with
              | base =>
                rw [sub_self, Finset.sum_eq_zero]
                intro s _; rw [if_neg (by omega)]
              | succ d hd ih =>
                have e : ∀ s ∈ Finset.Icc 1 T,
                    (if t < s ∧ s < t + (d + 1) then V I y i s - V I y i (s + 1) else 0) =
                    (if t < s ∧ s < t + d then V I y i s - V I y i (s + 1) else 0) +
                    (if t + d = s then V I y i s - V I y i (s + 1) else 0) := by
                  intro s _
                  by_cases h1 : t + d = s
                  · rw [if_pos (by omega), if_neg (by omega), if_pos h1, zero_add]
                  · rw [if_neg h1, add_zero]
                    apply if_congr _ rfl rfl
                    omega
                rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← ih, Finset.sum_ite_eq]
                split_ifs with h1
                · rw [show t + (d + 1) = t + d + 1 by ring]; ring
                · rw [Finset.mem_Icc] at h1
                  rw [hV0 i (t + d) (by omega), hV0 i (t + (d + 1)) (by omega)]; ring
            unfold P
            have e1 : V I y i (t + 1) - ∑ d ∈ Finset.Icc 1 T, I.g z i d * V I y i (t + d) =
                ∑ d ∈ Finset.Icc 1 T, I.g z i d * (V I y i (t + 1) - V I y i (t + d)) := by
              simp only [mul_sub, Finset.sum_sub_distrib]
              rw [← Finset.sum_mul, hI.g_sum, one_mul]
            rw [e1]
            have e2 : ∀ d ∈ Finset.Icc 1 T, I.g z i d * (V I y i (t + 1) - V I y i (t + d)) =
                ∑ s ∈ Finset.Icc 1 T, if t < s ∧ s < t + d then
                  I.g z i d * (V I y i s - V I y i (s + 1)) else 0 := by
              intro d hd
              rw [Finset.mem_Icc] at hd
              rw [htel d hd.1, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s _
              rw [mul_ite, mul_zero]
            rw [Finset.sum_congr rfl e2, Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro s _
            split_ifs with hs
            · unfold Gbar
              rw [Finset.sum_filter, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro d _
              by_cases h1 : s - t < d
              · rw [if_pos (by omega), if_pos h1]
              · rw [if_neg (by omega), if_neg h1, zero_mul]
            · apply Finset.sum_eq_zero
              intro d _
              rw [if_neg (by tauto)]
          have hGn : ∀ z i k, 0 ≤ Gbar I z i k := by
            intro z i k; unfold Gbar; exact Finset.sum_nonneg fun d _ => hI.g_nonneg z i d
          -- the LP capacity constraint
          have hcap : ∀ i, ∀ s ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T, (if t < s then
              ∑ z, ∑ S ∈ I.feas, I.F t z * Gbar I z i (s - t) * I.phi z S i * y t z S else 0) ≤ I.c i := by
            intro i s hs
            have hs' := Finset.mem_Icc.mp hs
            refine le_trans ?_ (hy.1.2.1 i s hs)
            rw [← Finset.sum_filter]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro t ht
              rw [Finset.mem_filter, Finset.mem_Icc] at ht
              rw [Finset.mem_Icc]; omega
            · intro t ht _
              rw [Finset.mem_Icc] at ht
              refine Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun S hS => ?_
              exact mul_nonneg (mul_nonneg (mul_nonneg (hI.F_nonneg t z) (hGn z i _))
                (hI.phi_nonneg z S hS i)) (hy.1.1 t (by rw [Finset.mem_Icc]; omega) z S hS)
          have hVtel : ∀ i, ∑ s ∈ Finset.Icc 1 T, (V I y i s - V I y i (s + 1)) = V I y i 1 := by
            intro i
            have h : ∀ N, ∑ s ∈ Finset.Icc 1 N, (V I y i s - V I y i (s + 1)) = V I y i 1 - V I y i (N + 1) := by
              intro N
              induction N with
              | zero => simp
              | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring
            rw [h T, hV0 i (T + 1) (by omega), sub_zero]
          have hdn : ∀ i, ∀ s ∈ Finset.Icc 1 T, (I.c i : ℝ) * (V I y i s - V I y i (s + 1)) = D i s := by
            intro i s hs
            have := hcpos i
            rw [hVrec i s hs]; field_simp; ring
          have hhalf : ∀ i, contrib I y i ≤ 2 * ((I.c i : ℝ) * V I y i 1) := by
            intro i
            have h1 : contrib I y i ≤ ∑ t ∈ Finset.Icc 1 T, (D i t +
                ∑ z, ∑ S ∈ I.feas, I.F t z * y t z S * I.phi z S i * P I y i t z) := by
              unfold contrib
              apply Finset.sum_le_sum
              intro t ht
              rw [hD, ← Finset.sum_add_distrib]
              apply Finset.sum_le_sum
              intro z _
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_le_sum
              intro S hS
              have hn : 0 ≤ I.F t z * y t z S * I.phi z S i :=
                mul_nonneg (mul_nonneg (hI.F_nonneg t z) (hy.1.1 t ht z S hS)) (hI.phi_nonneg z S hS i)
              have hm := mul_le_mul_of_nonneg_left (le_max_left (I.r z i - P I y i t z) 0) hn
              nlinarith
            have h2 : ∑ t ∈ Finset.Icc 1 T, D i t = I.c i * V I y i 1 := by
              rw [← hVtel i, Finset.mul_sum]
              exact Finset.sum_congr rfl fun s hs => (hdn i s hs).symm
            have h3 : ∑ t ∈ Finset.Icc 1 T, ∑ z, ∑ S ∈ I.feas, I.F t z * y t z S * I.phi z S i * P I y i t z
                = ∑ s ∈ Finset.Icc 1 T, (V I y i s - V I y i (s + 1)) *
                  ∑ t ∈ Finset.Icc 1 T, (if t < s then
              ∑ z, ∑ S ∈ I.feas, I.F t z * Gbar I z i (s - t) * I.phi z S i * y t z S else 0) := by
              simp only [hPform, Finset.mul_sum]
              rw [Finset.sum_comm (s := Finset.Icc 1 T) (t := Finset.Icc 1 T)]
              apply Finset.sum_congr rfl
              intro t _
              rw [Finset.sum_congr rfl (fun z _ => Finset.sum_comm), Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro s _
              split_ifs with hs
              · rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro z _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro S _
                ring
              · simp
            have h4 : ∑ s ∈ Finset.Icc 1 T, (V I y i s - V I y i (s + 1)) *
                  ∑ t ∈ Finset.Icc 1 T, (if t < s then
              ∑ z, ∑ S ∈ I.feas, I.F t z * Gbar I z i (s - t) * I.phi z S i * y t z S else 0)
                ≤ I.c i * V I y i 1 := by
              rw [← hVtel i, Finset.mul_sum]
              apply Finset.sum_le_sum
              intro s hs
              rw [mul_comm]
              apply mul_le_mul_of_nonneg_right (hcap i s hs)
              have := hdn i s hs
              have hc := hcpos i
              have := hD0 i s hs
              by_contra hneg
              push Not at hneg
              nlinarith
            rw [Finset.sum_add_distrib, h2, h3] at h1
            linarith
          have hLPc : lpObj I y = ∑ i, contrib I y i := by
            unfold lpObj contrib
            symm
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro t _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro z _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro S _
            apply Finset.sum_congr rfl
            intro i _
            ring
          have hT2 : (1 / 2 : ℝ) * lpObj I y ≤ expRev I y (alg3 I y) 1 (fun _ _ => 0) := by
            rw [hER, hLPc, Finset.mul_sum]
            apply Finset.sum_le_sum
            intro i _
            linarith [hA3 i, hhalf i]
          clear hA3 hhalf hVtel hdn hPform hD0 hV0 hVrec hψ3 hkeep3 hk301
          have hVn : ∀ i, 0 ≤ Val (ψr (alg2 γ)) 1 (fun _ _ => 0) i := by
            intro i
            refine hPot (ψr (alg2 γ)) hψ2 i (fun _ _ => 0) (fun _ => le_rfl) ?_ _ 1 (fun _ _ => 0) rfl
              (by rw [Finset.mem_Icc]; omega) (by rw [hwin]; intros; rfl)
            intro t J ht h
            refine Finset.sum_nonneg fun x _ => ?_
            refine mul_nonneg (hw0 t ht _ (hact01 _ hψ2 t J) x) ?_
            split_ifs
            · linarith [hI.r_nonneg x.1 i]
            · norm_num
          obtain ⟨q, hq⟩ : ∃ q : Fin n → ℕ → ℝ, ∀ i t, q i t = ∑ z, ∑ S ∈ I.feas,
              I.F t z * y t z S * (I.phi z S i * I.r z i) := ⟨_, fun _ _ => rfl⟩
          have hFyn : ∀ t ∈ Finset.Icc 1 T, ∀ z, ∀ S ∈ I.feas, 0 ≤ I.F t z * y t z S :=
            fun t ht z S hS => mul_nonneg (hI.F_nonneg t z) (hy.1.1 t ht z S hS)
          have hqn : ∀ i, ∀ t ∈ Finset.Icc 1 T, 0 ≤ q i t := by
            intro i t ht
            rw [hq]
            refine Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun S hS => ?_
            exact mul_nonneg (hFyn t ht z S hS) (mul_nonneg (hI.phi_nonneg z S hS i) (hI.r_nonneg z i))
          have hcontq : ∀ i, contrib I y i = ∑ t ∈ Finset.Icc 1 T, q i t := by
            intro i
            unfold contrib
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [hq]
            refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun S _ => ?_
            ring
          obtain ⟨b, hb⟩ : ∃ b : Fin n → ℕ → ℕ → ℝ, ∀ i t s, b i t s = ∑ z, ∑ S ∈ I.feas,
              I.F t z * y t z S * (I.phi z S i * Gbar I z i (s - t)) := ⟨_, fun _ _ _ => rfl⟩
          have hbn : ∀ i, ∀ t ∈ Finset.Icc 1 T, ∀ s, 0 ≤ b i t s := by
            intro i t ht s
            rw [hb]
            refine Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun S hS => ?_
            exact mul_nonneg (hFyn t ht z S hS) (mul_nonneg (hI.phi_nonneg z S hS i) (hGn z i _))
          have hbcap : ∀ i, ∀ s ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Ico 1 s, b i t s ≤ I.c i := by
            intro i s hs
            have hs' := Finset.mem_Icc.mp hs
            refine le_trans (le_of_eq ?_) (hcap i s hs)
            rw [← Finset.sum_filter]
            have e : (Finset.Icc 1 T).filter (fun t => t < s) = Finset.Ico 1 s := by
              ext t; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]; omega
            rw [e]
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [hb]
            refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun S _ => ?_
            ring
          have hA2 : γ < 1 → ∀ i, ∑ s ∈ Finset.Icc 1 T, (1 - γ) * q i s *
              (1 - (1 - γ) ^ (I.c i) * Real.exp (γ * I.c i)) ≤ Val (ψr (alg2 γ)) 1 (fun _ _ => 0) i := by
            intro hγ1 i
            have hg0 : 0 < 1 - γ := by linarith
            obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (1 - γ)⁻¹ := ⟨_, rfl⟩
            have hθ1 : 1 ≤ θ := by rw [hθ]; exact (one_le_inv₀ hg0).mpr (by linarith)
            have hθ0 : 0 < θ := by linarith
            have hθg : θ * (1 - γ) = 1 := by rw [hθ]; field_simp
            have hθg1 : (θ - 1) * (1 - γ) = γ := by linarith
            obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → ℕ → (ℕ → ℕ) → ℝ, ∀ s t j, Φ s t j =
                θ ^ (∑ r ∈ Finset.Ioc t (t + T), if s < r then j r else 0) * (1 - γ) ^ (I.c i) *
                  Real.exp (∑ τ ∈ Finset.Ico t s, γ * b i τ s) := ⟨_, fun _ _ _ => rfl⟩
            have hΦ0 : ∀ s t j, 0 ≤ Φ s t j := by
              intro s t j; rw [hΦ]; positivity
            have := hPot (ψr (alg2 γ)) hψ2 i
              (fun t j => ∑ s ∈ Finset.Icc t T, (1 - γ) * q i s * (1 - Φ s t j))
              ?_ ?_ _ 1 (fun _ _ => 0) rfl (by rw [Finset.mem_Icc]; omega) (by rw [hwin]; intros; rfl)
            · refine le_trans ?_ this
              apply Finset.sum_le_sum
              intro s hs
              apply mul_le_mul_of_nonneg_left _ (mul_nonneg hg0.le (hqn i s hs))
              have e : Φ s 1 (fun _ => 0) ≤ (1 - γ) ^ (I.c i) * Real.exp (γ * I.c i) := by
                rw [hΦ]
                simp only [ite_self, Finset.sum_const_zero, pow_zero, one_mul]
                apply mul_le_mul_of_nonneg_left _ (pow_nonneg hg0.le _)
                apply Real.exp_le_exp.mpr
                rw [← Finset.mul_sum]
                exact mul_le_mul_of_nonneg_left (hbcap i s hs) hγ01.1
              linarith
            · intro j
              rw [Finset.Icc_eq_empty (by omega)]; simp
            · intro t J ht h
              have ht' := Finset.mem_Icc.mp ht
              have hwn := hw0 t ht _ (hact01 _ hψ2 t J)
              -- reward part
              have hrew : (1 - γ) * q i t * (1 - Φ t t (J i)) ≤
                  ∑ x, w t (act (ψr (alg2 γ)) t J) x * (if x.2.2.2.2.1 = some i then I.r x.1 i else 0) := by
                rw [hwm t ht _ i (fun z _ => I.r z i)]
                simp only [← Finset.sum_mul, hI.g_sum, one_mul]
                by_cases hh : I.c i - ∑ s ∈ Finset.Ioc t (t + T), J i s = 0
                · have hz : ∑ z, ∑ S ∈ I.feas, I.F t z * y t z S * (act (ψr (alg2 γ)) t J z i *
                      I.phi z S i * I.r z i) = 0 := by
                    refine Finset.sum_eq_zero fun z _ => Finset.sum_eq_zero fun S _ => ?_
                    rw [hact, if_pos hh]; ring
                  rw [hz]
                  have h1 : 1 ≤ Φ t t (J i) := by
                    rw [hΦ]
                    simp only [Finset.Ico_self, Finset.sum_empty, Real.exp_zero, mul_one]
                    have e : ∑ r ∈ Finset.Ioc t (t + T), (if t < r then J i r else 0) =
                        ∑ s ∈ Finset.Ioc t (t + T), J i s := by
                      refine Finset.sum_congr rfl fun s hs => ?_
                      rw [if_pos (Finset.mem_Ioc.mp hs).1]
                    rw [e]
                    calc (1:ℝ) = θ ^ (I.c i) * (1 - γ) ^ (I.c i) := by rw [← mul_pow, hθg, one_pow]
                      _ ≤ _ := by
                        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hg0.le _)
                        exact pow_le_pow_right₀ hθ1 (Nat.sub_eq_zero_iff_le.mp hh)
                  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hg0.le (hqn i t ht)) (by linarith)
                · have hz : ∑ z, ∑ S ∈ I.feas, I.F t z * y t z S * (act (ψr (alg2 γ)) t J z i *
                      I.phi z S i * I.r z i) = (1 - γ) * q i t := by
                    rw [hq, Finset.mul_sum]
                    refine Finset.sum_congr rfl fun z _ => ?_
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl fun S _ => ?_
                    rw [hact, if_neg hh, hψr, hkeep2]; ring
                  rw [hz]
                  have := mul_nonneg (mul_nonneg hg0.le (hqn i t ht)) (hΦ0 t t (J i))
                  linarith
              -- supermartingale part
              have hsup : ∀ s ∈ Finset.Icc (t + 1) T,
                  ∑ x, w t (act (ψr (alg2 γ)) t J) x * Φ s (t + 1) (nx t J x i) ≤ Φ s t (J i) := by
                intro s hs
                have hs' := Finset.mem_Icc.mp hs
                have hout : ∀ x : Step n T Z,
                    ∑ r ∈ Finset.Ioc (t + 1) (t + 1 + T), (if s < r then nx t J x i r else 0) =
                    ∑ r ∈ Finset.Ioc t (t + T), (if s < r then J i r else 0) +
                      (if x.2.2.2.2.1 = some i then (if s < t + (x.2.2.2.2.2 : ℕ) then 1 else 0) else 0) := by
                  intro x
                  have hl := hlin t J x i (fun r => if s < r then 1 else 0) (by omega) h
                    (by rw [if_neg (by omega)])
                  have : ((∑ r ∈ Finset.Ioc (t + 1) (t + 1 + T), (if s < r then nx t J x i r else 0) : ℕ) : ℝ) =
                    ((∑ r ∈ Finset.Ioc t (t + T), (if s < r then J i r else 0) +
                      (if x.2.2.2.2.1 = some i then (if s < t + (x.2.2.2.2.2 : ℕ) then 1 else 0) else 0) : ℕ) : ℝ) := by
                    push_cast
                    simp only [mul_ite, mul_one, mul_zero] at hl
                    rw [hl]
                    congr 1
                    by_cases h1 : x.2.2.2.2.1 = some i
                    · rw [if_pos h1, if_pos h1]
                      by_cases h2 : 1 < (x.2.2.2.2.2 : ℕ)
                      · rw [if_pos h2]
                      · rw [if_neg h2, if_neg (by omega)]
                    · rw [if_neg h1, if_neg h1]
                  exact_mod_cast this
                obtain ⟨K, hK⟩ : ∃ K : ℝ, K = θ ^ (∑ r ∈ Finset.Ioc t (t + T), if s < r then J i r else 0) *
                  (1 - γ) ^ (I.c i) * Real.exp (∑ τ ∈ Finset.Ico (t + 1) s, γ * b i τ s) := ⟨_, rfl⟩
                have hK0 : 0 ≤ K := by rw [hK]; positivity
                have e1 : ∀ x : Step n T Z, w t (act (ψr (alg2 γ)) t J) x * Φ s (t + 1) (nx t J x i) =
                    K * (w t (act (ψr (alg2 γ)) t J) x + w t (act (ψr (alg2 γ)) t J) x *
                      (if x.2.2.2.2.1 = some i then (if s < t + (x.2.2.2.2.2 : ℕ) then θ - 1 else 0) else 0)) := by
                  intro x
                  rw [hΦ, hout, pow_add, hK]
                  by_cases h1 : x.2.2.2.2.1 = some i
                  · by_cases h2 : s < t + (x.2.2.2.2.2 : ℕ)
                    · simp only [h1, h2, if_true, pow_one]; ring
                    · simp only [h1, h2, if_true, if_false, pow_zero]; ring
                  · simp only [h1, if_false, pow_zero]; ring
                rw [Finset.sum_congr rfl (fun x _ => e1 x), ← Finset.mul_sum, Finset.sum_add_distrib,
                  hw1 t ht, hwm t ht _ i (fun z d => if s < t + d then θ - 1 else 0)]
                have e2 : ∀ z, ∑ d ∈ Finset.Icc 1 T, I.g z i d * (if s < t + d then θ - 1 else 0) =
                    (θ - 1) * Gbar I z i (s - t) := by
                  intro z
                  unfold Gbar
                  rw [Finset.sum_filter, Finset.mul_sum]
                  refine Finset.sum_congr rfl fun d _ => ?_
                  by_cases h2 : s < t + d
                  · rw [if_pos h2, if_pos (by omega)]; ring
                  · rw [if_neg h2, if_neg (by omega)]; ring
                simp only [e2]
                have e3 : ∑ z, ∑ S ∈ I.feas, I.F t z * y t z S * (act (ψr (alg2 γ)) t J z i * I.phi z S i *
                    ((θ - 1) * Gbar I z i (s - t))) ≤ γ * b i t s := by
                  rw [hb, Finset.mul_sum]
                  refine Finset.sum_le_sum fun z _ => ?_
                  rw [Finset.mul_sum]
                  refine Finset.sum_le_sum fun S hS => ?_
                  have ha : act (ψr (alg2 γ)) t J z i ≤ 1 - γ := by
                    rw [hact]; split_ifs
                    · exact hg0.le
                    · rw [hψr, hkeep2]
                  have hn : 0 ≤ I.F t z * y t z S * (I.phi z S i * ((θ - 1) * Gbar I z i (s - t))) :=
                    mul_nonneg (hFyn t ht z S hS) (mul_nonneg (hI.phi_nonneg z S hS i)
                      (mul_nonneg (by linarith) (hGn z i _)))
                  calc I.F t z * y t z S * (act (ψr (alg2 γ)) t J z i * I.phi z S i *
                      ((θ - 1) * Gbar I z i (s - t)))
                      = act (ψr (alg2 γ)) t J z i *
                        (I.F t z * y t z S * (I.phi z S i * ((θ - 1) * Gbar I z i (s - t)))) := by ring
                    _ ≤ (1 - γ) * (I.F t z * y t z S * (I.phi z S i * ((θ - 1) * Gbar I z i (s - t)))) :=
                        mul_le_mul_of_nonneg_right ha hn
                    _ = ((θ - 1) * (1 - γ)) * (I.F t z * y t z S * (I.phi z S i * Gbar I z i (s - t))) := by ring
                    _ = _ := by rw [hθg1]
                calc K * (1 + ∑ z, ∑ S ∈ I.feas, I.F t z * y t z S * (act (ψr (alg2 γ)) t J z i * I.phi z S i *
                    ((θ - 1) * Gbar I z i (s - t)))) ≤ K * Real.exp (γ * b i t s) := by
                      apply mul_le_mul_of_nonneg_left _ hK0
                      linarith [Real.add_one_le_exp (γ * b i t s)]
                  _ = Φ s t (J i) := by
                      rw [hΦ, hK, mul_assoc _ _ (Real.exp (γ * b i t s)), ← Real.exp_add,
                        Finset.sum_eq_sum_Ico_succ_bot (show t < s by omega), add_comm (γ * b i t s)]
              have e5 : ∑ x, w t (act (ψr (alg2 γ)) t J) x * ((if x.2.2.2.2.1 = some i then I.r x.1 i else 0) +
                  ∑ s ∈ Finset.Icc (t + 1) T, (1 - γ) * q i s * (1 - Φ s (t + 1) (nx t J x i))) =
                  ∑ x, w t (act (ψr (alg2 γ)) t J) x * (if x.2.2.2.2.1 = some i then I.r x.1 i else 0) +
                  ∑ s ∈ Finset.Icc (t + 1) T, (1 - γ) * q i s *
                    (1 - ∑ x, w t (act (ψr (alg2 γ)) t J) x * Φ s (t + 1) (nx t J x i)) := by
                simp only [mul_add, Finset.sum_add_distrib]
                congr 1
                simp only [Finset.mul_sum]
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun s _ => ?_
                rw [← hw1 t ht (act (ψr (alg2 γ)) t J), ← Finset.sum_sub_distrib, Finset.mul_sum]
                refine Finset.sum_congr rfl fun x _ => ?_
                rw [hw1 t ht]
                ring
              rw [e5]
              have e6 : ∑ s ∈ Finset.Icc t T, (1 - γ) * q i s * (1 - Φ s t (J i)) =
                  (1 - γ) * q i t * (1 - Φ t t (J i)) +
                  ∑ s ∈ Finset.Icc (t + 1) T, (1 - γ) * q i s * (1 - Φ s t (J i)) := by
                rw [← Finset.insert_Icc_add_one_left_eq_Icc ht'.2, Finset.sum_insert (by simp)]
              rw [e6]
              refine add_le_add hrew (Finset.sum_le_sum fun s hs => ?_)
              have hs' := Finset.mem_Icc.mp hs
              apply mul_le_mul_of_nonneg_left _ (mul_nonneg hg0.le (hqn i s (by rw [Finset.mem_Icc]; omega)))
              linarith [hsup s hs]
          -- scalar bound
          have hsc : γ < 1 → ∀ c : ℕ, (1 - γ) ^ c * Real.exp (γ * c) ≤
              Real.exp (-(γ ^ 2 * c / (2 - γ))) := by
            intro hγ1 c
            have hg0 : 0 < 1 - γ := by linarith
            have hlog : Real.log (1 - γ) + γ ≤ -(γ ^ 2 / (2 - γ)) := by
              have hl := Real.le_log_one_add_of_nonneg (x := γ / (1 - γ)) (div_nonneg hγ01.1 hg0.le)
              have e1 : 1 + γ / (1 - γ) = (1 - γ)⁻¹ := by field_simp; ring
              rw [e1, Real.log_inv] at hl
              have h2 : (0:ℝ) < 2 - γ := by linarith
              have e2 : 2 * (γ / (1 - γ)) / (γ / (1 - γ) + 2) = γ + γ ^ 2 / (2 - γ) := by
                have : γ / (1 - γ) + 2 = (2 - γ) / (1 - γ) := by field_simp; ring
                rw [this]; field_simp; ring
              rw [e2] at hl
              linarith
            have e : (1 - γ) ^ c = Real.exp (c * Real.log (1 - γ)) := by
              rw [mul_comm, Real.exp_mul, Real.exp_log hg0, Real.rpow_natCast]
            rw [e, ← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) c)
            calc (c : ℝ) * Real.log (1 - γ) + γ * c = c * (Real.log (1 - γ) + γ) := by ring
              _ ≤ c * -(γ ^ 2 / (2 - γ)) := this
              _ = _ := by ring
          have hT1 : (1 - epsStar (cmin I : ℝ)) * lpObj I y ≤ expRev I y (alg2 γ) 1 (fun _ _ => 0) := by
            rw [hER, ← hγ.2]
            rcases eq_or_lt_of_le hγ01.2 with h1 | h1
            · have : hfun γ (cmin I : ℝ) = 1 := by unfold hfun; rw [h1]; ring
              rw [this, sub_self, zero_mul]
              exact Finset.sum_nonneg fun i _ => hVn i
            · rw [hLPc, Finset.mul_sum]
              apply Finset.sum_le_sum
              intro i _
              refine le_trans ?_ (hA2 h1 i)
              rw [hcontq, Finset.mul_sum]
              apply Finset.sum_le_sum
              intro s hs
              have hcm : (cmin I : ℝ) ≤ I.c i := by
                have : cmin I ≤ I.c i := Finset.inf'_le _ (Finset.mem_univ i)
                exact_mod_cast this
              have h2 : Real.exp (-(γ ^ 2 * (I.c i : ℝ) / (2 - γ))) ≤
                  Real.exp (-(γ ^ 2 * (cmin I : ℝ) / (2 - γ))) := by
                apply Real.exp_le_exp.mpr
                apply neg_le_neg
                apply div_le_div_of_nonneg_right _ (by linarith)
                exact mul_le_mul_of_nonneg_left hcm (sq_nonneg _)
              have h3 := hsc h1 (I.c i)
              have h4 : 0 ≤ (1 - γ) * q i s := mul_nonneg (by linarith) (hqn i s hs)
              unfold hfun
              calc (1 - (1 - (1 - γ) * (1 - Real.exp (-(γ ^ 2 * (cmin I : ℝ) / (2 - γ)))))) * q i s
                  = (1 - γ) * q i s * (1 - Real.exp (-(γ ^ 2 * (cmin I : ℝ) / (2 - γ)))) := by ring
                _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) h4
          refine ⟨?_, hii'⟩
          have hJ0 : ValidStart I 1 (fun _ _ => 0) := ⟨fun _ _ _ => rfl, fun _ => by simp⟩
          have hfin := hii' 1 (by rw [Finset.mem_Icc]; omega) (fun _ _ => 0) hJ0
          unfold expRevHybridII
          have hfa := le_trans (le_max_left _ _) hfin
          have hfb := le_trans (le_max_right _ _) hfin
          rcases le_total (1/2 : ℝ) (epsStar (cmin I : ℝ)) with hmin | hmin
          · rw [min_eq_left hmin]
            linarith
          · rw [min_eq_right hmin]
            linarith
