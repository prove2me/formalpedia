-- Prove2me | solution 1 for SchedComplexity.Partition.Supplement.theorem_1d
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:37:49.664794+00:00
-- url     : https://prove2.me/submissions/9391e94f-4537-473f-b1b3-23f92cb24000

import Mathlib
import Definitions.Def_SchedComplexity_Partition_Supplement_Family

open SchedComplexity
open SchedComplexity.Partition
open SchedComplexity.Partition.Supplement

open CookPvsNP ProjSchedTW.Complexity

theorem solution (k : Criterion) :
    PolyReducible (language (.fixed 2) .flow ∅ k) (language (.fixed 2) .permutation ∅ k) ∧
    PolyReducible (language (.fixed 2) .permutation ∅ k) (language (.fixed 2) .flow ∅ k) := by
      have hid : PolyTimeComputable (fun x : List BSym => x) := by
        let M : TM BSym :=
          { Q := Bool, q₀ := true, qaccept := true, qreject := false,
            accept_ne_reject := by decide, δ := fun q s => (q, s, Move.right) }
        refine ⟨BSym, inferInstance, Function.Embedding.refl _, Function.Embedding.refl _, M, 0, ?_⟩
        intro x
        have hhalt : ∀ w, M.IsHalting (M.init w) := fun w => Or.inl rfl
        have hrun : ∀ t w, M.run t (M.init w) = M.init w := by
          intro t w
          exact Function.iterate_fixed (by simp [TM.step, hhalt w]) t
        refine ⟨?_, ?_⟩
        · unfold TM.HaltsWithin; rw [hrun]; exact hhalt _
        · rw [hrun]
          cases x with
          | nil => simp [TM.output, TM.init]
          | cons a t =>
            simp [TM.output, TM.init]
            apply (show ∀ y ∈ ((List.map (some ∘ ⇑(Function.Embedding.refl BSym)) t).reverse ++ [some a]),
              y ≠ none by simp; rintro y (⟨b, -, rfl⟩ | rfl) <;> simp)
            exact List.getElem_mem _
      have hcore : ∀ {n : ℕ} (Q : SchedComplexity.Shops.ShopInstance n 2),
            (∀ j, (Q.ops j).map Prod.fst = List.ofFn (fun i : Fin 2 => i)) →
            (∀ j, Q.release j = 0) → Q.prec = ∅ → ∀ S, Q.IsFeasible S →
            ∃ S', Q.IsFeasible S' ∧ CommonOrder Q S' ∧ ∀ j, Q.completion S' j ≤ Q.completion S j := by
        intro n Q hflow hrel0 hprec S hS
        obtain ⟨-, hchain, hdisj, -⟩ := hS
        have hlen : ∀ j, (Q.ops j).length = 2 := fun j => by
          simpa using congrArg List.length (hflow j)
        have hmach : ∀ o : Q.Op, (Q.mach o).val = o.2.val := by
          intro o
          have h1 := congrArg (fun L => L[o.2.val]?) (hflow o.1)
          have h2 : o.2.val < 2 := by have := hlen o.1; have := o.2.isLt; omega
          simp only [List.getElem?_map, List.getElem?_ofFn] at h1
          rw [List.getElem?_eq_getElem o.2.2] at h1
          simp [h2] at h1
          simp [SchedComplexity.Shops.ShopInstance.mach, h1]
        let op0 : Fin n → Q.Op := fun j => ⟨j, ⟨0, by rw [hlen]; norm_num⟩⟩
        let op1 : Fin n → Q.Op := fun j => ⟨j, ⟨1, by rw [hlen]; norm_num⟩⟩
        have hop : ∀ o : Q.Op, o = op0 o.1 ∨ o = op1 o.1 := by
          rintro ⟨j, r⟩
          have : r.val < 2 := by have := hlen j; have := r.isLt; omega
          rcases (show r.val = 0 ∨ r.val = 1 by omega) with h | h
          · left; simp only [op0]; congr 1; exact Fin.ext h
          · right; simp only [op1]; congr 1; exact Fin.ext h
        have hv0 : ∀ j, (op0 j).2.val = 0 := fun j => rfl
        have hv1 : ∀ j, (op1 j).2.val = 1 := fun j => rfl
        let p1 : Fin n → ℕ := fun j => Q.proc (op0 j)
        let key : Fin n → ℕ := fun j => 2 * S (op1 j) + Q.proc (op1 j)
        let π := Tuple.sort key
        have hmono : ∀ c d : Fin n, c ≤ d → key (π c) ≤ key (π d) :=
          fun c d h => Tuple.monotone_sort key h
        have hm2 : ∀ i j : Fin n, i ≠ j → key i ≤ key j → S (op1 i) + Q.proc (op1 i) ≤ S (op1 j) := by
          intro i j hij hk
          have hne : op1 i ≠ op1 j := by
            intro h; apply hij; exact congrArg Sigma.fst h
          have hm : Q.mach (op1 i) = Q.mach (op1 j) := Fin.ext (by rw [hmach, hmach])
          rcases hdisj _ _ hne hm with h | h
          · exact h
          · simp only [key] at hk; omega
        have hm2' : ∀ i j : Fin n, key i ≤ key j → S (op1 i) ≤ S (op1 j) := by
          intro i j hk
          by_cases hij : i = j
          · subst hij; exact le_refl _
          · have := hm2 i j hij hk; omega
        have hch : ∀ i, S (op0 i) + p1 i ≤ S (op1 i) := fun i => hchain i _ _ rfl
        let T : Fin n → Finset (Fin n) := fun j =>
          insert (π.symm j) (Finset.univ.filter (· < π.symm j))
        have hsum : ∀ j, ∑ c ∈ T j, p1 (π c) ≤ S (op1 j) := by
          intro j
          let I : Fin n → Finset ℕ := fun c => Finset.Ico (S (op0 (π c))) (S (op0 (π c)) + p1 (π c))
          have hcard : ∑ c ∈ T j, p1 (π c) = ((T j).biUnion I).card := by
            rw [Finset.card_biUnion]
            · simp [I]
            · intro c _ c' _ hcc
              have hne : op0 (π c) ≠ op0 (π c') := by
                intro h; apply hcc; exact π.injective (congrArg Sigma.fst h)
              have hm : Q.mach (op0 (π c)) = Q.mach (op0 (π c')) := Fin.ext (by rw [hmach, hmach])
              have hd := hdisj _ _ hne hm
              rw [Function.onFun, Finset.disjoint_left]
              intro x hx hx'
              simp only [I, Finset.mem_Ico] at hx hx'
              simp only [p1] at hx hx'
              omega
          rw [hcard]
          have hsub : (T j).biUnion I ⊆ Finset.range (S (op1 j)) := by
            intro x hx
            simp only [Finset.mem_biUnion] at hx
            obtain ⟨c, hc, hx⟩ := hx
            have hcle : c ≤ π.symm j := by
              simp only [T, Finset.mem_insert, Finset.mem_filter] at hc
              rcases hc with h | h
              · exact h.le
              · exact h.2.le
            have hk := hmono _ _ hcle
            rw [Equiv.apply_symm_apply] at hk
            have h1 := hm2' _ _ hk
            have h2 := hch (π c)
            simp only [I, Finset.mem_Ico] at hx
            simp only [Finset.mem_range]
            omega
          simpa using Finset.card_le_card hsub
        let S' : Q.Op → ℕ := fun o =>
          if o.2.val = 0 then ∑ c ∈ Finset.univ.filter (· < π.symm o.1), p1 (π c) else S o
        have hS'0 : ∀ j, S' (op0 j) = ∑ c ∈ Finset.univ.filter (· < π.symm j), p1 (π c) := by
          intro j; simp only [S', hv0, if_true]; rfl
        have hS'1 : ∀ j, S' (op1 j) = S (op1 j) := by
          intro j; simp [S', hv1]
        have hT : ∀ j, ∑ c ∈ T j, p1 (π c) = S' (op0 j) + p1 j := by
          intro j
          simp only [T]
          rw [Finset.sum_insert (by simp), hS'0, Equiv.apply_symm_apply, add_comm]
        have hord0 : ∀ i i', π.symm i < π.symm i' → S' (op0 i) + Q.proc (op0 i) ≤ S' (op0 i') := by
          intro i i' hlt
          have h := hT i
          simp only [p1] at h
          rw [← h, hS'0]
          apply Finset.sum_le_sum_of_subset
          intro c hc
          simp only [T, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
          rcases hc with h | h
          · rw [h]; exact hlt
          · exact lt_trans h hlt
        have hcomp0 : ∀ j, S' (op0 j) + Q.proc (op0 j) ≤ S (op1 j) := by
          intro j; have := hsum j; rw [hT] at this; exact this
        have hmach01 : ∀ i i', Q.mach (op0 i) ≠ Q.mach (op1 i') := by
          intro i i' h; have := congrArg Fin.val h; rw [hmach, hmach] at this; simp [hv0, hv1] at this
        have hval : ∀ (j : Fin n) (r : Fin (Q.ops j).length),
            ((⟨j, r⟩ : Q.Op) = op0 j ∧ r.val = 0) ∨ ((⟨j, r⟩ : Q.Op) = op1 j ∧ r.val = 1) := by
          intro j r
          rcases hop ⟨j, r⟩ with h | h
          · left; exact ⟨h, congrArg (fun o : Q.Op => o.2.val) h⟩
          · right; exact ⟨h, congrArg (fun o : Q.Op => o.2.val) h⟩
        refine ⟨S', ⟨?_, ?_, ?_, ?_⟩, ⟨π, ?_⟩, ?_⟩
        · intro o; rw [hrel0]; exact Nat.zero_le _
        · intro j r r' hr
          rcases hval j r with ⟨h, hv⟩ | ⟨h, hv⟩ <;> rcases hval j r' with ⟨h', hv'⟩ | ⟨h', hv'⟩
          · omega
          · rw [h, h', hS'1]; exact hcomp0 j
          · omega
          · omega
        · intro o o' hne hm
          rcases hop o with h | h <;> rcases hop o' with h' | h'
          · rw [h, h']
            have hne' : o.1 ≠ o'.1 := by
              intro he; apply hne; rw [h, h', he]
            rcases lt_or_gt_of_ne (π.symm.injective.ne hne') with hl | hl
            · left; exact hord0 _ _ hl
            · right; exact hord0 _ _ hl
          · exfalso; rw [h, h'] at hm; exact hmach01 _ _ hm
          · exfalso; rw [h, h'] at hm; exact hmach01 _ _ hm.symm
          · rw [h, h', hS'1, hS'1]; rw [h, h'] at hne hm; exact hdisj _ _ hne hm
        · intro j k hjk; simp [hprec] at hjk
        · intro a b o o' hab ho ho' hm
          rcases hop o with h | h <;> rcases hop o' with h' | h'
          · rw [h, h', ho, ho']
            apply hord0; simpa using hab
          · exfalso; rw [h, h'] at hm; exact hmach01 _ _ hm
          · exfalso; rw [h, h'] at hm; exact hmach01 _ _ hm.symm
          · rw [h, h', hS'1, hS'1, ho, ho']
            apply hm2
            · exact π.injective.ne hab.ne
            · exact hmono _ _ hab.le
        · intro j
          apply Finset.sup_le
          intro r _
          have h1 : S (op1 j) + Q.proc (op1 j) ≤ Q.completion S j :=
            Finset.le_sup (f := fun r : Fin (Q.ops j).length => S ⟨j, r⟩ + Q.proc ⟨j, r⟩)
              (Finset.mem_univ _)
          rcases hval j r with ⟨h, -⟩ | ⟨h, -⟩
          · rw [h]; have := hcomp0 j; omega
          · rw [h, hS'1]; exact h1

      have hval : ∀ {n : ℕ} (I : Instance n 2) (Q : SchedComplexity.Shops.ShopInstance n 2)
          (S S' : Q.Op → ℕ) (y : Bound k), (∀ j, Q.completion S' j ≤ Q.completion S j) →
          ValueLE I Q S k y → ValueLE I Q S' k y := by
        intro n I Q S S' y hC hV
        cases k with
        | cmax => exact fun j => le_trans (hC j) (hV j)
        | sumWC =>
          refine le_trans (Finset.sum_le_sum fun j _ => ?_) hV
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hC j) (by positivity)
        | lmax =>
          intro j; have := hV j; have := hC j; unfold lateness at *; omega
        | sumWT =>
          refine le_trans (Finset.sum_le_sum fun j _ => ?_) hV
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := hC j; unfold tardiness lateness; omega
        | sumWU =>
          refine le_trans (Finset.sum_le_sum fun j _ => ?_) hV
          refine Nat.mul_le_mul_left _ ?_
          have := hC j; unfold lateIndicator; split_ifs <;> omega
      have hlang : ∀ x, x ∈ language (.fixed 2) .flow ∅ k ↔ x ∈ language (.fixed 2) .permutation ∅ k := by
        intro x
        simp only [language, Problem.language, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨hv, n, m, I, y, hA, hH, hD, hM, rfl⟩
          obtain ⟨-, rfl⟩ := hA
          refine ⟨hv, n, 2, I, y, ⟨by norm_num, rfl⟩, hH, hD, ?_, rfl⟩
          obtain ⟨hr, hp, -⟩ := hD
          simp at hr hp
          obtain ⟨a, S, hF, -, -, -, hV⟩ := hM
          have hflow : IsFlow I := by simpa [HasShape] using hH
          obtain ⟨S', hF', hC', hle⟩ := hcore I.shop hflow hr hp S hF
          exact ⟨a, S', hF', fun _ => hC', by simp, by simp, hval I I.shop S S' y hle hV⟩
        · rintro ⟨hv, n, m, I, y, hA, hH, hD, hM, rfl⟩
          refine ⟨hv, n, m, I, y, hA, hH, hD, ?_, rfl⟩
          obtain ⟨a, S, hF, -, hNW, hDl, hV⟩ := hM
          exact ⟨a, S, hF, by simp, hNW, hDl, hV⟩
      refine ⟨⟨fun x => x, hid, fun x => hlang x⟩, ⟨fun x => x, hid, fun x => (hlang x).symm⟩⟩
