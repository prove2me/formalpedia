-- Prove2me | solution 1 for OnlineMaxWeightMatch.Approx.Supplement.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:29:39.550384+00:00
-- url     : https://prove2.me/submissions/62992eb4-da87-4075-bc40-0bcb2ed5cd7c

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Supplement_ExpanderSplit

open OnlineMaxWeightMatch
open OnlineMaxWeightMatch.Approx
open OnlineMaxWeightMatch.Approx.Supplement

/-- Lemma 3.2: for a 3CNF MAX-SSAT formula `φ` and graphs `G v` of expansion at least 1 on the
copies of each deterministic variable, the split formula `φ′` satisfies
`OPT_on(φ′) = OPT_on(φ) + E_n`. -/
theorem solution (φ : SSATFormula) (hφ : φ.IsThreeCNF)
    (G : (v : ℕ) → SimpleGraph (Fin (φ.occ v)))
    (hG : ∀ v, v < φ.n → ¬ IsRandomVar v → HasExpansionAtLeastOne (G v)) :
    ssatOpt (φ.split G) = ssatOpt φ + φ.En G := by
      set_option backward.isDefEq.respectTransparency false in
        classical
        have hlenpos (v : ℕ) : 0 < φ.blockLen v := by
          unfold SSATFormula.blockLen
          split_ifs with h
          · omega
          · have : φ.occ v ≠ 0 := fun h0 => h (Or.inr h0)
            omega
        have hlenodd (v : ℕ) : φ.blockLen v % 2 = 1 := by
          unfold SSATFormula.blockLen
          split_ifs with h
          · rfl
          · have : φ.occ v ≠ 0 := fun h0 => h (Or.inr h0)
            omega
        have hstartsucc (v : ℕ) : φ.blockStart (v + 1) = φ.blockStart v + φ.blockLen v := by
          simp [SSATFormula.blockStart, Finset.sum_range_succ]
        have hstartmono : StrictMono φ.blockStart := by
          apply strictMono_nat_of_lt_succ
          intro v
          rw [hstartsucc]
          exact Nat.lt_add_of_pos_right (hlenpos v)
        have hstartpar (v : ℕ) : φ.blockStart v % 2 = v % 2 := by
          induction v with
          | zero => simp [SSATFormula.blockStart]
          | succ v ih => rw [hstartsucc, Nat.add_mod, hlenodd, ih]; omega
        have hrandom (v : ℕ) : IsRandomVar (φ.blockStart v) ↔ IsRandomVar v := by
          simp only [IsRandomVar, hstartpar]
        have hcopypar (v j : ℕ) : IsRandomVar (φ.copyVar v j) ↔ IsRandomVar v := by
          simp [SSATFormula.copyVar, IsRandomVar, Nat.add_mod, hstartpar]
        have hcopylt (v j : ℕ) (hv : ¬ IsRandomVar v) (hj : j < φ.occ v) :
            φ.copyVar v j < φ.blockStart (v + 1) := by
          rw [SSATFormula.copyVar, hstartsucc]
          have hl : φ.blockLen v = 2 * φ.occ v - 1 := by
            simp [SSATFormula.blockLen, hv, Nat.ne_of_gt (Nat.zero_lt_of_lt hj)]
          rw [hl]
          omega
        have hcopybound (v j : ℕ) (hv : v < φ.n) (hd : ¬ IsRandomVar v)
            (hj : j < φ.occ v) : φ.copyVar v j < (φ.split G).n := by
          exact lt_of_lt_of_le (hcopylt v j hd hj) (hstartmono.monotone hv)
        have hstartbound (v : ℕ) (hv : v < φ.n) : φ.blockStart v < (φ.split G).n :=
          hstartmono hv
        have hvarbound (l : ℕ × Bool) (hl : l ∈ φ.clauses.flatten) : l.1 < φ.n := by
          obtain ⟨C, hC, hl⟩ := List.mem_flatten.mp hl
          exact (hφ C hC).2.2 l hl
        have hvaluebound (ψ : SSATFormula) (σ : SSATPolicy ψ.n) :
            0 ≤ ssatValue ψ σ ∧ ssatValue ψ σ ≤ ψ.clauses.length := by
          have hp : (0 : ℝ) < 2 ^ ψ.n := by positivity
          constructor
          · unfold ssatValue
            positivity
          · unfold ssatValue
            apply (div_le_iff₀ hp).2
            calc
              _ ≤ ∑ _r : Fin ψ.n → Bool, (ψ.clauses.length : ℝ) := by
                apply Finset.sum_le_sum
                intro r _
                exact_mod_cast List.countP_le_length
              _ = _ := by simp [mul_comm]
        have hcut (a : ℕ) (H : SimpleGraph (Fin a)) (hH : HasExpansionAtLeastOne H)
            (S : Finset (Fin a)) (hS : 2 * S.card ≤ a) :
            S.card ≤ ((Finset.univ : Finset (Fin a × Fin a)).filter
              (fun e => e.1 < e.2 ∧ H.Adj e.1 e.2 ∧ ((e.1 ∈ S) ≠ (e.2 ∈ S)))).card := by
          by_cases hne : S.Nonempty
          · have hex := hH S hne (by simpa using hS)
            apply hex.trans
            apply Finset.card_le_card_of_injOn
              (fun e : Fin a × Fin a => if e.1 < e.2 then e else (e.2, e.1))
            · intro e he
              obtain ⟨heprod, hadj⟩ := Finset.mem_filter.mp he
              obtain ⟨h1, h2⟩ := Finset.mem_product.mp heprod
              have h2' : e.2 ∉ S := by simpa using h2
              have hneq : e.1 ≠ e.2 := by intro h; exact h2' (h ▸ h1)
              change (if e.1 < e.2 then e else (e.2, e.1)) ∈
                (Finset.univ.filter (fun e : Fin a × Fin a =>
                  e.1 < e.2 ∧ H.Adj e.1 e.2 ∧ ((e.1 ∈ S) ≠ (e.2 ∈ S))))
              by_cases hlt : e.1 < e.2
              · simp only [if_pos hlt, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨hlt, hadj, by simp [h1, h2']⟩
              · simp only [if_neg hlt, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hneq), hadj.symm,
                  by simp [h1, h2']⟩
            · intro e he f hf hef
              have he1 : e.1 ∈ S := (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1
              have he2 : e.2 ∉ S := by
                simpa using (Finset.mem_product.mp (Finset.mem_filter.mp he).1).2
              have hf1 : f.1 ∈ S := (Finset.mem_product.mp (Finset.mem_filter.mp hf).1).1
              have hf2 : f.2 ∉ S := by
                simpa using (Finset.mem_product.mp (Finset.mem_filter.mp hf).1).2
              dsimp only at hef
              split_ifs at hef with h1 h2 h2
              · exact hef
              · have hh : e.1 = f.2 := congrArg Prod.fst hef
                exact False.elim (hf2 (hh ▸ he1))
              · have hh : e.1 = f.2 := congrArg Prod.snd hef
                exact False.elim (hf2 (hh ▸ he1))
              · exact Prod.ext (congrArg Prod.snd hef) (congrArg Prod.fst hef)
          · simp [Finset.not_nonempty_iff_eq_empty.mp hne]
        have hmajority (a : ℕ) (H : SimpleGraph (Fin a)) (hH : HasExpansionAtLeastOne H)
            (x : Fin a → Bool) :
            ∃ b : Bool,
              ((Finset.univ : Finset (Fin a)).filter (fun j => x j ≠ b)).card ≤
                ((Finset.univ : Finset (Fin a × Fin a)).filter
                  (fun e => e.1 < e.2 ∧ H.Adj e.1 e.2 ∧ x e.1 ≠ x e.2)).card := by
          let T : Finset (Fin a) := Finset.univ.filter (fun j => x j = true)
          have hc : T.card + Tᶜ.card = a := by simp
          by_cases ht : 2 * T.card ≤ a
          · refine ⟨false, ?_⟩
            have heq : Finset.univ.filter (fun j => x j ≠ false) = T := by
              ext j; simp [T]
            rw [heq]
            convert hcut a H hH T ht using 1
            congr 1
            ext e
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            simp [T]
          · refine ⟨true, ?_⟩
            have heq : Finset.univ.filter (fun j => x j ≠ true) = Tᶜ := by
              ext j; simp [T]
            rw [heq]
            convert hcut a H hH Tᶜ (by omega) using 1
            congr 1
            ext e
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            simp [T]
        have hsumFin (a : ℕ) (f : Fin a → ℕ) :
            ((List.finRange a).map f).sum = ∑ j, f j := by
          rw [← List.ofFn_eq_map, List.sum_ofFn]
        have hsumRange (a : ℕ) (f : ℕ → ℕ) :
            ((List.range a).map f).sum = ∑ j ∈ Finset.range a, f j := by
          simpa only [List.toFinset_range] using (List.sum_toFinset f (List.nodup_range (n := a))).symm
        have hcountSum {α : Type} (L : List α) (p : α → Bool) :
            L.countP p = (L.map (fun a => if p a then 1 else 0)).sum := by
          induction L with
          | nil => simp
          | cons a L ih => simp [List.countP_cons, ih]; split <;> omega
        let cuts (x : ℕ → Bool) (v : ℕ) : ℕ :=
          ((Finset.univ : Finset (Fin (φ.occ v) × Fin (φ.occ v))).filter
            (fun e => e.1 < e.2 ∧ (G v).Adj e.1 e.2 ∧
              x (φ.copyVar v e.1) ≠ x (φ.copyVar v e.2))).card
        have heqscore (x : ℕ → Bool) :
            (φ.equalityClauses G).countP (clauseSat x) +
              ∑ v ∈ (Finset.range φ.n).filter (fun v => ¬ IsRandomVar v), cuts x v = φ.En G := by
          simp only [SSATFormula.equalityClauses, List.countP_flatMap, apply_ite,
            List.countP_nil, Function.comp_def]
          simp_rw [hsumRange, hsumFin]
          simp only [SSATFormula.En, cuts, numEdges, Finset.card_eq_sum_ones,
            Finset.sum_filter, Fintype.sum_prod_type]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro v hv
          by_cases hr : IsRandomVar v
          · simp [hr]
          · simp only [hr, not_false_eq_true, ↓reduceIte, Finset.mul_sum]
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            by_cases he : j < k ∧ (G v).Adj j k
            · simp only [he, true_and, ↓reduceIte]
              cases hx : x (φ.copyVar v j) <;> cases hy : x (φ.copyVar v k) <;>
                simp [clauseSat, hx, hy]
            · simp [show ¬ (j < k ∧ (G v).Adj j k ∧ x (φ.copyVar v j) ≠ x (φ.copyVar v k)) from fun hh => he ⟨hh.1, hh.2.1⟩, he]
        have hprefixAppend {α β : Type} (A B : List α) (F : List α → α → β) :
            (A ++ B).mapIdx (fun k l => F ((A ++ B).take k) l) =
              A.mapIdx (fun k l => F (A.take k) l) ++
              B.mapIdx (fun k l => F (A ++ B.take k) l) := by
          rw [List.mapIdx_append]
          congr 1
          · apply List.mapIdx_eq_mapIdx_iff.mpr
            intro k hk
            rw [List.take_append_of_le_length (Nat.le_of_lt hk)]
          · apply List.mapIdx_eq_mapIdx_iff.mpr
            intro k hk
            simp [List.take_append, List.take_of_length_le (by omega : A.length ≤ k + A.length)]
        have hprefixFlatten {α β : Type} (Cs : List (List α)) (B : List α)
            (F : List α → α → β) :
            (Cs.mapIdx (fun r C => C.mapIdx
              (fun p l => F (B ++ (Cs.take r).flatten ++ C.take p) l))).flatten =
            Cs.flatten.mapIdx (fun k l => F (B ++ Cs.flatten.take k) l) := by
          induction Cs generalizing B with
          | nil => simp
          | cons C Cs ih =>
            simp only [List.mapIdx_cons, List.flatten_cons, List.take_succ_cons,
              List.take_zero, List.flatten_nil, List.append_nil]
            rw [hprefixAppend C Cs.flatten (fun P l => F (B ++ P) l)]
            have hh := ih (B ++ C)
            simpa only [List.flatten_cons, List.append_assoc] using
              congrArg (fun X => C.mapIdx (fun p l => F (B ++ C.take p) l) ++ X) hh
        have hoccSum (n : ℕ) (L : List (ℕ × Bool))
            (hb : ∀ l ∈ L, l.1 < n) (w : ℕ → ℕ → ℕ) :
            (L.mapIdx (fun k l => w l.1 ((L.take k).countP (fun l' => l'.1 == l.1)))).sum =
              ∑ v ∈ Finset.range n, ∑ j ∈ Finset.range (L.countP (fun l => l.1 == v)), w v j := by
          induction L using List.reverseRecOn with
          | nil => simp
          | append_singleton L l ih =>
            have hbL : ∀ l' ∈ L, l'.1 < n := fun l' hl' => hb l' (List.mem_append_left _ hl')
            have hbl : l.1 < n := hb l (by simp)
            have hstep (v : ℕ) :
                (∑ j ∈ Finset.range ((L ++ [l]).countP (fun l' => l'.1 == v)), w v j) =
                (∑ j ∈ Finset.range (L.countP (fun l' => l'.1 == v)), w v j) +
                  if v = l.1 then w l.1 (L.countP (fun l' => l'.1 == l.1)) else 0 := by
              by_cases hv : v = l.1
              · subst v; simp [List.countP_append, Finset.sum_range_succ]
              · simp [List.countP_append, hv, Ne.symm hv]
            rw [hprefixAppend L [l] (fun P l => w l.1 (P.countP (fun l' => l'.1 == l.1)))]
            simp only [List.mapIdx_singleton, List.take_zero, List.append_nil,
              List.sum_append, List.sum_singleton]
            rw [ih hbL]
            simp_rw [hstep]
            rw [Finset.sum_add_distrib]
            simp [hbl]
        have hmapIdxMap {α β γ : Type} (L : List α) (f : ℕ → α → β) (g : β → γ) :
            (L.mapIdx f).map g = L.mapIdx (fun i l => g (f i l)) := by
          apply List.ext_getElem
          · simp
          · intro i h1 h2
            simp
        have hmapIdxConst {α β : Type} (L : List α) (f : α → β) :
            L.mapIdx (fun _ l => f l) = L.map f := by
          apply List.ext_getElem
          · simp
          · intro i h1 h2
            simp
        have hboolstep (u v A B : Bool) (c d : ℕ)
            (h : (if A then 1 else 0) ≤ (if B then 1 else 0) + d)
            (hc : u ≠ v → 1 ≤ c) :
            (if u || A then 1 else 0) ≤ (if v || B then 1 else 0) + (c + d) := by
          cases u <;> cases v <;> cases A <;> cases B <;> simp at h hc ⊢ <;> omega
        have hclauseBound (C : List (ℕ × Bool)) (a : ℕ → (ℕ × Bool) → ℕ)
            (x y : ℕ → Bool) :
            (if clauseSat x (C.mapIdx (fun p l => (a p l, l.2))) then 1 else 0) ≤
              (if clauseSat y C then 1 else 0) +
                (C.mapIdx (fun p l => if x (a p l) ≠ y l.1 then 1 else 0)).sum := by
          induction C generalizing a with
          | nil => simp [clauseSat]
          | cons l C ih =>
            have hh := ih (fun p l => a (p + 1) l)
            have hh' := hboolstep (x (a 0 l) == l.2) (y l.1 == l.2)
              (clauseSat x (C.mapIdx (fun p l => (a (p + 1) l, l.2))))
              (clauseSat y C) (if x (a 0 l) ≠ y l.1 then 1 else 0)
              (C.mapIdx (fun p l => if x (a (p + 1) l) ≠ y l.1 then 1 else 0)).sum hh
              (by
                intro hn
                by_cases he : x (a 0 l) = y l.1
                · exact False.elim (hn (by rw [he]))
                · simp [he])
            simpa only [List.mapIdx_cons, clauseSat, List.any_cons, List.sum_cons] using hh'
        have hsplitBound (x y : ℕ → Bool)
            (hr : ∀ v, v < φ.n → IsRandomVar v → x (φ.blockStart v) = y v) :
            φ.splitClauses.countP (clauseSat x) ≤ φ.numSat y +
              ∑ v ∈ (Finset.range φ.n).filter (fun v => ¬ IsRandomVar v),
                ((Finset.univ : Finset (Fin (φ.occ v))).filter
                  (fun j : Fin (φ.occ v) => x (φ.copyVar v j) ≠ y v)).card := by
          let a : List (ℕ × Bool) → (ℕ × Bool) → ℕ := fun P l =>
            if IsRandomVar l.1 then φ.blockStart l.1
            else φ.copyVar l.1 (P.countP (fun l' => l'.1 == l.1))
          have ha : φ.splitClauses = φ.clauses.mapIdx (fun r C =>
              C.mapIdx (fun p l => (a ((φ.clauses.take r).flatten ++ C.take p) l, l.2))) := by
            unfold SSATFormula.splitClauses
            apply List.mapIdx_eq_mapIdx_iff.mpr
            intro r hr
            apply List.mapIdx_eq_mapIdx_iff.mpr
            intro p hp
            dsimp [a]
            split_ifs <;> rfl
          let w : ℕ → ℕ → ℕ := fun v j =>
            if IsRandomVar v then 0 else if x (φ.copyVar v j) ≠ y v then 1 else 0
          have hcost :
              (φ.clauses.mapIdx (fun r C => (C.mapIdx (fun p l =>
                if x (a ((φ.clauses.take r).flatten ++ C.take p) l) ≠ y l.1 then 1 else 0)).sum)).sum =
              ∑ v ∈ (Finset.range φ.n).filter (fun v => ¬ IsRandomVar v),
                ((Finset.univ : Finset (Fin (φ.occ v))).filter
                  (fun j : Fin (φ.occ v) => x (φ.copyVar v j) ≠ y v)).card := by
            have hlocal : φ.clauses.mapIdx (fun r C => C.mapIdx (fun p l =>
                if x (a ((φ.clauses.take r).flatten ++ C.take p) l) ≠ y l.1 then 1 else 0)) =
                φ.clauses.mapIdx (fun r C => C.mapIdx (fun p l =>
                  w l.1 (((φ.clauses.take r).flatten ++ C.take p).countP (fun l' => l'.1 == l.1)))) := by
              apply List.mapIdx_eq_mapIdx_iff.mpr
              intro r hr'
              apply List.mapIdx_eq_mapIdx_iff.mpr
              intro p hp
              let l := φ.clauses[r][p]
              have hl : l ∈ φ.clauses.flatten := List.mem_flatten.mpr
                ⟨φ.clauses[r], List.getElem_mem hr', List.getElem_mem hp⟩
              change (if x (a ((φ.clauses.take r).flatten ++ φ.clauses[r].take p) l) ≠ y l.1 then 1 else 0) =
                w l.1 (((φ.clauses.take r).flatten ++ φ.clauses[r].take p).countP (fun l' => l'.1 == l.1))
              by_cases hv : IsRandomVar l.1
              · simp only [a, w, hv, ↓reduceIte, hr l.1 (hvarbound l hl) hv, ne_self_iff_false]
              · simp only [a, w, hv, ↓reduceIte]
            rw [← hmapIdxMap, ← List.sum_flatten, hlocal]
            have hh := hprefixFlatten φ.clauses []
              (fun P l => w l.1 (P.countP (fun l' => l'.1 == l.1)))
            simp only [List.nil_append] at hh
            rw [hh, hoccSum φ.n φ.clauses.flatten hvarbound w]
            simp only [SSATFormula.occ, Finset.sum_filter, Finset.card_eq_sum_ones]
            apply Finset.sum_congr rfl
            intro v hv
            by_cases hd : IsRandomVar v
            · simp [w, hd]
            · simp only [w, hd, ↓reduceIte, not_false_eq_true]
              exact (Fin.sum_univ_eq_sum_range
                (fun j => if x (φ.copyVar v j) ≠ y v then 1 else 0) (φ.occ v)).symm
          rw [ha, hcountSum, SSATFormula.numSat, hcountSum]
          rw [hmapIdxMap]
          rw [← hcost, ← hmapIdxConst φ.clauses (fun C => if clauseSat y C then 1 else 0)]
          simp only [List.mapIdx_eq_ofFn, List.sum_ofFn]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro r hr'
          simpa only [List.mapIdx_eq_ofFn, List.sum_ofFn] using
            hclauseBound (φ.clauses.get r) (fun p l => a ((φ.clauses.take r).flatten ++ (φ.clauses.get r).take p) l) x y
        have hassigncausal (n : ℕ) (σ : SSATPolicy n) (r s : Fin n → Bool)
            (v : ℕ) (h : ∀ j : Fin n, j.val < v → IsRandomVar j.val → r j = s j) :
            ¬ IsRandomVar v → σ.assign r v = σ.assign s v := by
          intro hd
          unfold SSATPolicy.assign
          split_ifs with hv
          · congr 1
            funext j
            split_ifs with hj
            · exact h j.val j.property hj
            · rfl
          · rfl
        have hrealize (n : ℕ) (A : (Fin n → Bool) → Fin n → Bool)
            (hr : ∀ r i, IsRandomVar i.val → A r i = r i)
            (hc : ∀ r s i, ¬ IsRandomVar i.val →
              (∀ j : Fin n, j < i → IsRandomVar j.val → r j = s j) → A r i = A s i) :
            ∃ σ : SSATPolicy n, ∀ r i, σ.assign r i.val = A r i := by
          let σ : SSATPolicy n := fun i h =>
            A (fun j => if hj : j < i then h ⟨j, hj⟩ else false) i
          refine ⟨σ, ?_⟩
          intro r i
          simp only [SSATPolicy.assign, i.isLt, ↓reduceDIte]
          by_cases hi : IsRandomVar i.val
          · simpa [hi] using (hr r i hi).symm
          · simp only [hi, ↓reduceIte]
            apply hc _ _ i hi
            intro j hj hrj
            simp [hj, hrj]
        have havg (n m : ℕ) (f : Fin n → Fin m) (hf : Function.Injective f)
            (F : (Fin m → Bool) → ℝ) :
            (∑ d : Fin m → Bool, ∑ r : Fin n → Bool, F (Function.extend f r d)) =
              (2 : ℝ) ^ n * ∑ d : Fin m → Bool, F d := by
          let swap : ((Fin m → Bool) × (Fin n → Bool)) →
              ((Fin m → Bool) × (Fin n → Bool)) :=
            fun p => (Function.extend f p.2 p.1, fun i => p.1 (f i))
          have hs : Function.Involutive swap := by
            intro p
            apply Prod.ext
            · funext k
              dsimp [swap]
              by_cases hk : ∃ i, f i = k
              · obtain ⟨i, rfl⟩ := hk
                rw [hf.extend_apply]
              · rw [Function.extend_apply' _ _ _ hk, Function.extend_apply' _ _ _ hk]
            · funext i
              exact hf.extend_apply _ _ i
          have he := Equiv.sum_comp (Function.Involutive.toPerm swap hs) (fun p => F p.1)
          simpa [Fintype.sum_prod_type, swap, Fintype.card_fun, ← Finset.sum_mul, mul_comm] using he
        have hpointBound (x y : ℕ → Bool)
            (hr : ∀ v, v < φ.n → IsRandomVar v → x (φ.blockStart v) = y v)
            (hm : ∀ v, v < φ.n → ¬ IsRandomVar v →
              ((Finset.univ : Finset (Fin (φ.occ v))).filter
                (fun j : Fin (φ.occ v) => x (φ.copyVar v j) ≠ y v)).card ≤ cuts x v) :
            (φ.split G).numSat x ≤ φ.numSat y + φ.En G := by
          have hb := hsplitBound x y hr
          have hc := heqscore x
          have hs : (∑ v ∈ (Finset.range φ.n).filter (fun v => ¬ IsRandomVar v),
              ((Finset.univ : Finset (Fin (φ.occ v))).filter
                (fun j : Fin (φ.occ v) => x (φ.copyVar v j) ≠ y v)).card) ≤
              ∑ v ∈ (Finset.range φ.n).filter (fun v => ¬ IsRandomVar v), cuts x v := by
            apply Finset.sum_le_sum
            intro v hv
            exact hm v (Finset.mem_range.mp (Finset.mem_filter.mp hv).1) (Finset.mem_filter.mp hv).2
          change (φ.splitClauses ++ φ.equalityClauses G).countP (clauseSat x) ≤ φ.numSat y + φ.En G
          rw [List.countP_append]
          omega
        have hrank (r p : ℕ) (hr : r < φ.clauses.length) (hp : p < φ.clauses[r].length) :
            (((φ.clauses.take r).flatten ++ φ.clauses[r].take p).countP
              (fun l' => l'.1 == φ.clauses[r][p].1)) < φ.occ φ.clauses[r][p].1 := by
          let pred : ℕ × Bool → Bool := fun l' => l'.1 == φ.clauses[r][p].1
          have hsub : ((φ.clauses.take r).flatten ++ φ.clauses[r]).Sublist φ.clauses.flatten := by
            simpa only [List.take_succ_eq_append_getElem hr, List.flatten_append,
              List.flatten_cons, List.flatten_nil, List.append_nil] using
                (List.take_sublist (r + 1) φ.clauses).flatten
          have hsub' := (List.take_sublist (p + 1) φ.clauses[r]).countP_le (p := pred)
          rw [List.take_succ_eq_append_getElem hp, List.countP_append] at hsub'
          have hlast : List.countP pred [φ.clauses[r][p]] = 1 := by simp [pred]
          rw [hlast] at hsub'
          have htotal := hsub.countP_le (p := pred)
          simp only [List.countP_append] at htotal ⊢
          change List.countP pred (φ.clauses.take r).flatten +
              List.countP pred (φ.clauses[r].take p) < List.countP pred φ.clauses.flatten
          omega
        have hpointExact (x y : ℕ → Bool)
            (hr : ∀ v, v < φ.n → IsRandomVar v → x (φ.blockStart v) = y v)
            (hd : ∀ v, v < φ.n → ¬ IsRandomVar v → ∀ j, j < φ.occ v → x (φ.copyVar v j) = y v) :
            (φ.split G).numSat x = φ.numSat y + φ.En G := by
          have hsat : φ.splitClauses.countP (clauseSat x) = φ.numSat y := by
            rw [SSATFormula.splitClauses, SSATFormula.numSat, hcountSum, hcountSum, hmapIdxMap,
              ← hmapIdxConst φ.clauses (fun C => if clauseSat y C then 1 else 0)]
            congr 1
            apply List.mapIdx_eq_mapIdx_iff.mpr
            intro r hr'
            congr 1
            have heval :
                ((φ.clauses[r]).mapIdx (fun p l =>
                  if IsRandomVar l.1 then (φ.blockStart l.1, l.2)
                  else (φ.copyVar l.1
                    (((φ.clauses.take r).flatten ++ φ.clauses[r].take p).countP (fun l' => l'.1 == l.1)), l.2))).map
                    (fun l => x l.1 == l.2) = φ.clauses[r].map (fun l => y l.1 == l.2) := by
              rw [hmapIdxMap, ← hmapIdxConst]
              apply List.mapIdx_eq_mapIdx_iff.mpr
              intro p hp
              let l := φ.clauses[r][p]
              have hl : l ∈ φ.clauses.flatten := List.mem_flatten.mpr
                ⟨φ.clauses[r], List.getElem_mem hr', List.getElem_mem hp⟩
              simp only [apply_ite, ite_self]
              change ((if IsRandomVar l.1 then x (φ.blockStart l.1) else
                x (φ.copyVar l.1 (((φ.clauses.take r).flatten ++ φ.clauses[r].take p).countP
                  (fun l' => l'.1 == l.1)))) == l.2) = (y l.1 == l.2)
              by_cases hv : IsRandomVar l.1
              · rw [if_pos hv, hr l.1 (hvarbound l hl) hv]
              · rw [if_neg hv, hd l.1 (hvarbound l hl) hv _ (hrank r p hr' hp)]
            have hh := congrArg (fun L : List Bool => L.any id) heval
            exact congrArg (fun b => b = true) (by
              simpa only [List.any_map, Function.comp_def, id_eq, clauseSat] using hh)
          have hc : ∑ v ∈ (Finset.range φ.n).filter (fun v => ¬ IsRandomVar v), cuts x v = 0 := by
            apply Finset.sum_eq_zero
            intro v hv
            obtain ⟨hvn, hvd⟩ := Finset.mem_filter.mp hv
            have hvn' := Finset.mem_range.mp hvn
            apply Finset.card_eq_zero.mpr
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro e he
            obtain ⟨_, _, _, he⟩ := Finset.mem_filter.mp he
            exact he ((hd v hvn' hvd e.1 e.1.isLt).trans (hd v hvn' hvd e.2 e.2.isLt).symm)
          have he := heqscore x
          rw [hc, add_zero] at he
          simp only [SSATFormula.numSat, SSATFormula.split, List.countP_append, hsat, he]
        let f : Fin φ.n → Fin (φ.split G).n := fun v => ⟨φ.blockStart v, hstartbound v v.isLt⟩
        have hf : Function.Injective f := by
          intro i j hij
          exact Fin.ext (hstartmono.injective (congrArg Fin.val hij))
        let merge (d : Fin (φ.split G).n → Bool) (r : Fin φ.n → Bool) := Function.extend f r d
        have hmerge (d : Fin (φ.split G).n → Bool) (r : Fin φ.n → Bool) (v : Fin φ.n) :
            merge d r (f v) = r v := hf.extend_apply r d v
        have hmergeCausal (d : Fin (φ.split G).n → Bool) (r s : Fin φ.n → Bool)
            (v : Fin φ.n) (hv : ¬ IsRandomVar v.val)
            (hh : ∀ j : Fin φ.n, j < v → IsRandomVar j.val → r j = s j)
            (k : Fin (φ.split G).n) (hk : k.val < φ.blockStart (v.val + 1))
            (hkr : IsRandomVar k.val) : merge d r k = merge d s k := by
          by_cases hek : ∃ u, f u = k
          · obtain ⟨u, rfl⟩ := hek
            rw [hmerge, hmerge]
            have hu : u.val < v.val + 1 := hstartmono.lt_iff_lt.mp hk
            have hru : IsRandomVar u.val := (hrandom u.val).mp hkr
            have hne : u.val ≠ v.val := by intro he; exact hv (he ▸ hru)
            exact hh u (by change u.val < v.val; omega) hru
          · exact (Function.extend_apply' r d k hek).trans (Function.extend_apply' s d k hek).symm
        let maj (v : ℕ) (x : Fin (φ.occ v) → Bool) : Bool :=
          if h : v < φ.n ∧ ¬ IsRandomVar v then
            (hmajority _ (G v) (hG v h.1 h.2) x).choose
          else false
        have hmaj (v : ℕ) (hv : v < φ.n) (hd : ¬ IsRandomVar v) (x : ℕ → Bool) :
            ((Finset.univ : Finset (Fin (φ.occ v))).filter
              (fun j : Fin (φ.occ v) => x (φ.copyVar v j) ≠ maj v (fun j => x (φ.copyVar v j)))).card ≤ cuts x v := by
          simpa only [maj, dif_pos (show v < φ.n ∧ ¬ IsRandomVar v from ⟨hv, hd⟩), cuts] using
            (hmajority _ (G v) (hG v hv hd) (fun j => x (φ.copyVar v j))).choose_spec
        have hupperPolicy (σ : SSATPolicy (φ.split G).n) (d : Fin (φ.split G).n → Bool) :
            ∃ τ : SSATPolicy φ.n, ∀ r,
              (φ.split G).numSat (σ.assign (merge d r)) ≤ φ.numSat (τ.assign r) + φ.En G := by
          let A : (Fin φ.n → Bool) → Fin φ.n → Bool := fun r v =>
            if IsRandomVar v.val then r v
            else maj v.val (fun j => σ.assign (merge d r) (φ.copyVar v.val j))
          obtain ⟨τ, hτ⟩ := hrealize φ.n A
            (by intro r i hi; simp [A, hi])
            (by
              intro r s v hv hh
              simp only [A, hv, ↓reduceIte]
              apply congrArg (maj v.val)
              funext j
              apply hassigncausal _ σ _ _ _ _ ((hcopypar v j).not.mpr hv)
              intro k hk hkr
              exact hmergeCausal d r s v hv hh k
                (hk.trans (hcopylt v j hv j.isLt)) hkr)
          refine ⟨τ, fun r => hpointBound _ _ ?_ ?_⟩
          · intro v hv hr
            rw [hτ r ⟨v, hv⟩]
            simp only [A, hr, ↓reduceIte]
            simp only [SSATPolicy.assign, hstartbound v hv, ↓reduceDIte, (hrandom v).mpr hr,
              ↓reduceIte]
            exact hmerge d r ⟨v, hv⟩
          · intro v hv hd
            have he := hτ r ⟨v, hv⟩
            simp only [A, hd, ↓reduceIte] at he
            rw [he]
            exact hmaj v hv hd _
        have hvalsum (ψ : SSATFormula) (σ : SSATPolicy ψ.n) :
            (∑ r : Fin ψ.n → Bool, (ψ.numSat (σ.assign r) : ℝ)) =
              (2 : ℝ) ^ ψ.n * ssatValue ψ σ := by
          unfold ssatValue
          field_simp
        have hvalopt (ψ : SSATFormula) (σ : SSATPolicy ψ.n) : ssatValue ψ σ ≤ ssatOpt ψ := by
          apply le_ciSup
          exact ⟨ψ.clauses.length, by rintro _ ⟨τ, rfl⟩; exact (hvaluebound ψ τ).2⟩
        have hupper : ssatOpt (φ.split G) ≤ ssatOpt φ + φ.En G := by
          let : Nonempty (SSATPolicy (φ.split G).n) := ⟨fun _ _ => false⟩
          apply ciSup_le
          intro σ
          have hsumd (d : Fin (φ.split G).n → Bool) :
              (∑ r : Fin φ.n → Bool, ((φ.split G).numSat (σ.assign (merge d r)) : ℝ)) ≤
                (2 : ℝ)^φ.n * (ssatOpt φ + φ.En G) := by
            obtain ⟨τ, hτ⟩ := hupperPolicy σ d
            calc
              _ ≤ ∑ r : Fin φ.n → Bool, ((φ.numSat (τ.assign r) : ℝ) + φ.En G) := by
                apply Finset.sum_le_sum
                intro r hr
                exact_mod_cast hτ r
              _ = (2 : ℝ)^φ.n * (ssatValue φ τ + φ.En G) := by
                rw [Finset.sum_add_distrib, hvalsum]
                simp [mul_add]
              _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (hvalopt φ τ) le_rfl) (by positivity)
          have hsum := Finset.sum_le_sum (s := Finset.univ) (fun d _ => hsumd d)
          rw [show (∑ d, ∑ r, ((φ.split G).numSat (σ.assign (merge d r)) : ℝ)) =
              (2 : ℝ)^φ.n * ∑ d, ((φ.split G).numSat (σ.assign d) : ℝ) from
            havg _ _ f hf (fun d => ((φ.split G).numSat (σ.assign d) : ℝ))] at hsum
          rw [hvalsum] at hsum
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hsum
          have hp : (0 : ℝ) < 2^φ.n * 2^(φ.split G).n := by positivity
          apply (mul_le_mul_iff_of_pos_left hp).mp
          nlinarith only [hsum]
        have hcopyUnique (v w : ℕ) (hv : ¬ IsRandomVar v) (hw : ¬ IsRandomVar w)
            (j k : ℕ) (hj : j < φ.occ v) (hk : k < φ.occ w)
            (he : φ.copyVar v j = φ.copyVar w k) : v = w := by
          rcases lt_trichotomy v w with hlt | heq | hgt
          · have h1 := hcopylt v j hv hj
            have h2 := hstartmono.monotone (Nat.succ_le_iff.mpr hlt)
            simp only [Nat.succ_eq_add_one] at h2
            have h3 : φ.blockStart w ≤ φ.copyVar w k := by simp [SSATFormula.copyVar]
            omega
          · exact heq
          · have h1 := hcopylt w k hw hk
            have h2 := hstartmono.monotone (Nat.succ_le_iff.mpr hgt)
            simp only [Nat.succ_eq_add_one] at h2
            have h3 : φ.blockStart v ≤ φ.copyVar v j := by simp [SSATFormula.copyVar]
            omega
        let extract (r : Fin (φ.split G).n → Bool) : Fin φ.n → Bool := fun v => r (f v)
        have hlowerPolicy (σ : SSATPolicy φ.n) :
            ∃ τ : SSATPolicy (φ.split G).n, ∀ r,
              (φ.split G).numSat (τ.assign r) = φ.numSat (σ.assign (extract r)) + φ.En G := by
          let P (k : Fin (φ.split G).n) :=
            ∃ v : Fin φ.n, ¬ IsRandomVar v.val ∧ ∃ j : Fin (φ.occ v.val), φ.copyVar v.val j = k.val
          let A : (Fin (φ.split G).n → Bool) → Fin (φ.split G).n → Bool := fun r k =>
            if IsRandomVar k.val then r k
            else if h : P k then σ.assign (extract r) h.choose.val else false
          have hAc : ∀ r s k, ¬ IsRandomVar k.val →
              (∀ j : Fin (φ.split G).n, j < k → IsRandomVar j.val → r j = s j) → A r k = A s k := by
            intro r s k hk hh
            simp only [A, hk, ↓reduceIte]
            by_cases hp : P k
            · simp only [dif_pos hp]
              obtain ⟨hvd, j, hj⟩ := hp.choose_spec
              apply hassigncausal _ σ _ _ _ _ hvd
              intro u hu hur
              apply hh (f u) _ ((hrandom u.val).mpr hur)
              change φ.blockStart u.val < k.val
              have hlt := hstartmono hu
              have hle : φ.blockStart hp.choose.val ≤ φ.copyVar hp.choose.val j := by
                simp [SSATFormula.copyVar]
              omega
            · simp only [dif_neg hp]
          obtain ⟨τ, hτ⟩ := hrealize (φ.split G).n A
            (by intro r i hi; simp [A, hi]) hAc
          refine ⟨τ, fun r => hpointExact _ _ ?_ ?_⟩
          · intro v hv hr
            rw [hτ r (f ⟨v, hv⟩)]
            have hrf : IsRandomVar (f ⟨v, hv⟩).val := (hrandom v).mpr hr
            simp only [A, hrf, ↓reduceIte]
            simp only [SSATPolicy.assign, hv, ↓reduceDIte, hr, ↓reduceIte]
            rfl
          · intro v hv hd j hj
            let k : Fin (φ.split G).n := ⟨φ.copyVar v j, hcopybound v j hv hd hj⟩
            have hp : P k := ⟨⟨v, hv⟩, hd, ⟨j, hj⟩, rfl⟩
            have ho : hp.choose.val = v := by
              obtain ⟨hwd, wj, hwj⟩ := hp.choose_spec
              exact hcopyUnique _ _ hwd hd _ j wj.isLt hj hwj
            rw [hτ r k]
            simp only [A, show ¬ IsRandomVar k.val from (hcopypar v j).not.mpr hd,
              ↓reduceIte, dif_pos hp, ho]
        have havgExtract (F : (Fin φ.n → Bool) → ℝ) :
            (2 : ℝ)^φ.n * ∑ d : Fin (φ.split G).n → Bool, F (extract d) =
              (2 : ℝ)^(φ.split G).n * ∑ r : Fin φ.n → Bool, F r := by
          have he := (havg φ.n (φ.split G).n f hf (fun d => F (extract d))).symm
          have hm (d : Fin (φ.split G).n → Bool) (r : Fin φ.n → Bool) : extract (merge d r) = r := by
            funext i
            exact hmerge d r i
          simpa only [show Function.extend f = fun r d => merge d r from rfl,
            hm, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] using he
        have hlower : ssatOpt φ + φ.En G ≤ ssatOpt (φ.split G) := by
          let : Nonempty (SSATPolicy φ.n) := ⟨fun _ _ => false⟩
          suffices hs : ssatOpt φ ≤ ssatOpt (φ.split G) - φ.En G by linarith
          apply ciSup_le
          intro σ
          obtain ⟨τ, hτ⟩ := hlowerPolicy σ
          have hs : (∑ r : Fin (φ.split G).n → Bool, ((φ.split G).numSat (τ.assign r) : ℝ)) =
              (∑ r : Fin (φ.split G).n → Bool, (φ.numSat (σ.assign (extract r)) : ℝ)) +
                (2 : ℝ)^(φ.split G).n * φ.En G := by
            simp_rw [hτ, Nat.cast_add]
            rw [Finset.sum_add_distrib]
            simp
          have he := havgExtract (fun r => (φ.numSat (σ.assign r) : ℝ))
          rw [hvalsum] at he hs
          have hp : (0 : ℝ) < 2^φ.n * 2^(φ.split G).n := by positivity
          have hveq : ssatValue (φ.split G) τ = ssatValue φ σ + φ.En G := by
            apply (mul_left_cancel₀ (ne_of_gt hp))
            nlinarith only [congrArg (fun z : ℝ => (2 : ℝ)^φ.n * z) hs, he]
          have hv := hvalopt (φ.split G) τ
          rw [hveq] at hv
          linarith
        exact le_antisymm hupper hlower
