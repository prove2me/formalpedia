-- Prove2me | solution 1 for OnlineMaxWeightMatch.Approx.Supplement.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:29:54.43759+00:00
-- url     : https://prove2.me/submissions/e08af9c3-80ea-4801-ae3e-296f3f754015

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Supplement_Gadget

open OnlineMaxWeightMatch
open OnlineMaxWeightMatch.Approx
open OnlineMaxWeightMatch.Approx.Supplement

open OnlineMaxWeightMatch.Approx

/-- Lemma 3.4: every optimal online policy on `I_φ` matches every arriving literal ball to one of
its neighbouring bins, on every arrival pattern of positive probability. -/
theorem solution (φ : SSATFormula) (k : ℕ) (hφ : φ.IsThreeCNF) (h1 : φ.NoNegatedRandom)
    (h2 : φ.OccursAtMost k)
    (π : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length))
    (hπ : policyValue (gadget φ k) π = optOn (gadget φ k))
    (a : Fin (φ.n + φ.clauses.length) → Bool) (ha : 0 < arrivalProb (gadget φ k) a)
    (t : Fin (φ.n + φ.clauses.length)) (ht : t.val < φ.n) (hat : a t = true) :
    ∃ i, (i, t) ∈ π.matching a ∧ 0 < (gadget φ k).w i t := by
      by_contra hbad
      push_neg at hbad
      have GS : ∀ (σ : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length))
          (b : Fin (φ.n + φ.clauses.length) → Bool) (j : ℕ) (e : LitBin φ.n × Fin (φ.n + φ.clauses.length)),
          e ∈ σ.matchingUpTo b (j+1) ↔ e ∈ σ.matchingUpTo b j ∨
            (∃ h : j < φ.n + φ.clauses.length, e.2 = ⟨j, h⟩ ∧ σ ⟨j, h⟩ (fun s => b s.1) = some e.1 ∧
              b ⟨j, h⟩ = true ∧ ∀ s, (e.1, s) ∉ σ.matchingUpTo b j) := by
        intro σ b j e
        simp only [OnlinePolicy.matchingUpTo]
        split_ifs with h
        · split
          · rename_i i hi
            split_ifs with h'
            · simp only [Finset.mem_insert]
              constructor
              · rintro (rfl | he)
                · exact Or.inr ⟨h, rfl, hi, h'.1, h'.2⟩
                · exact Or.inl he
              · rintro (he | ⟨_, e2, e3, _, _⟩)
                · exact Or.inr he
                · left; rw [hi] at e3; cases e3; ext <;> simp [e2]
            · constructor
              · exact Or.inl
              · rintro (he | ⟨_, e2, e3, e4, e5⟩)
                · exact he
                · rw [hi] at e3; cases e3; exact absurd ⟨e4, e5⟩ h'
          · rename_i hi
            constructor
            · exact Or.inl
            · rintro (he | ⟨_, e2, e3, e4, e5⟩)
              · exact he
              · rw [hi] at e3; cases e3
        · constructor
          · exact Or.inl
          · rintro (he | ⟨h3, _⟩)
            · exact he
            · exact absurd h3 h
      have G1 : ∀ (σ : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length))
          (b : Fin (φ.n + φ.clauses.length) → Bool) (j : ℕ),
          ∀ e ∈ σ.matchingUpTo b j, e.2.val < j ∧ b e.2 = true := by
        intro σ b j
        induction j with
        | zero => simp [OnlinePolicy.matchingUpTo]
        | succ j ih =>
          intro e he
          rcases (GS σ b j e).1 he with he | ⟨h, e2, _, e4, _⟩
          · exact ⟨by have := (ih e he).1; omega, (ih e he).2⟩
          · rw [e2]; exact ⟨by simp, e4⟩
      have G2 : ∀ (σ : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length))
          (b : Fin (φ.n + φ.clauses.length) → Bool) (j : ℕ),
          ∀ i u u', (i, u) ∈ σ.matchingUpTo b j → (i, u') ∈ σ.matchingUpTo b j → u = u' := by
        intro σ b j
        induction j with
        | zero => simp [OnlinePolicy.matchingUpTo]
        | succ j ih =>
          intro i u u' hu hu'
          rcases (GS σ b j _).1 hu with e1 | ⟨h, e1, _, _, f1⟩ <;>
            rcases (GS σ b j _).1 hu' with e2 | ⟨h', e2, _, _, f2⟩
          · exact ih i u u' e1 e2
          · exact absurd e1 (f2 u)
          · exact absurd e2 (f1 u')
          · simp only at e1 e2; rw [e1, e2]
      have G3 : ∀ (σ : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length))
          (b : Fin (φ.n + φ.clauses.length) → Bool) (j : ℕ),
          ∀ i i' u, (i, u) ∈ σ.matchingUpTo b j → (i', u) ∈ σ.matchingUpTo b j → i = i' := by
        intro σ b j
        induction j with
        | zero => simp [OnlinePolicy.matchingUpTo]
        | succ j ih =>
          intro i i' u hu hu'
          rcases (GS σ b j _).1 hu with e1 | ⟨h, e1, g1, _, f1⟩ <;>
            rcases (GS σ b j _).1 hu' with e2 | ⟨h', e2, g2, _, f2⟩
          · exact ih i i' u e1 e2
          · have := (G1 σ b j _ e1).1; simp only at e2 this; rw [e2] at this; simp at this
          · have := (G1 σ b j _ e2).1; simp only at e1 this; rw [e1] at this; simp at this
          · simp only at g1 g2; rw [g1] at g2; exact Option.some_injective _ g2
      have G4 : ∀ (σ : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length))
          (b b' : Fin (φ.n + φ.clauses.length) → Bool) (j : ℕ),
          (∀ s : Fin (φ.n + φ.clauses.length), s.val < j → b s = b' s) →
          σ.matchingUpTo b j = σ.matchingUpTo b' j := by
        intro σ b b' j
        induction j with
        | zero => intro _; simp [OnlinePolicy.matchingUpTo]
        | succ j ih =>
          intro hb
          have ih' := ih (fun s hs => hb s (by omega))
          ext e
          rw [GS, GS, ih']
          constructor
          · rintro (h | ⟨h, e2, e3, e4, e5⟩)
            · exact Or.inl h
            · refine Or.inr ⟨h, e2, ?_, ?_, e5⟩
              · rw [← e3]; congr 1; funext s; symm
                exact hb s.1 (by have := s.2; rw [Fin.le_def] at this; simp at this; omega)
              · rw [← e4]; exact (hb _ (by simp)).symm
          · rintro (h | ⟨h, e2, e3, e4, e5⟩)
            · exact Or.inl h
            · refine Or.inr ⟨h, e2, ?_, ?_, e5⟩
              · rw [← e3]; congr 1; funext s
                exact hb s.1 (by have := s.2; rw [Fin.le_def] at this; simp at this; omega)
              · rw [← e4]; exact (hb _ (by simp))
      have G5 : ∀ (σ : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length))
          (b : Fin (φ.n + φ.clauses.length) → Bool) (u : Fin (φ.n + φ.clauses.length)) i (j : ℕ),
          u.val < j → ((i, u) ∈ σ.matchingUpTo b j ↔ (i, u) ∈ σ.matchingUpTo b (u.val + 1)) := by
        intro σ b u i j
        induction j with
        | zero => intro h; omega
        | succ j ih =>
          intro hj
          rcases Nat.lt_or_ge u.val j with hl | hl
          · rw [← ih hl, GS]
            constructor
            · rintro (h | ⟨h, e2, _⟩)
              · exact h
              · simp only at e2; rw [e2] at hl; simp at hl
            · exact Or.inl
          · have : u.val = j := by omega
            rw [this]
      have L : ∀ (σ : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length))
          (b : Fin (φ.n + φ.clauses.length) → Bool) (T : Finset (LitBin φ.n × Fin (φ.n + φ.clauses.length))),
          (∀ u i, σ u (fun s => b s.1) = some i ↔ (i, u) ∈ T) → (∀ e ∈ T, b e.2 = true) →
          (∀ i u u', (i, u) ∈ T → (i, u') ∈ T → u = u') →
          ∀ j ≤ φ.n + φ.clauses.length, σ.matchingUpTo b j = T.filter (fun e => e.2.val < j) := by
        intro σ b T H1 H2 H3 j
        induction j with
        | zero => intro _; ext e; simp [OnlinePolicy.matchingUpTo]
        | succ j ih =>
          intro hj
          have ih' := ih (by omega)
          ext e
          rw [GS, ih', Finset.mem_filter, Finset.mem_filter]
          constructor
          · rintro (⟨h, h'⟩ | ⟨h, e2, e3, e4, e5⟩)
            · exact ⟨h, by omega⟩
            · refine ⟨?_, by rw [e2]; simp⟩
              have := (H1 _ _).1 e3; rw [← e2] at this; exact this
          · rintro ⟨h, h'⟩
            rcases Nat.lt_or_ge e.2.val j with hl | hl
            · exact Or.inl ⟨h, hl⟩
            · right
              have hv : e.2.val = j := by omega
              have hjN : j < φ.n + φ.clauses.length := by omega
              have e2 : e.2 = ⟨j, hjN⟩ := Fin.ext hv
              refine ⟨hjN, e2, ?_, ?_, ?_⟩
              · rw [← e2]; exact (H1 _ _).2 h
              · rw [← e2]; exact H2 e h
              · intro s hs
                rw [Finset.mem_filter] at hs
                have h5 : e.2 = s := H3 e.1 e.2 s h hs.1
                have h6 := hs.2
                simp only at h6
                rw [← h5] at h6; omega
      classical
      have NA : ∀ (b b' : Fin (φ.n + φ.clauses.length) → Bool) u i,
          (∀ s, s ≤ u → b s = b' s) → ((i, u) ∈ π.matching b ↔ (i, u) ∈ π.matching b') := by
        intro b b' u i hb
        unfold OnlinePolicy.matching
        rw [G5 π b u i _ u.2, G5 π b' u i _ u.2, G4 π b b' (u.val + 1)]
        intro s hs; exact hb s (by rw [Fin.le_def]; omega)
      set c0 : LitBin φ.n := (⟨t.val, ht⟩, true) with hc0
      set ext : (u : Fin (φ.n + φ.clauses.length)) → ({s // s ≤ u} → Bool) →
          (Fin (φ.n + φ.clauses.length) → Bool) := fun u p s => if h : s ≤ u then p ⟨s, h⟩ else false
        with hext_def
      have hext : ∀ (b : Fin (φ.n + φ.clauses.length) → Bool) u s, s ≤ u →
          ext u (fun s => b s.1) s = b s := by
        intro b u s hs; simp [hext_def, hs]
      obtain ⟨π', hπ'⟩ : ∃ π' : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length), ∀ u p,
          π' u p = if (u = t ∧ ∀ s, s ≤ t → ext u p s = a s) then some c0 else
            if h : ∃ i, (i, u) ∈ π.matching (ext u p) ∧ ¬ (i = c0 ∧ (u < t ∨ ∀ s, s ≤ t → ext u p s = a s))
            then some (Classical.choose h) else none := ⟨_, fun _ _ => rfl⟩
      have dspec : ∀ (b : Fin (φ.n + φ.clauses.length) → Bool) u (C : LitBin φ.n → Prop) i
          (inst : Decidable (∃ j, (j, u) ∈ π.matching b ∧ C j)),
          (if h : ∃ j, (j, u) ∈ π.matching b ∧ C j then some (Classical.choose h) else none) = some i
            ↔ ((i, u) ∈ π.matching b ∧ C i) := by
        intro b u C i inst
        split_ifs with h
        · have hs := Classical.choose_spec h
          constructor
          · intro e; cases e; exact hs
          · intro hi; congr 1; exact G3 π b _ _ _ _ hs.1 hi.1
        · simp only [false_iff]
          exact fun hi => h ⟨i, hi⟩
      set agr : (Fin (φ.n + φ.clauses.length) → Bool) → Prop := fun b => ∀ s, s ≤ t → b s = a s with hagr
      set T : (Fin (φ.n + φ.clauses.length) → Bool) → Finset (LitBin φ.n × Fin (φ.n + φ.clauses.length)) :=
        fun b => if agr b then insert (c0, t) ((π.matching b).filter (fun e => e.2 ≠ t ∧ e.1 ≠ c0))
          else (π.matching b).filter (fun e => ¬ (e.1 = c0 ∧ e.2 < t)) with hT
      have H1 : ∀ b u i, π' u (fun s => b s.1) = some i ↔ (i, u) ∈ T b := by
        intro b u i
        rw [hπ']
        by_cases hag : agr b
        · by_cases hu : u = t
          · subst hu
            have : ∀ s, s ≤ u → ext u (fun s => b s.1) s = a s := fun s hs => (hext b u s hs).trans (hag s hs)
            rw [if_pos ⟨rfl, this⟩]
            simp only [hT, hag, if_true, Finset.mem_insert,
              Finset.mem_filter, Option.some.injEq, Prod.mk.injEq, and_true, ne_eq, not_true_eq_false,
              false_and, and_false, or_false]
            exact eq_comm
          · have hc : (u < t ∨ ∀ s, s ≤ t → ext u (fun s => b s.1) s = a s) := by
              rcases lt_or_gt_of_ne hu with h | h
              · exact Or.inl h
              · exact Or.inr fun s hs => (hext b u s (le_trans hs h.le)).trans (hag s hs)
            rw [if_neg (fun h => hu h.1), dspec _ _ _ _ _, NA (ext u (fun s => b s.1)) b u i (fun s hs => hext b u s hs)]
            simp only [hc, and_true, hT, hag, if_true, Finset.mem_insert,
              Finset.mem_filter, Prod.mk.injEq, ne_eq, hu, not_false_eq_true, true_and, and_false, false_or]
        · have hq : ∀ u', t ≤ u' → ¬ ∀ s, s ≤ t → ext u' (fun s => b s.1) s = a s := by
            intro u' hu' hh
            exact hag fun s hs => (hext b u' s (le_trans hs hu')).symm.trans (hh s hs)
          by_cases hu : u = t
          · subst hu
            rw [if_neg (fun h => hq u le_rfl h.2), dspec _ _ _ _ _, NA (ext u (fun s => b s.1)) b u i (fun s hs => hext b u s hs)]
            simp only [hq u le_rfl, lt_self_iff_false, false_or, hT, hag, if_false,
              Finset.mem_filter, and_false, not_false_eq_true, and_true]
          · have hc : (u < t ∨ ∀ s, s ≤ t → ext u (fun s => b s.1) s = a s) ↔ u < t := by
              constructor
              · rintro (h | h)
                · exact h
                · rcases lt_or_gt_of_ne hu with h' | h'
                  · exact h'
                  · exact absurd h (hq u h'.le)
              · exact Or.inl
            rw [if_neg (fun h => hu h.1), dspec _ _ _ _ _, NA (ext u (fun s => b s.1)) b u i (fun s hs => hext b u s hs)]
            simp only [hc, hT, hag, if_false, Finset.mem_filter]
      have H2 : ∀ b, ∀ e ∈ T b, b e.2 = true := by
        intro b e he
        simp only [hT] at he
        split_ifs at he with hag
        · rcases Finset.mem_insert.1 he with rfl | he
          · simp only; rw [hag t le_rfl]; exact hat
          · exact (G1 π b _ e (Finset.mem_filter.1 he).1).2
        · exact (G1 π b _ e (Finset.mem_filter.1 he).1).2
      have H3 : ∀ b i u u', (i, u) ∈ T b → (i, u') ∈ T b → u = u' := by
        intro b i u u' hu hu'
        simp only [hT] at hu hu'
        split_ifs at hu hu' with hag
        · rcases Finset.mem_insert.1 hu with e1 | e1 <;> rcases Finset.mem_insert.1 hu' with e2 | e2
          · simp only [Prod.mk.injEq] at e1 e2; rw [e1.2, e2.2]
          · simp only [Prod.mk.injEq] at e1; exact absurd e1.1 (Finset.mem_filter.1 e2).2.2
          · simp only [Prod.mk.injEq] at e2; exact absurd e2.1 (Finset.mem_filter.1 e1).2.2
          · exact G2 π b _ i u u' (Finset.mem_filter.1 e1).1 (Finset.mem_filter.1 e2).1
        · exact G2 π b _ i u u' (Finset.mem_filter.1 hu).1 (Finset.mem_filter.1 hu').1
      have hM' : ∀ b, π'.matching b = T b := by
        intro b
        unfold OnlinePolicy.matching
        rw [L π' b (T b) (H1 b) (H2 b) (H3 b) _ le_rfl]
        ext e; simp [Finset.mem_filter, e.2.2]
      set I := gadget φ k with hI
      have wc0t : I.w c0 t = 1 := by simp [hI, gadget, hc0, ht]
      have wlit : ∀ u : Fin (φ.n + φ.clauses.length), u.val < φ.n → u ≠ t → I.w c0 u = 0 := by
        intro u hu hut
        have : ¬ (t.val = u.val) := fun h => hut (Fin.ext h).symm
        simp [hI, gadget, hc0, hu, this]
      set G : Fin (φ.n + φ.clauses.length) → ℝ := fun u => if u ≠ t then I.w c0 u else 0 with hG
      have Gnn : ∀ u, 0 ≤ G u := by intro u; simp only [hG]; split_ifs <;> simp [I.w_nonneg]
      have D1 : ∀ b, ¬ agr b → ∑ e ∈ T b, I.w e.1 e.2 = ∑ e ∈ π.matching b, I.w e.1 e.2 := by
        intro b hag
        simp only [hT, hag, if_false]
        rw [← Finset.sum_filter_add_sum_filter_not (π.matching b) (fun e => ¬(e.1 = c0 ∧ e.2 < t))]
        have hz : ∑ x ∈ Finset.filter (fun e : LitBin φ.n × Fin (φ.n + φ.clauses.length) =>
            ¬¬(e.1 = c0 ∧ e.2 < t)) (π.matching b), I.w x.1 x.2 = 0 := by
          apply Finset.sum_eq_zero
          intro e he
          rw [Finset.mem_filter, not_not] at he
          rw [he.2.1]
          exact wlit _ (by have := he.2.2; rw [Fin.lt_def] at this; omega) (ne_of_lt he.2.2)
        rw [hz, add_zero]
      have D2 : ∀ b, agr b → 1 + ∑ e ∈ π.matching b, I.w e.1 e.2 -
          ∑ u, (if b u = true then G u else 0) ≤ ∑ e ∈ T b, I.w e.1 e.2 := by
        intro b hag
        simp only [hT, hag, if_true]
        rw [Finset.sum_insert (by simp), wc0t]
        rw [← Finset.sum_filter_add_sum_filter_not (π.matching b) (fun e => e.2 ≠ t ∧ e.1 ≠ c0)]
        have key : ∑ e ∈ Finset.filter (fun e => ¬(e.2 ≠ t ∧ e.1 ≠ c0)) (π.matching b), I.w e.1 e.2
            ≤ ∑ u, (if b u = true then G u else 0) := by
          set F : LitBin φ.n × Fin (φ.n + φ.clauses.length) → ℝ := fun e => if e.1 = c0 then G e.2 else 0
            with hF
          have Fnn : ∀ e, 0 ≤ F e := by intro e; simp only [hF]; split_ifs <;> simp [Gnn]
          calc ∑ e ∈ Finset.filter (fun e => ¬(e.2 ≠ t ∧ e.1 ≠ c0)) (π.matching b), I.w e.1 e.2
              ≤ ∑ e ∈ Finset.filter (fun e => ¬(e.2 ≠ t ∧ e.1 ≠ c0)) (π.matching b), F e := by
                apply Finset.sum_le_sum
                intro e he
                rw [Finset.mem_filter] at he
                by_cases h2t : e.2 = t
                · have hm : (e.1, t) ∈ π.matching a := by
                    rw [← NA b a t e.1 (fun s hs => hag s hs), ← h2t]; exact he.1
                  have := hbad e.1 hm
                  rw [h2t]; exact le_trans this (Fnn e)
                · have he1 : e.1 = c0 := by
                    by_contra h; exact he.2 ⟨h2t, h⟩
                  have : F e = I.w c0 e.2 := by simp [hF, he1, hG, h2t]
                  rw [this, he1]
            _ ≤ ∑ e ∈ Finset.univ.filter (fun e : LitBin φ.n × Fin (φ.n + φ.clauses.length) => b e.2 = true), F e := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro e he
                  rw [Finset.mem_filter] at he
                  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (G1 π b _ e he.1).2⟩
                · intro e _ _; exact Fnn e
            _ = ∑ u, (if b u = true then G u else 0) := by
                rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro u _
                split_ifs with hb
                · simp [hF, Finset.sum_ite_eq']
                · simp
        linarith
      set P : (Fin (φ.n + φ.clauses.length) → Bool) → ℝ := fun b => arrivalProb I b with hP
      have Pnn : ∀ b, 0 ≤ P b := by
        intro b; simp only [hP, arrivalProb]
        apply Finset.prod_nonneg; intro s _
        split_ifs
        · exact I.p_nonneg s
        · linarith [I.p_le_one s]
      set PS := ∑ b, (if agr b then P b else 0) with hPS
      have indep : ∀ u, t < u → ∑ b, (if agr b ∧ b u = true then P b else 0) = I.p u * PS := by
        intro u htu
        set fl : (Fin (φ.n + φ.clauses.length) → Bool) → (Fin (φ.n + φ.clauses.length) → Bool) :=
          fun b => Function.update b u (!b u) with hfl
        have flinv : Function.Involutive fl := by
          intro b; funext s; simp only [hfl]
          by_cases hs : s = u
          · subst hs; simp
          · simp [Function.update_of_ne hs]
        set Q : (Fin (φ.n + φ.clauses.length) → Bool) → ℝ :=
          fun b => ∏ s ∈ Finset.univ.erase u, (if b s = true then I.p s else 1 - I.p s) with hQ
        have hPQ : ∀ b, P b = (if b u = true then I.p u else 1 - I.p u) * Q b := by
          intro b; simp only [hP, arrivalProb, hQ]
          exact (Finset.mul_prod_erase Finset.univ (fun s => if b s = true then I.p s else 1 - I.p s)
            (Finset.mem_univ u)).symm
        have hQfl : ∀ b, Q (fl b) = Q b := by
          intro b; simp only [hQ]
          apply Finset.prod_congr rfl; intro s hs
          have : s ≠ u := Finset.ne_of_mem_erase hs
          simp [hfl, Function.update_of_ne this]
        have hagfl : ∀ b, agr (fl b) ↔ agr b := by
          intro b
          have hfls : ∀ s, s ≠ u → fl b s = b s := fun s h => Function.update_of_ne h _ _
          constructor
          · intro h s hs
            have := h s hs
            rwa [hfls s (ne_of_lt (lt_of_le_of_lt hs htu))] at this
          · intro h s hs
            show fl b s = a s
            rw [hfls s (ne_of_lt (lt_of_le_of_lt hs htu))]; exact h s hs
        have hflu : ∀ b, fl b u = !b u := by intro b; simp [hfl]
        set A := ∑ b, (if agr b ∧ b u = true then Q b else 0) with hA
        have hB : ∑ b, (if agr b ∧ b u = false then Q b else 0) = A := by
          rw [hA]
          apply Fintype.sum_equiv (Function.Involutive.toPerm fl flinv)
          intro b
          simp only [Function.Involutive.coe_toPerm, hagfl, hflu, hQfl]
          cases b u <;> simp
        have hX : ∑ b, (if agr b ∧ b u = true then P b else 0) = I.p u * A := by
          rw [hA, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _
          split_ifs with h
          · rw [hPQ, if_pos h.2]
          · simp
        have hPSA : PS = A := by
          have : PS = I.p u * A + (1 - I.p u) * ∑ b, (if agr b ∧ b u = false then Q b else 0) := by
            rw [hPS, hA, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro b _
            rw [hPQ]
            cases hbu : b u <;> by_cases hg : agr b <;> simp [hg]
          rw [this, hB]; ring
        rw [hX, hPSA]
      have cntL : ∀ L : List (List (ℕ × Bool)), (∑ r : Fin L.length,
          (if (t.val, true) ∈ L.getD r.val [] then (1:ℕ) else 0)) = L.countP (fun C => decide ((t.val, true) ∈ C)) := by
        intro L
        induction L with
        | nil => simp
        | cons C L ih =>
          rw [List.countP_cons, ← ih]
          simp only [List.length_cons, Fin.sum_univ_succ, Fin.val_zero, List.getD_cons_zero, Fin.val_succ,
            List.getD_cons_succ, decide_eq_true_eq]
          ring
      have cntk : (∑ r : Fin φ.clauses.length,
          (if (t.val, true) ∈ φ.clauses.getD r.val [] then (1:ℕ) else 0)) ≤ k := by
        rw [cntL]
        refine le_trans (List.countP_mono_left (q := fun C => C.any fun l => l.1 == t.val) ?_) ?_
        · intro C _ hC
          simp only [decide_eq_true_eq] at hC
          simp only [List.any_eq_true, beq_iff_eq]
          exact ⟨_, hC, rfl⟩
        · rw [List.countP_eq_length_filter]; exact h2 t.val
      have Gp : ∑ u, G u * I.p u ≤ 1 / 2 := by
        rw [Fin.sum_univ_add]
        have z1 : ∑ i : Fin φ.n, G (Fin.castAdd φ.clauses.length i) * I.p (Fin.castAdd φ.clauses.length i) = 0 := by
          apply Finset.sum_eq_zero; intro i _
          simp only [hG]
          split_ifs with h
          · rw [wlit _ (by simp) h, zero_mul]
          · rw [zero_mul]
        rw [z1, zero_add]
        have z2 : ∀ r : Fin φ.clauses.length, G (Fin.natAdd φ.n r) * I.p (Fin.natAdd φ.n r) =
            (1 / (2 * (k:ℝ))) * (if (t.val, true) ∈ φ.clauses.getD r.val [] then (1:ℕ) else 0 : ℕ) := by
          intro r
          have hne : Fin.natAdd φ.n r ≠ t := by
            intro h; have := congrArg Fin.val h; simp at this; omega
          have hm : (φ.clauses.length : ℝ) ≠ 0 := by
            have := r.2; exact_mod_cast (by omega : φ.clauses.length ≠ 0)
          simp only [hG, ne_eq, hne, not_false_eq_true, if_true, hI, gadget, Fin.val_natAdd]
          have h3 : ¬ (φ.n + r.val < φ.n) := by omega
          simp only [h3, if_false, Nat.add_sub_cancel_left, hc0]
          split_ifs <;> push_cast <;> field_simp <;> simp
        simp_rw [z2]
        rw [← Finset.mul_sum]
        have := cntk
        have hk : ((∑ r : Fin φ.clauses.length,
          (if (t.val, true) ∈ φ.clauses.getD r.val [] then (1:ℕ) else 0) : ℕ) : ℝ) ≤ k := by exact_mod_cast this
        push_cast at hk ⊢
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; simp
        · have hkpos : (0:ℝ) < k := by exact_mod_cast h0
          rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
          linarith
      have hV : ∀ σ, policyValue I σ = ∑ b, P b * ∑ e ∈ σ.matching b, I.w e.1 e.2 := fun σ => rfl
      have bdd : BddAbove (Set.range (fun σ => policyValue I σ)) := by
        refine ⟨∑ b, P b * ∑ e : LitBin φ.n × Fin (φ.n + φ.clauses.length), I.w e.1 e.2, ?_⟩
        rintro _ ⟨σ, rfl⟩
        simp only
        rw [hV]
        apply Finset.sum_le_sum; intro b _
        apply mul_le_mul_of_nonneg_left _ (Pnn b)
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro e _ _; exact I.w_nonneg _ _
      have hle : policyValue I π' ≤ policyValue I π := by
        rw [hπ]; exact le_ciSup bdd π'
      have step1 : ∑ b, (if agr b then P b * (1 - ∑ u, (if b u = true then G u else 0)) else 0)
          ≤ policyValue I π' - policyValue I π := by
        rw [hV, hV, ← Finset.sum_sub_distrib]
        apply Finset.sum_le_sum; intro b _
        rw [hM', ← mul_sub]
        split_ifs with hag
        · apply mul_le_mul_of_nonneg_left _ (Pnn b)
          have := D2 b hag; linarith
        · rw [D1 b hag]; simp
      have step2 : ∑ b, (if agr b then P b * (1 - ∑ u, (if b u = true then G u else 0)) else 0)
          = PS - ∑ u, G u * ∑ b, (if agr b ∧ b u = true then P b else 0) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm (f := fun u b => G u * (if agr b ∧ b u = true then P b else 0)), hPS,
          ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro b _
        by_cases hag : agr b
        · simp only [hag, if_true, true_and, mul_sub, mul_one, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl; intro u _
          split_ifs <;> ring
        · simp [hag]
      have step3 : ∑ u, G u * ∑ b, (if agr b ∧ b u = true then P b else 0) = PS * ∑ u, G u * I.p u := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro u _
        by_cases htu : t < u
        · rw [indep u htu]; ring
        · have : G u = 0 := by
            simp only [hG]
            split_ifs with h
            · apply wlit u _ h
              have : u < t := lt_of_le_of_ne (not_lt.1 htu) h
              rw [Fin.lt_def] at this; omega
            · rfl
          rw [this]; ring
      have PSpos : 0 < PS := by
        have : (if agr a then P a else 0) ≤ PS := by
          rw [hPS]
          exact Finset.single_le_sum (f := fun b => if agr b then P b else 0)
            (fun b _ => by split_ifs <;> simp [Pnn b]) (Finset.mem_univ a)
        have hagra : agr a := fun s _ => rfl
        rw [if_pos hagra] at this
        exact lt_of_lt_of_le ha this
      have : PS * ∑ u, G u * I.p u ≤ PS * (1 / 2) := mul_le_mul_of_nonneg_left Gp PSpos.le
      linarith
