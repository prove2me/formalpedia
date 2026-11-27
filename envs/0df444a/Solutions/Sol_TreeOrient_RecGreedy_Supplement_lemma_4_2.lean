-- Prove2me | solution 1 for TreeOrient.RecGreedy.Supplement.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:25:04.861655+00:00
-- url     : https://prove2.me/submissions/a1889d0a-7f90-45da-a7bf-78c2b2df5e55

import Mathlib
import Definitions.Def_TreeOrient_RecGreedy_Supplement_LengthModel

open TreeOrient
open TreeOrient.RecGreedy
open TreeOrient.RecGreedy.Supplement

/-- Lemma 4.2, p. 11 (PDF 12): `RG-DC(r, k_r, Y, D, B, L, X, i)` returns a feasible,
length-respecting output `T` with `f_X(T) ≥ f_X(T∗)/i` for every compatible `T∗`. -/
theorem solution {n : ℕ} (I : LInst n) (r : Fin n) (kr : ℕ) (Y : Finset (Fin n))
    (D : Fin n → ℕ) (B L : ℕ) (X : Finset (Fin n)) (i : ℕ) (A : Edges n)
    (hmono : IsMonotone I.f)
    (hsub : NonmonotoneSubmod.Shared.Submodular (fun S => (I.f S : ℝ)))
    (hi : 1 ≤ i)
    (hA : CompatibleDC I r kr Y D B L ((3 / 2 : ℝ) ^ i) A) :
    ∃ T, (rgdc I 1 .enum i r kr Y D B L X).1 = some T ∧
      FeasibleDC I r kr Y D B L T ∧
      fX I.f X r A ≤ (i : ℝ) * fX I.f X r T := by
          classical
          -- chooseBest
          have cb : ∀ (X : Finset (Fin n)) (r : Fin n) (cands : List (Edges n))
              (init : Option (Edges n)) (k : ℕ),
              (∀ T, (cands.foldl (fun (p : Option (Edges n) × ℕ) T =>
                ((match p.1 with
                  | none => some T
                  | some old => if fX I.f X r old < fX I.f X r T then some T else p.1), p.2 + 1))
                  (init, k)).1 = some T → init = some T ∨ T ∈ cands) ∧
              (∀ T ∈ cands, ∃ T', (cands.foldl (fun (p : Option (Edges n) × ℕ) T =>
                ((match p.1 with
                  | none => some T
                  | some old => if fX I.f X r old < fX I.f X r T then some T else p.1), p.2 + 1))
                  (init, k)).1 = some T' ∧ fX I.f X r T ≤ fX I.f X r T') ∧
              (∀ T0, init = some T0 → ∃ T', (cands.foldl (fun (p : Option (Edges n) × ℕ) T =>
                ((match p.1 with
                  | none => some T
                  | some old => if fX I.f X r old < fX I.f X r T then some T else p.1), p.2 + 1))
                  (init, k)).1 = some T' ∧ fX I.f X r T0 ≤ fX I.f X r T') := by
            intro X r cands
            induction cands with
            | nil => intro init k; simp only [List.foldl_nil, List.not_mem_nil]; exact ⟨fun T h => Or.inl h, fun T h => h.elim, fun T0 h => ⟨T0, h, le_rfl⟩⟩
            | cons c cs ih =>
              intro init k
              simp only [List.foldl_cons]
              rcases init with _ | old
              · obtain ⟨h1, h2, h3⟩ := ih (some c) (k + 1)
                refine ⟨fun T hT => ?_, fun T hT => ?_, fun T0 h => by simp at h⟩
                · rcases h1 T hT with h | h
                  · right; simp at h; simp [h]
                  · right; simp [h]
                · rcases List.mem_cons.1 hT with h | h
                  · subst h; exact h3 _ rfl
                  · exact h2 T h
              · by_cases hlt : fX I.f X r old < fX I.f X r c
                · simp only [hlt, if_true]
                  obtain ⟨h1, h2, h3⟩ := ih (some c) (k + 1)
                  refine ⟨fun T hT => ?_, fun T hT => ?_, fun T0 h => ?_⟩
                  · rcases h1 T hT with h | h
                    · right; simp at h; simp [h]
                    · right; simp [h]
                  · rcases List.mem_cons.1 hT with h | h
                    · subst h; exact h3 _ rfl
                    · exact h2 T h
                  · simp at h; subst h
                    obtain ⟨T', e, le⟩ := h3 c rfl
                    exact ⟨T', e, hlt.le.trans le⟩
                · simp only [hlt, if_false]
                  obtain ⟨h1, h2, h3⟩ := ih (some old) (k + 1)
                  refine ⟨fun T hT => ?_, fun T hT => ?_, fun T0 h => ?_⟩
                  · rcases h1 T hT with h | h
                    · left; exact h
                    · right; simp [h]
                  · rcases List.mem_cons.1 hT with h | h
                    · subst h
                      obtain ⟨T', e, le⟩ := h3 old rfl
                      exact ⟨T', e, (not_lt.1 hlt).trans le⟩
                    · exact h2 T h
                  · exact h3 T0 h
          have reach_snd : ∀ (A : Edges n) (r w : Fin n), Reaches A r w → w = r ∨ w ∈ A.image Prod.snd := by
            intro A r w h
            rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 h with h | ⟨c, _, hc⟩
            · exact Or.inl h
            · exact Or.inr (Finset.mem_image.2 ⟨(c, w), hc, rfl⟩)
          have arbo_card : ∀ (A : Edges n) (r : Fin n), IsArbo r A → ((verts r A).erase r).card ≤ A.card := by
            intro A r hA
            calc ((verts r A).erase r).card ≤ (A.image Prod.snd).card := by
                  apply Finset.card_le_card
                  intro w hw
                  rcases Finset.mem_erase.1 hw with ⟨hne, hw⟩
                  rcases reach_snd A r w (hA.2.2 w hw) with h | h
                  · exact absurd h hne
                  · exact h
              _ ≤ A.card := Finset.card_image_le
          have verts_empty : ∀ r : Fin n, verts r (∅ : Edges n) = {r} := by
            intro r; simp [verts]
          have verts_single : ∀ r v : Fin n, verts r ({(r, v)} : Edges n) = {r, v} := by
            intro r v; simp [verts]
          have lenTo_single : ∀ (len : Fin n → Fin n → ℕ) (r v : Fin n), r ≠ v →
              lenTo len {(r, v)} r v = len r v := by
            intro len r v h
            have hw : HasWalkOfLength len {(r, v)} r v (len r v) :=
              Relation.ReflTransGen.single ⟨by simp, by simp⟩
            have hex : ∃ m, HasWalkOfLength len {(r, v)} r v m := ⟨_, hw⟩
            unfold lenTo
            rw [dif_pos hex]
            apply le_antisymm (Nat.find_min' hex hw)
            have key : ∀ p : Fin n × ℕ, Relation.ReflTransGen (WalkStep len {(r, v)}) (r, 0) p →
                (p = (r, 0) ∨ p = (v, len r v)) := by
              intro p hp
              induction hp with
              | refl => left; rfl
              | tail _ hst ih =>
                obtain ⟨he, hl⟩ := hst
                simp at he
                obtain ⟨h1, h2⟩ := he
                rcases ih with ih | ih
                · right; subst ih; exact Prod.ext h2 (by rw [hl, h2]; exact Nat.zero_add _)
                · exfalso; subst ih; exact h (by simpa using h1.symm)
            rcases key _ (Nat.find_spec hex) with h' | h'
            · exact absurd (congrArg Prod.fst h') (by simpa using h.symm)
            · exact le_of_eq (congrArg Prod.snd h').symm
          have lenSum_empty : ∀ (len : Fin n → Fin n → ℕ) (kr : ℕ) (r : Fin n), lenSum len kr r ∅ = 0 := by
            intro len kr r; simp [lenSum, verts_empty]
          have lenSum_single : ∀ (len : Fin n → Fin n → ℕ) (kr : ℕ) (r v : Fin n), r ≠ v →
              lenSum len kr r {(r, v)} = kr + len r v := by
            intro len kr r v h
            have : (verts r ({(r, v)} : Edges n)).erase r = {v} := by
              rw [verts_single]; ext w; simp
              rintro rfl e; exact h e.symm
            simp [lenSum, this, lenTo_single len r v h]
          have reach_single : ∀ r v w : Fin n, w ∈ verts r ({(r, v)} : Edges n) → Reaches {(r, v)} r w := by
            intro r v w hw
            rw [verts_single] at hw
            simp at hw
            rcases hw with rfl | rfl
            · exact Relation.ReflTransGen.refl
            · exact Relation.ReflTransGen.single (by simp)
          have arbo_single : ∀ r v : Fin n, r ≠ v → IsArbo r ({(r, v)} : Edges n) := by
            intro r v h
            refine ⟨?_, ?_, reach_single r v⟩
            · intro e he; simp at he; subst he; exact fun e => h e.symm
            · intro e he e' he' _; simp at he he'; rw [he, he']
          have fs1 : ∀ (r : Fin n) (kr : ℕ) (Y : Finset (Fin n)) (D : Fin n → ℕ) (B L : ℕ) (v : Fin n),
              r ≠ v → I.c r v ≤ B → kr + I.len r v ≤ L → Y ⊆ {r, v} →
              (∀ w ∈ Y.erase r, I.len r v ≤ D w) → FeasibleDC I r kr Y D B L {(r, v)} := by
            intro r kr Y D B L v h hc hl hY hD
            refine ⟨⟨reach_single r v, by simp [cost, hc], by rw [verts_single]; exact hY⟩,
              {(r, v)}, subset_rfl, arbo_single r v h, rfl, by rw [lenSum_single _ _ _ _ h]; exact hl, ?_⟩
            intro w hw
            have hw' : w = v := by
              have := hY (Finset.mem_of_mem_erase hw)
              simp at this
              rcases this with rfl | rfl
              · simp at hw
              · rfl
            subst hw'
            rw [lenTo_single _ _ _ h]; exact hD _ hw
          have fs0 : ∀ (r : Fin n) (kr : ℕ) (Y : Finset (Fin n)) (D : Fin n → ℕ) (B L : ℕ),
              Y ⊆ {r} → FeasibleDC I r kr Y D B L ∅ := by
            intro r kr Y D B L hY
            refine ⟨⟨fun w hw => ?_, by simp [cost], by rw [verts_empty]; exact hY⟩,
              ∅, subset_rfl, ⟨by simp, by simp, fun w hw => ?_⟩, rfl, by rw [lenSum_empty]; exact Nat.zero_le _, ?_⟩
            · rw [verts_empty] at hw; simp at hw; subst hw; exact Relation.ReflTransGen.refl
            · rw [verts_empty] at hw; simp at hw; subst hw; exact Relation.ReflTransGen.refl
            · intro w hw
              have := hY (Finset.mem_of_mem_erase hw)
              simp at this; subst this; simp at hw
          have shape1 : ∀ (A : Edges n) (r : Fin n), IsArbo r A → A.card ≤ 1 →
              A = ∅ ∨ ∃ v, r ≠ v ∧ A = {(r, v)} := by
            intro A r hA hc
            rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hc with h | h
            · left; exact Finset.card_eq_zero.1 h
            · right
              obtain ⟨⟨a, b⟩, rfl⟩ := Finset.card_eq_one.1 h
              have hb : b ≠ r := hA.1 (a, b) (by simp)
              have ha : a = r := by
                by_contra hne
                have hav : a ∈ verts r ({(a, b)} : Edges n) := by simp [verts]
                rcases reach_snd _ r a (hA.2.2 a hav) with h1 | h1
                · exact hne h1
                · simp at h1
                  subst h1
                  have key : ∀ w, Reaches ({(a, a)} : Edges n) r w → w = r := by
                    intro w hw
                    induction hw with
                    | refl => rfl
                    | tail _ hst ih =>
                      simp at hst; obtain ⟨h1, h2⟩ := hst; subst ih; exact absurd h1.symm hne
                  exact hne (key a (hA.2.2 a hav))
              subst ha
              exact ⟨b, fun e => hb e.symm, rfl⟩
          have base : ∀ (r : Fin n) (kr : ℕ) (Y : Finset (Fin n)) (D : Fin n → ℕ) (B L : ℕ)
              (X : Finset (Fin n)) (A : Edges n),
              CompatibleDC I r kr Y D B L ((3 / 2 : ℝ) ^ 1) A →
              ∃ T, (rgdc I 1 .enum 1 r kr Y D B L X).1 = some T ∧
                FeasibleDC I r kr Y D B L T ∧ fX I.f X r A ≤ ((1 : ℕ) : ℝ) * fX I.f X r T := by
            intro r kr Y D B L X A hA
            obtain ⟨⟨hArbo, hYA, hcardA, hcost⟩, hlen, hD⟩ := hA
            have hc1 : A.card ≤ 1 := by
              have : (A.card : ℝ) < 2 := by linarith
              exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
            have hYsub : Y.erase r ⊆ (verts r A).erase r := Finset.erase_subset_erase _ hYA
            have hYc : (Y.erase r).card ≤ 1 := (Finset.card_le_card hYsub).trans ((arbo_card A r hArbo).trans hc1)
            have hcap : ¬ capImp 1 (0 + 1) < ((Y.erase r).card : ℝ) := by
              rw [capImp]; norm_num
              have : ((Y.erase r).card : ℝ) ≤ 1 := by exact_mod_cast hYc
              linarith
            simp only [rgdc, hcap, if_false, if_true]
            have fXmono : ∀ T T' : Edges n, verts r T ⊆ verts r T' → fX I.f X r T ≤ fX I.f X r T' := by
              intro T T' h
              unfold fX
              have := hmono _ _ (Finset.union_subset_union_left h (t := X))
              have : (I.f (verts r T ∪ X) : ℝ) ≤ I.f (verts r T' ∪ X) := by exact_mod_cast this
              linarith
            by_cases hY0 : Y.erase r = ∅
            · rw [if_pos hY0]
              have hYr : Y ⊆ {r} := by
                intro w hw
                by_cases hwr : w = r
                · simp [hwr]
                · have : w ∈ Y.erase r := Finset.mem_erase.2 ⟨hwr, hw⟩
                  rw [hY0] at this; simp at this
              obtain ⟨h1, h2, h3⟩ := cb X r (List.filterMap
                            (fun v =>
                              if (decide (v = r) || decide (B < I.c r v) || decide (L < kr + I.len r v)) = true then none
                              else some ({(r, v)} : Edges n))
                            (List.finRange n)) (some ∅) 0
              obtain ⟨T', hT', hle0⟩ := h3 ∅ rfl
              have hcbeq : ∀ init cands, chooseBest I.f X r init cands = List.foldl (fun (p : Option (Edges n) × ℕ) T =>
                ((match p.1 with
                  | none => some T
                  | some old => if fX I.f X r old < fX I.f X r T then some T else p.1), p.2 + 1)) (init, 0) cands := by
                intro init cands; rfl
              rw [hcbeq]
              refine ⟨T', hT', ?_, ?_⟩
              · rcases h1 T' hT' with h | h
                · cases h; exact fs0 r kr Y D B L hYr
                · obtain ⟨v, -, hv⟩ := List.mem_filterMap.1 h
                  by_cases hb : (decide (v = r) || decide (B < I.c r v) || decide (L < kr + I.len r v)) = true
                  · rw [if_pos hb] at hv; cases hv
                  · rw [if_neg hb] at hv; cases hv
                    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hb
                    exact fs1 r kr Y D B L v (fun e => hb.1.1 e.symm) hb.1.2 hb.2
                      (hYr.trans (by simp)) (fun w hw => by rw [hY0] at hw; simp at hw)
              · rw [Nat.cast_one, one_mul]
                rcases shape1 A r hArbo hc1 with rfl | ⟨v, hv, rfl⟩
                · exact hle0
                · have hmem : ({(r, v)} : Edges n) ∈ List.filterMap
                            (fun v =>
                              if (decide (v = r) || decide (B < I.c r v) || decide (L < kr + I.len r v)) = true then none
                              else some ({(r, v)} : Edges n))
                            (List.finRange n) := by
                    refine List.mem_filterMap.2 ⟨v, List.mem_finRange v, ?_⟩
                    rw [if_neg]
                    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt]
                    refine ⟨⟨fun e => hv e.symm, by simpa [cost] using hcost⟩, ?_⟩
                    rw [lenSum_single _ _ _ _ hv] at hlen; exact hlen
                  obtain ⟨T'', hT'', hle⟩ := h2 _ hmem
                  rw [hT'] at hT''; cases hT''; exact hle
            · rw [if_neg hY0]
              rcases shape1 A r hArbo hc1 with rfl | ⟨v, hv, rfl⟩
              · exfalso; apply hY0
                apply Finset.eq_empty_of_forall_notMem
                intro w hw
                have := hYsub hw
                rw [verts_empty] at this; simp at this
              · have hYv : Y.erase r = {v} := by
                  apply Finset.eq_singleton_iff_unique_mem.2
                  have hall : ∀ w ∈ Y.erase r, w = v := by
                    intro w hw
                    have := hYsub hw
                    rw [verts_single] at this; simp at this; exact this.2
                  obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.2 hY0
                  refine ⟨?_, hall⟩
                  rwa [← hall w hw]
                have hvY : v ∈ Y.erase r := by rw [hYv]; simp
                rw [hYv]
                simp only [Finset.toList_singleton]
                rw [lenSum_single _ _ _ _ hv] at hlen
                have hDv := hD v hvY
                rw [lenTo_single _ _ _ hv] at hDv
                have hcv : I.c r v ≤ B := by simpa [cost] using hcost
                rw [if_pos ⟨hcv, hlen, hDv⟩]
                refine ⟨_, rfl, ?_, by rw [Nat.cast_one, one_mul]⟩
                refine fs1 r kr Y D B L v hv hcv hlen ?_ ?_
                · intro w hw
                  by_cases hwr : w = r
                  · simp [hwr]
                  · have : w ∈ Y.erase r := Finset.mem_erase.2 ⟨hwr, hw⟩
                    rw [hYv] at this; simp at this; simp [this]
                · intro w hw; rw [hYv] at hw; simp at hw; subst hw; exact hDv
          have foldl_app : ∀ {β : Type} (F : List (Edges n × ℕ × ℕ) × ℕ → β → List (Edges n × ℕ × ℕ) × ℕ)
              (g : β → List (Edges n × ℕ × ℕ)), (∀ p x, (F p x).1 = p.1 ++ g x) →
              ∀ (l : List β) p, (l.foldl F p).1 = p.1 ++ l.flatMap g := by
            intro β F g hF l
            induction l with
            | nil => intro p; simp
            | cons x xs ih => intro p; simp [List.foldl_cons, ih, hF, List.append_assoc]
          have leaf_final : ∀ (sub : SubCall n) (r : Fin n) (kr : ℕ) (Y : Finset (Fin n)) (D : Fin n → ℕ)
              (X : Finset (Fin n)) (Brem Lrem : ℕ) (T : Edges n),
              (sub r kr Y D Brem Lrem X).1 = some T →
              (T, 0, 0) ∈ (solveLeaf I .enum sub r kr Y D X Brem Lrem true).1 := by
            intro sub r kr Y D X Brem Lrem T h
            unfold solveLeaf
            simp only [if_true]
            rcases hs : sub r kr Y D Brem Lrem X with ⟨o, t⟩
            rw [hs] at h; simp at h; subst h; simp
          have leaf_nf : ∀ (sub : SubCall n) (r : Fin n) (kr : ℕ) (Y : Finset (Fin n)) (D : Fin n → ℕ)
              (X : Finset (Fin n)) (Brem Lrem b l : ℕ) (T : Edges n), b ≤ Brem → l ≤ Lrem →
              (sub r kr Y D b l X).1 = some T →
              (T, Brem - b, Lrem - l) ∈ (solveLeaf I .enum sub r kr Y D X Brem Lrem false).1 := by
            intro sub r kr Y D X Brem Lrem b l T hb hl h
            unfold solveLeaf
            simp only [Bool.false_eq_true, if_false]
            rw [foldl_app _ (fun l => (List.range (Brem + 1)).flatMap (fun b =>
                (sub r kr Y D b l X).1.toList.map (fun T => (T, Brem - b, Lrem - l))))]
            · simp only [List.nil_append, List.mem_flatMap, List.mem_range]
              refine ⟨l, by omega, b, by omega, ?_⟩
              rw [h]; simp
            · intro p x
              rw [foldl_app _ (fun b => (sub r kr Y D b x X).1.toList.map (fun T => (T, Brem - b, Lrem - x)))]
              intro q y; rfl
          have exp1 : ∀ (sub : SubCall n) (r : Fin n) (kr : ℕ) (Y : Finset (Fin n)) (D : Fin n → ℕ)
              (X : Finset (Fin n)) (B L : ℕ),
              (expand I .enum sub 1 r kr Y D X B L true).1 =
              (List.finRange n).flatMap (fun v => Y.powerset.toList.flatMap (fun S =>
                (List.range (L + 1)).flatMap (fun d1 =>
                  if ∃ w ∈ Y \ (S ∪ {v}), D w < d1 then []
                  else ((expand I .enum sub 0 r kr ((S ∪ {v}) \ {r})
                      (fun w => if w = v then (if v ∈ Y then min d1 (D v) else d1) else D w) X B L false).1).flatMap
                    (fun p => (expand I .enum sub 0 v (kr + lenTo I.len p.1 r v) (Y \ (S ∪ {v}))
                      (fun w => D w - d1) (X ∪ verts r p.1) p.2.1 p.2.2 true).1.map
                      (fun q => (p.1 ∪ q.1, q.2.1, q.2.2)))))) := by
            intro sub r kr Y D X B L
            rw [expand]
            have G3 : ∀ v S d1, ∀ t : List (Edges n × ℕ × ℕ) × ℕ, ((if ∃ w ∈ Y \ (S ∪ {v}), D w < d1 then (t.1, t.2 + 1)
                      else
                        let D1 : Fin n → ℕ := fun w =>
                          if w = v then (if v ∈ Y then min d1 (D v) else d1) else D w
                        let D2 : Fin n → ℕ := fun w => D w - d1
                        let (left, t1) := expand I .enum sub 0 r kr ((S ∪ {v}) \ {r}) D1 X B L false
                        let (more, t2) := left.foldl (fun (more, t2) (p : Edges n × ℕ × ℕ) =>
                          let (right, t') := expand I .enum sub 0 v (kr + lenTo I.len p.1 r v)
                            (Y \ (S ∪ {v})) D2 (X ∪ verts r p.1) p.2.1 p.2.2 true
                          (more ++ right.map (fun q => (p.1 ∪ q.1, q.2.1, q.2.2)), t2 + t')) ([], 0)
                        (t.1 ++ more, t.2 + 1 + t1 + t2)) : List (Edges n × ℕ × ℕ) × ℕ).1 = t.1 ++
                  (if ∃ w ∈ Y \ (S ∪ {v}), D w < d1 then []
                  else ((expand I .enum sub 0 r kr ((S ∪ {v}) \ {r})
                      (fun w => if w = v then (if v ∈ Y then min d1 (D v) else d1) else D w) X B L false).1).flatMap
                    (fun p => (expand I .enum sub 0 v (kr + lenTo I.len p.1 r v) (Y \ (S ∪ {v}))
                      (fun w => D w - d1) (X ∪ verts r p.1) p.2.1 p.2.2 true).1.map
                      (fun q => (p.1 ∪ q.1, q.2.1, q.2.2)))) := by
              intro v S d1 t
              by_cases h : ∃ w ∈ Y \ (S ∪ {v}), D w < d1
              · rw [if_pos h, if_pos h]; simp
              · rw [if_neg h, if_neg h]
                dsimp only
                rw [foldl_app _ (fun p => (expand I .enum sub 0 v (kr + lenTo I.len p.1 r v) (Y \ (S ∪ {v}))
                      (fun w => D w - d1) (X ∪ verts r p.1) p.2.1 p.2.2 true).1.map
                      (fun q => (p.1 ∪ q.1, q.2.1, q.2.2))) ?_]
                · simp
                · intro u x; rfl
            rw [foldl_app _ (fun v => Y.powerset.toList.flatMap (fun S => (List.range (L+1)).flatMap (fun d1 => (if ∃ w ∈ Y \ (S ∪ {v}), D w < d1 then []
                  else ((expand I .enum sub 0 r kr ((S ∪ {v}) \ {r})
                      (fun w => if w = v then (if v ∈ Y then min d1 (D v) else d1) else D w) X B L false).1).flatMap
                    (fun p => (expand I .enum sub 0 v (kr + lenTo I.len p.1 r v) (Y \ (S ∪ {v}))
                      (fun w => D w - d1) (X ∪ verts r p.1) p.2.1 p.2.2 true).1.map
                      (fun q => (p.1 ∪ q.1, q.2.1, q.2.2))))))) ?_]
            · simp only [List.nil_append]
            intro p v
            rw [foldl_app _ (fun S => (List.range (L+1)).flatMap (fun d1 => (if ∃ w ∈ Y \ (S ∪ {v}), D w < d1 then []
                  else ((expand I .enum sub 0 r kr ((S ∪ {v}) \ {r})
                      (fun w => if w = v then (if v ∈ Y then min d1 (D v) else d1) else D w) X B L false).1).flatMap
                    (fun p => (expand I .enum sub 0 v (kr + lenTo I.len p.1 r v) (Y \ (S ∪ {v}))
                      (fun w => D w - d1) (X ∪ verts r p.1) p.2.1 p.2.2 true).1.map
                      (fun q => (p.1 ∪ q.1, q.2.1, q.2.2)))))) ?_]
            intro q S
            rw [foldl_app _ (fun d1 => (if ∃ w ∈ Y \ (S ∪ {v}), D w < d1 then []
                  else ((expand I .enum sub 0 r kr ((S ∪ {v}) \ {r})
                      (fun w => if w = v then (if v ∈ Y then min d1 (D v) else d1) else D w) X B L false).1).flatMap
                    (fun p => (expand I .enum sub 0 v (kr + lenTo I.len p.1 r v) (Y \ (S ∪ {v}))
                      (fun w => D w - d1) (X ∪ verts r p.1) p.2.1 p.2.2 true).1.map
                      (fun q => (p.1 ∪ q.1, q.2.1, q.2.2))))) ?_]
            intro t d1
            exact G3 v S d1 t
          have leafF : ∀ (sub : SubCall n) (r : Fin n) (kr : ℕ) (Y : Finset (Fin n)) (D : Fin n → ℕ)
              (X : Finset (Fin n)) (Brem Lrem : ℕ),
              (expand I .enum sub 0 r kr Y D X Brem Lrem false).1 =
                (List.range (Lrem + 1)).flatMap (fun l => (List.range (Brem + 1)).flatMap (fun b =>
                  (sub r kr Y D b l X).1.toList.map (fun T => (T, Brem - b, Lrem - l)))) := by
            intro sub r kr Y D X Brem Lrem
            rw [expand, solveLeaf]
            simp only [Bool.false_eq_true, if_false]
            rw [foldl_app _ (fun l => (List.range (Brem + 1)).flatMap (fun b =>
                (sub r kr Y D b l X).1.toList.map (fun T => (T, Brem - b, Lrem - l))))]
            · simp only [List.nil_append]
            · intro p x
              rw [foldl_app _ (fun b => (sub r kr Y D b x X).1.toList.map (fun T => (T, Brem - b, Lrem - x)))]
              intro q y; rfl
          have leafT : ∀ (sub : SubCall n) (r : Fin n) (kr : ℕ) (Y : Finset (Fin n)) (D : Fin n → ℕ)
              (X : Finset (Fin n)) (Brem Lrem : ℕ),
              (expand I .enum sub 0 r kr Y D X Brem Lrem true).1 =
                (sub r kr Y D Brem Lrem X).1.toList.map (fun T => (T, 0, 0)) := by
            intro sub r kr Y D X Brem Lrem
            rw [expand, solveLeaf]
            rfl
          have candMem : ∀ (sub : SubCall n) (r : Fin n) (kr : ℕ) (Y : Finset (Fin n)) (D : Fin n → ℕ)
              (X : Finset (Fin n)) (B L : ℕ) (T : Edges n),
              T ∈ (expand I .enum sub 1 r kr Y D X B L true).1.map Prod.fst ↔
              ∃ v S d1 b l T1 T2, S ⊆ Y ∧ d1 ≤ L ∧ ¬ (∃ w ∈ Y \ (S ∪ {v}), D w < d1) ∧ b ≤ B ∧ l ≤ L ∧
                (sub r kr ((S ∪ {v}) \ {r})
                  (fun w => if w = v then (if v ∈ Y then min d1 (D v) else d1) else D w) b l X).1 = some T1 ∧
                (sub v (kr + lenTo I.len T1 r v) (Y \ (S ∪ {v})) (fun w => D w - d1) (B - b) (L - l)
                  (X ∪ verts r T1)).1 = some T2 ∧ T = T1 ∪ T2 := by
            intro sub r kr Y D X B L T
            rw [exp1]
            simp only [leafF, leafT, List.mem_map, List.mem_flatMap, List.mem_range, List.mem_finRange,
              true_and, Finset.mem_toList, Finset.mem_powerset, Option.mem_toList]
            constructor
            · rintro ⟨⟨T', a, b'⟩, ⟨v, S, hS, d1, hd1, hmem⟩, rfl⟩
              by_cases h : ∃ w ∈ Y \ (S ∪ {v}), D w < d1
              · rw [if_pos h] at hmem; simp at hmem
              · rw [if_neg h] at hmem
                simp only [List.mem_flatMap, List.mem_map, List.mem_range, Option.mem_toList] at hmem
                obtain ⟨p, ⟨l, hl, b, hb, T1, hT1, rfl⟩, q, ⟨T2, hT2, rfl⟩, he⟩ := hmem
                simp only [Prod.mk.injEq] at he
                refine ⟨v, S, d1, b, l, T1, T2, hS, by omega, h, by omega, by omega, ?_, ?_, he.1.symm⟩
                · simpa using hT1
                · simpa using hT2
            · rintro ⟨v, S, d1, b, l, T1, T2, hS, hd1, h, hb, hl, hT1, hT2, rfl⟩
              refine ⟨(T1 ∪ T2, 0, 0), ⟨v, S, hS, d1, by omega, ?_⟩, rfl⟩
              rw [if_neg h]
              simp only [List.mem_flatMap, List.mem_map, List.mem_range, Option.mem_toList]
              refine ⟨(T1, B - b, L - l), ⟨l, by omega, b, by omega, T1, hT1, rfl⟩, (T2, 0, 0), ⟨T2, hT2, rfl⟩, rfl⟩
          have hcbeq : ∀ (X : Finset (Fin n)) (r : Fin n) init cands, chooseBest I.f X r init cands = List.foldl (fun (p : Option (Edges n) × ℕ) T =>
                ((match p.1 with
                  | none => some T
                  | some old => if fX I.f X r old < fX I.f X r T then some T else p.1), p.2 + 1)) (init, 0) cands := by
            intro X r init cands; rfl
          have walk_mono : ∀ (len : Fin n → Fin n → ℕ) (E E' : Edges n) (r w : Fin n) (m : ℕ), E ⊆ E' →
              HasWalkOfLength len E r w m → HasWalkOfLength len E' r w m := by
            intro len E E' r w m hE h
            exact Relation.ReflTransGen.mono (p := WalkStep len E') (fun p q (hpq : WalkStep len E p q) => ⟨hE hpq.1, hpq.2⟩) _ _ h
          have reach_walk : ∀ (len : Fin n → Fin n → ℕ) (E : Edges n) (r w : Fin n),
              Reaches E r w → ∃ m, HasWalkOfLength len E r w m := by
            intro len E r w h
            induction h with
            | refl => exact ⟨0, Relation.ReflTransGen.refl⟩
            | tail _ hst ih =>
              obtain ⟨m, hm⟩ := ih
              exact ⟨m + len _ _, Relation.ReflTransGen.tail hm (show WalkStep len E (_, m) (_, m + len _ _) from ⟨hst, rfl⟩)⟩
          have lenTo_le : ∀ (len : Fin n → Fin n → ℕ) (E : Edges n) (r w : Fin n) (m : ℕ),
              HasWalkOfLength len E r w m → lenTo len E r w ≤ m := by
            intro len E r w m h
            have hex : ∃ m, HasWalkOfLength len E r w m := ⟨m, h⟩
            unfold lenTo; rw [dif_pos hex]; exact Nat.find_min' hex h
          have lenTo_spec : ∀ (len : Fin n → Fin n → ℕ) (E : Edges n) (r w : Fin n),
              Reaches E r w → HasWalkOfLength len E r w (lenTo len E r w) := by
            intro len E r w h
            have hex := reach_walk len E r w h
            unfold lenTo; rw [dif_pos hex]; exact Nat.find_spec hex
          have lenTo_self : ∀ (len : Fin n → Fin n → ℕ) (E : Edges n) (r : Fin n), lenTo len E r r = 0 := by
            intro len E r
            exact Nat.le_zero.1 (lenTo_le len E r r 0 Relation.ReflTransGen.refl)
          have walk_shift : ∀ (len : Fin n → Fin n → ℕ) (E : Edges n) (p q : Fin n × ℕ) (a : ℕ),
              Relation.ReflTransGen (WalkStep len E) p q →
              Relation.ReflTransGen (WalkStep len E) (p.1, p.2 + a) (q.1, q.2 + a) := by
            intro len E p q a h
            induction h with
            | refl => exact Relation.ReflTransGen.refl
            | tail _ hst ih =>
              refine Relation.ReflTransGen.tail ih ⟨hst.1, ?_⟩
              simp only; rw [hst.2]; omega
          have walk_append : ∀ (len : Fin n → Fin n → ℕ) (E : Edges n) (r v w : Fin n) (a b : ℕ),
              HasWalkOfLength len E r v a → HasWalkOfLength len E v w b →
              HasWalkOfLength len E r w (a + b) := by
            intro len E r v w a b h1 h2
            have := walk_shift len E (v, 0) (w, b) a h2
            simp only [zero_add] at this
            unfold HasWalkOfLength at *
            rw [Nat.add_comm a b]; exact h1.trans this
          have spt : ∀ (len : Fin n → Fin n → ℕ) (E : Edges n) (r : Fin n),
              (∀ w ∈ verts r E, Reaches E r w) →
              ∃ A' ⊆ E, IsArbo r A' ∧ verts r A' = verts r E ∧
                ∀ w ∈ verts r E, lenTo len A' r w ≤ lenTo len E r w := by
            intro len E r hreach
            let WS3 : Fin n × ℕ × ℕ → Fin n × ℕ × ℕ → Prop := fun p q =>
              (p.1, q.1) ∈ E ∧ q.2.1 = p.2.1 + len p.1 q.1 ∧ q.2.2 = p.2.2 + 1
            have up : ∀ p q : Fin n × ℕ, Relation.ReflTransGen (WalkStep len E) p q → ∀ h : ℕ,
                ∃ h', Relation.ReflTransGen WS3 (p.1, p.2, h) (q.1, q.2, h') := by
              intro p q hpq
              induction hpq with
              | refl => intro h; exact ⟨h, Relation.ReflTransGen.refl⟩
              | tail _ hst ih =>
                intro h
                obtain ⟨h', hh⟩ := ih h
                exact ⟨h' + 1, Relation.ReflTransGen.tail hh ⟨hst.1, hst.2, rfl⟩⟩
            have down : ∀ p q : Fin n × ℕ × ℕ, Relation.ReflTransGen WS3 p q →
                Relation.ReflTransGen (WalkStep len E) (p.1, p.2.1) (q.1, q.2.1) := by
              intro p q hpq
              induction hpq with
              | refl => exact Relation.ReflTransGen.refl
              | tail _ hst ih => exact Relation.ReflTransGen.tail ih ⟨hst.1, hst.2.1⟩
            let dist : Fin n → ℕ := fun w => lenTo len E r w
            have hex3 : ∀ w ∈ verts r E, ∃ h, Relation.ReflTransGen WS3 (r, 0, 0) (w, dist w, h) := by
              intro w hw
              exact up (r, 0) (w, dist w) (lenTo_spec len E r w (hreach w hw)) 0
            let hop : Fin n → ℕ := fun w => if hw : w ∈ verts r E then Nat.find (hex3 w hw) else 0
            have hop_spec : ∀ w (hw : w ∈ verts r E),
                Relation.ReflTransGen WS3 (r, 0, 0) (w, dist w, hop w) := by
              intro w hw
              simp only [hop, dif_pos hw]; exact Nat.find_spec (hex3 w hw)
            have hop_le : ∀ w (hw : w ∈ verts r E) h,
                Relation.ReflTransGen WS3 (r, 0, 0) (w, dist w, h) → hop w ≤ h := by
              intro w hw h hh
              simp only [hop, dif_pos hw]; exact Nat.find_min' (hex3 w hw) hh
            have tailv : ∀ a b : Fin n, (a, b) ∈ E → a ∈ verts r E := by
              intro a b h; simp only [verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
              exact Or.inr (Or.inl ⟨(a, b), h, rfl⟩)
            have predex : ∀ w, w ∈ verts r E → w ≠ r → ∃ u, (u, w) ∈ E ∧ u ∈ verts r E ∧
                dist u + len u w ≤ dist w ∧ hop u < hop w := by
              intro w hw hwr
              rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hop_spec w hw) with h | ⟨p, hp, hst⟩
              · have h' := congrArg Prod.fst h; simp only at h'; exact (hwr (by rw [h'])).elim
              · obtain ⟨he, hl, hh⟩ := hst
                have hu := tailv _ _ he
                refine ⟨p.1, he, hu, ?_, ?_⟩
                · have : dist p.1 ≤ p.2.1 := lenTo_le len E r p.1 p.2.1 (down _ _ hp)
                  simp only at hl; omega
                · have hd : dist p.1 ≤ p.2.1 := lenTo_le len E r p.1 p.2.1 (down _ _ hp)
                  -- walk to p.1 of length dist p.1 with hop p.1 hops; but we only need hop p.1 ≤ p.2.2
                  -- use: p walk at length p.2.1; need length = dist p.1
                  have hd' : p.2.1 = dist p.1 := by
                    by_contra hne
                    have hlt : dist p.1 < p.2.1 := lt_of_le_of_ne hd (Ne.symm hne)
                    have hw' : HasWalkOfLength len E r w (dist p.1 + len p.1 w) :=
                      Relation.ReflTransGen.tail (lenTo_spec len E r p.1 (hreach _ hu)) ⟨he, rfl⟩
                    have := lenTo_le len E r w _ hw'
                    simp only at hl; simp only [dist] at hl hlt; omega
                  have : hop p.1 ≤ p.2.2 := hop_le p.1 hu p.2.2 (by rw [← hd']; exact hp)
                  simp only at hh; omega
            choose! pred hpred using predex
            let A' : Edges n := ((verts r E).erase r).image (fun w => (pred w, w))
            have hA'E : A' ⊆ E := by
              intro e he
              obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 he
              obtain ⟨hwr, hw⟩ := Finset.mem_erase.1 hw
              exact (hpred w hw hwr).1
            have vmono : verts r A' ⊆ verts r E := by
              intro w hw
              simp only [verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hw ⊢
              rcases hw with h | ⟨e, he, h⟩ | ⟨e, he, h⟩
              · exact Or.inl h
              · exact Or.inr (Or.inl ⟨e, hA'E he, h⟩)
              · exact Or.inr (Or.inr ⟨e, hA'E he, h⟩)
            have memA' : ∀ w ∈ verts r E, w ≠ r → (pred w, w) ∈ A' := by
              intro w hw hwr
              exact Finset.mem_image.2 ⟨w, Finset.mem_erase.2 ⟨hwr, hw⟩, rfl⟩
            have ind : ∀ k, ∀ w ∈ verts r E, hop w = k →
                Reaches A' r w ∧ ∃ m ≤ dist w, HasWalkOfLength len A' r w m := by
              intro k
              induction k using Nat.strong_induction_on with
              | _ k ihk =>
                intro w hw hk
                by_cases hwr : w = r
                · subst hwr
                  exact ⟨Relation.ReflTransGen.refl, 0, Nat.zero_le _, Relation.ReflTransGen.refl⟩
                · obtain ⟨-, hu, hd, hh⟩ := hpred w hw hwr
                  obtain ⟨hr, m, hm, hwk⟩ := ihk (hop (pred w)) (hk ▸ hh) (pred w) hu rfl
                  refine ⟨Relation.ReflTransGen.tail hr (memA' w hw hwr), m + len (pred w) w, by omega,
                    Relation.ReflTransGen.tail hwk ⟨memA' w hw hwr, rfl⟩⟩
            refine ⟨A', hA'E, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
            · intro e he
              obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 he
              exact (Finset.mem_erase.1 hw).1
            · intro e he e' he' h
              obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 he
              obtain ⟨w', hw', rfl⟩ := Finset.mem_image.1 he'
              simp only at h; subst h; rfl
            · intro w hw; exact (ind _ w (vmono hw) rfl).1
            · apply Finset.Subset.antisymm vmono
              intro w hw
              by_cases hwr : w = r
              · subst hwr; simp [verts]
              · simp only [verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
                exact Or.inr (Or.inr ⟨_, memA' w hw hwr, rfl⟩)
            · intro w hw
              obtain ⟨-, m, hm, hwk⟩ := ind _ w hw rfl
              exact (lenTo_le len A' r w m hwk).trans hm
          have k_vU : ∀ (r v : Fin n) (T1 T2 : Edges n), v ∈ verts r T1 →
              verts r T1 ∪ verts v T2 ⊆ verts r (T1 ∪ T2) := by
            intro r v T1 T2 hv w hw
            unfold verts at hv hw ⊢
            rw [Finset.mem_union] at hw
            rw [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hv
            rw [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_image]
            rcases hw with hw | hw <;>
              rw [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hw
            · rcases hw with h | ⟨e, he, h⟩ | ⟨e, he, h⟩
              · exact Or.inl h
              · exact Or.inr (Or.inl ⟨e, Finset.mem_union_left _ he, h⟩)
              · exact Or.inr (Or.inr ⟨e, Finset.mem_union_left _ he, h⟩)
            · rcases hw with h | ⟨e, he, h⟩ | ⟨e, he, h⟩
              · subst h
                rcases hv with h | ⟨e, he, h⟩ | ⟨e, he, h⟩
                · exact Or.inl h
                · exact Or.inr (Or.inl ⟨e, Finset.mem_union_left _ he, h⟩)
                · exact Or.inr (Or.inr ⟨e, Finset.mem_union_left _ he, h⟩)
              · exact Or.inr (Or.inl ⟨e, Finset.mem_union_right _ he, h⟩)
              · exact Or.inr (Or.inr ⟨e, Finset.mem_union_right _ he, h⟩)
          have k_vU2 : ∀ (r v : Fin n) (T1 T2 : Edges n),
              verts r (T1 ∪ T2) ⊆ verts r T1 ∪ verts v T2 := by
            intro r v T1 T2 w hw
            unfold verts at hw ⊢
            rw [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hw
            rw [Finset.mem_union, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_image,
              Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_image]
            rcases hw with h | ⟨e, he, h⟩ | ⟨e, he, h⟩
            · exact Or.inl (Or.inl h)
            · rcases Finset.mem_union.1 he with he | he
              · exact Or.inl (Or.inr (Or.inl ⟨e, he, h⟩))
              · exact Or.inr (Or.inr (Or.inl ⟨e, he, h⟩))
            · rcases Finset.mem_union.1 he with he | he
              · exact Or.inl (Or.inr (Or.inr ⟨e, he, h⟩))
              · exact Or.inr (Or.inr (Or.inr ⟨e, he, h⟩))
          have combine : ∀ (r : Fin n) (kr : ℕ) (Y : Finset (Fin n)) (D : Fin n → ℕ) (B L : ℕ)
              (v : Fin n) (S : Finset (Fin n)) (d1 b l : ℕ) (T1 T2 : Edges n),
              S ⊆ Y.erase r → ¬ (∃ w ∈ Y.erase r \ (S ∪ {v}), D w < d1) → b ≤ B → l ≤ L →
              FeasibleDC I r kr ((S ∪ {v}) \ {r}) (fun w => if w = v then (if v ∈ Y.erase r then min d1 (D v) else d1) else D w) b l T1 →
              FeasibleDC I v (kr + lenTo I.len T1 r v) (Y.erase r \ (S ∪ {v})) (fun w => D w - d1)
                (B - b) (L - l) T2 →
              FeasibleDC I r kr Y D B L (T1 ∪ T2) := by
            intro r kr Y D B L v S d1 b l T1 T2 hS hskip hb hl h1 h2
            obtain ⟨⟨r1, c1, y1⟩, A1, hA1T, hA1, hV1, hl1, hD1⟩ := h1
            obtain ⟨⟨r2, c2, y2⟩, A2, hA2T, hA2, hV2, hl2, hD2⟩ := h2
            have hv : v ∈ verts r T1 := by
              by_cases hvr : v = r
              · subst hvr; simp [verts]
              · exact y1 (by simp [hvr])
            have mono1 : ∀ w, Reaches T1 r w → Reaches (T1 ∪ T2) r w := fun w h =>
              Relation.ReflTransGen.mono (r := fun a b => (a, b) ∈ T1) (fun a b h => Finset.mem_union_left T2 h) _ _ h
            have mono2 : ∀ w, Reaches T2 v w → Reaches (T1 ∪ T2) v w := fun w h =>
              Relation.ReflTransGen.mono (r := fun a b => (a, b) ∈ T2) (fun a b h => Finset.mem_union_right T1 h) _ _ h
            have hvu : verts r (T1 ∪ T2) ⊆ verts r T1 ∪ verts v T2 := k_vU2 r v T1 T2
            have hRU : ∀ w ∈ verts r (T1 ∪ T2), Reaches (T1 ∪ T2) r w := by
              intro w hw
              rcases Finset.mem_union.1 (hvu hw) with h | h
              · exact mono1 w (r1 w h)
              · exact (mono1 v (r1 v hv)).trans (mono2 w (r2 w h))
            have sub1 : verts r T1 ⊆ verts r (T1 ∪ T2) := fun w hw => k_vU r v T1 T2 hv (Finset.mem_union_left _ hw)
            have sub2 : verts v T2 ⊆ verts r (T1 ∪ T2) := fun w hw => k_vU r v T1 T2 hv (Finset.mem_union_right _ hw)
            have hYU : Y ⊆ verts r (T1 ∪ T2) := by
              intro w hw
              by_cases hwr : w = r
              · subst hwr; simp [verts]
              by_cases hw1 : w ∈ S ∪ {v}
              · exact sub1 (y1 (by simp only [Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hw1, hwr⟩))
              · exact sub2 (y2 (by simp only [Finset.mem_sdiff, Finset.mem_erase]; exact ⟨⟨hwr, hw⟩, hw1⟩))
            refine ⟨⟨hRU, ?_, hYU⟩, ?_⟩
            · unfold cost
              calc ∑ e ∈ T1 ∪ T2, I.c e.1 e.2 ≤ ∑ e ∈ T1, I.c e.1 e.2 + ∑ e ∈ T2, I.c e.1 e.2 :=
        by
                      have := Finset.sum_union_inter (s₁ := T1) (s₂ := T2) (f := fun e => I.c e.1 e.2)
                      omega
                _ ≤ b + (B - b) := Nat.add_le_add c1 c2
                _ = B := by omega
            · -- shortest-path arborescence of `T1 ∪ T2`
              obtain ⟨A', hA'E, hA', hVA', hlen'⟩ := spt I.len (T1 ∪ T2) r hRU
              refine ⟨A', hA'E, hA', hVA', ?_, ?_⟩
              · -- distance bounds
                have dist1 : ∀ w ∈ verts r A1, lenTo I.len (T1 ∪ T2) r w ≤ lenTo I.len A1 r w := by
                  intro w hw
                  apply lenTo_le
                  exact walk_mono _ _ _ _ _ _ (hA1T.trans Finset.subset_union_left)
                    (lenTo_spec _ _ _ _ (hA1.2.2 w hw))
                have hvA1 : v ∈ verts r A1 := hV1 ▸ hv
                have dist2 : ∀ w ∈ verts v A2, lenTo I.len (T1 ∪ T2) r w ≤
                    lenTo I.len T1 r v + lenTo I.len A2 v w := by
                  intro w hw
                  apply lenTo_le
                  exact walk_append _ _ _ _ _ _ _
                    (walk_mono _ _ _ _ _ _ Finset.subset_union_left (lenTo_spec _ _ _ _ (r1 v hv)))
                    (walk_mono _ _ _ _ _ _ (hA2T.trans Finset.subset_union_right)
                      (lenTo_spec _ _ _ _ (hA2.2.2 w hw)))
                unfold lenSum at hl1 hl2 ⊢
                rw [hVA']
                set V1 := (verts r A1).erase r
                set V2 := (verts v A2).erase v
                have hcov : (verts r (T1 ∪ T2)).erase r ⊆ V1 ∪ (V2 \ V1) := by
                  intro w hw
                  obtain ⟨hwr, hw⟩ := Finset.mem_erase.1 hw
                  rw [Finset.union_sdiff_self_eq_union]
                  rcases Finset.mem_union.1 (hvu hw) with h | h
                  · exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hwr, hV1 ▸ h⟩)
                  · by_cases hwv : w = v
                    · subst hwv; exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hwr, hvA1⟩)
                    · exact Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hwv, hV2 ▸ h⟩)
                calc ∑ w ∈ (verts r (T1 ∪ T2)).erase r, (kr + lenTo I.len A' r w)
                    ≤ ∑ w ∈ (verts r (T1 ∪ T2)).erase r, (kr + lenTo I.len (T1 ∪ T2) r w) := by
                      apply Finset.sum_le_sum; intro w hw
                      have := hlen' w (Finset.mem_of_mem_erase hw); omega
                  _ ≤ ∑ w ∈ V1 ∪ (V2 \ V1), (kr + lenTo I.len (T1 ∪ T2) r w) :=
                      Finset.sum_le_sum_of_subset_of_nonneg hcov (fun _ _ _ => Nat.zero_le _)
                  _ = ∑ w ∈ V1, (kr + lenTo I.len (T1 ∪ T2) r w) +
                        ∑ w ∈ V2 \ V1, (kr + lenTo I.len (T1 ∪ T2) r w) :=
                      Finset.sum_union Finset.disjoint_sdiff
                  _ ≤ ∑ w ∈ V1, (kr + lenTo I.len A1 r w) +
                        ∑ w ∈ V2, (kr + lenTo I.len T1 r v + lenTo I.len A2 v w) := by
                      apply Nat.add_le_add
                      · apply Finset.sum_le_sum; intro w hw
                        have := dist1 w (Finset.mem_of_mem_erase hw); omega
                      · calc ∑ w ∈ V2 \ V1, (kr + lenTo I.len (T1 ∪ T2) r w)
                            ≤ ∑ w ∈ V2 \ V1, (kr + lenTo I.len T1 r v + lenTo I.len A2 v w) := by
                              apply Finset.sum_le_sum; intro w hw
                              have := dist2 w (Finset.mem_of_mem_erase (Finset.mem_sdiff.1 hw).1); omega
                          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
                              (fun _ _ _ => Nat.zero_le _)
                  _ ≤ l + (L - l) := Nat.add_le_add hl1 hl2
                  _ = L := by omega
              · intro w hw
                obtain ⟨hwr, hwY⟩ := Finset.mem_erase.1 hw
                have h0 := hlen' w (hYU hwY)
                by_cases hw1 : w ∈ S ∪ {v}
                · have hm : w ∈ ((S ∪ {v}) \ {r}).erase r := by
                    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton]
                    exact ⟨hwr, hw1, hwr⟩
                  have hd := hD1 w hm
                  have hwA1 : w ∈ verts r A1 := hV1 ▸ y1 (Finset.mem_of_mem_erase hm)
                  have hdd : lenTo I.len (T1 ∪ T2) r w ≤ lenTo I.len A1 r w := by
                    apply lenTo_le
                    exact walk_mono _ _ _ _ _ _ (hA1T.trans Finset.subset_union_left)
                      (lenTo_spec _ _ _ _ (hA1.2.2 w hwA1))
                  by_cases hwv : w = v
                  · subst hwv
                    simp only [if_true, hw] at hd
                    have := min_le_right d1 (D w)
                    omega
                  · simp only [hwv, if_false] at hd
                    omega
                · have hwv : w ≠ v := fun e => hw1 (by simp [e])
                  have hm : w ∈ (Y.erase r \ (S ∪ {v})).erase v :=
                    Finset.mem_erase.2 ⟨hwv, Finset.mem_sdiff.2 ⟨hw, hw1⟩⟩
                  have hd : lenTo I.len A2 v w ≤ D w - d1 := hD2 w hm
                  have hwA2 : w ∈ verts v A2 := hV2 ▸ y2 (Finset.mem_of_mem_erase hm)
                  have hdd : lenTo I.len (T1 ∪ T2) r w ≤ lenTo I.len T1 r v + lenTo I.len A2 v w := by
                    apply lenTo_le
                    exact walk_append _ _ _ _ _ _ _
                      (walk_mono _ _ _ _ _ _ Finset.subset_union_left (lenTo_spec _ _ _ _ (r1 v hv)))
                      (walk_mono _ _ _ _ _ _ (hA2T.trans Finset.subset_union_right)
                        (lenTo_spec _ _ _ _ (hA2.2.2 w hwA2)))
                  have hvd : lenTo I.len T1 r v ≤ d1 := by
                    by_cases hvr : v = r
                    · subst hvr; rw [lenTo_self]; exact Nat.zero_le _
                    · have hm1 : v ∈ ((S ∪ {v}) \ {r}).erase r := by simp [hvr]
                      have := hD1 v hm1
                      simp only [if_true] at this
                      have hle : (if v ∈ Y.erase r then min d1 (D v) else d1) ≤ d1 := by
                        split_ifs
                        · exact min_le_left _ _
                        · exact le_rfl
                      have hvA1 : v ∈ verts r A1 := hV1 ▸ hv
                      have hT1 : lenTo I.len T1 r v ≤ lenTo I.len A1 r v :=
                        lenTo_le _ _ _ _ _ (walk_mono _ _ _ _ _ _ hA1T (lenTo_spec _ _ _ _ (hA1.2.2 v hvA1)))
                      omega
                  have hDw : ¬ D w < d1 := fun h => hskip ⟨w, Finset.mem_sdiff.2 ⟨hw, hw1⟩, h⟩
                  omega
          have hYr : ∀ (Y : Finset (Fin n)) (r : Fin n), Y.erase r = ∅ → Y ⊆ {r} := by
            intro Y r hY0 w hw
            by_cases hwr : w = r
            · simp [hwr]
            · have : w ∈ Y.erase r := Finset.mem_erase.2 ⟨hwr, hw⟩
              rw [hY0] at this; simp at this
          have sound : ∀ m, 1 ≤ m → ∀ (r : Fin n) (kr : ℕ) (Y : Finset (Fin n)) (D : Fin n → ℕ) (B L : ℕ)
              (X : Finset (Fin n)) (T : Edges n),
              (rgdc I 1 .enum m r kr Y D B L X).1 = some T → FeasibleDC I r kr Y D B L T := by
            intro m hm
            induction m, hm using Nat.le_induction with
            | base =>
              intro r kr Y D B L X T hT
              by_cases hcap : capImp 1 (0 + 1) < ((Y.erase r).card : ℝ)
              · simp only [rgdc, hcap, if_true] at hT; cases hT
              simp only [rgdc, hcap, if_false, if_true] at hT
              by_cases hY0 : Y.erase r = ∅
              · rw [if_pos hY0, hcbeq] at hT
                rcases (cb X r _ (some ∅) 0).1 T hT with h | h
                · cases h; exact fs0 r kr Y D B L (hYr Y r hY0)
                · obtain ⟨v, -, hv⟩ := List.mem_filterMap.1 h
                  by_cases hb : (decide (v = r) || decide (B < I.c r v) || decide (L < kr + I.len r v)) = true
                  · rw [if_pos hb] at hv; cases hv
                  · rw [if_neg hb] at hv; cases hv
                    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hb
                    exact fs1 r kr Y D B L v (fun e => hb.1.1 e.symm) hb.1.2 hb.2
                      ((hYr Y r hY0).trans (by simp)) (fun w hw => by rw [hY0] at hw; simp at hw)
              · rw [if_neg hY0] at hT
                split at hT
                · rename_i v hv
                  have hYv := Finset.toList_eq_singleton_iff.1 hv
                  split_ifs at hT with hc
                  cases hT
                  have hvr : r ≠ v := by
                    intro e; have : v ∈ Y.erase r := by rw [hYv]; simp
                    simp [e] at this
                  refine fs1 r kr Y D B L v hvr hc.1 hc.2.1 ?_ ?_
                  · intro w hw
                    by_cases hwr : w = r
                    · simp [hwr]
                    · have : w ∈ Y.erase r := Finset.mem_erase.2 ⟨hwr, hw⟩
                      rw [hYv] at this; simp at this; simp [this]
                  · intro w hw; rw [hYv] at hw; simp at hw; subst hw; exact hc.2.2
                · cases hT
            | succ m hm ih =>
              intro r kr Y D B L X T hT
              by_cases hcap : capImp 1 (m + 1) < ((Y.erase r).card : ℝ)
              · simp only [rgdc, hcap, if_true] at hT; cases hT
              have hm0 : m ≠ 0 := by omega
              simp only [rgdc, hcap, hm0, if_false] at hT
              rw [hcbeq] at hT
              rcases (cb X r _ _ 0).1 T hT with h | h
              · by_cases hY0 : Y.erase r = ∅
                · rw [if_pos hY0] at h; cases h; exact fs0 r kr Y D B L (hYr Y r hY0)
                · rw [if_neg hY0] at h; cases h
              · rw [candMem] at h
                obtain ⟨v, S, d1, b, l, T1, T2, hS, hd1, hskip, hb, hl, hT1, hT2, rfl⟩ := h
                exact combine r kr Y D B L v S d1 b l T1 T2 hS hskip hb hl (ih _ _ _ _ _ _ _ _ hT1)
                  (ih _ _ _ _ _ _ _ _ hT2)
          have k_acyc : ∀ (A : Edges n) (r : Fin n), IsArbo r A → ∀ w, Reaches A r w →
              ¬ Relation.TransGen (fun a b => (a, b) ∈ A) w w := by
            intro A r hA w hw
            induction hw with
            | refl =>
              intro h
              obtain ⟨b, -, hb⟩ := Relation.TransGen.tail'_iff.1 h
              exact hA.1 _ hb rfl
            | @tail q w _ hqw ih =>
              intro h
              obtain ⟨b, hb1, hb2⟩ := Relation.TransGen.tail'_iff.1 h
              have hbq : b = q := by
                have := hA.2.1 _ hb2 _ hqw rfl
                simp only [Prod.mk.injEq] at this; exact this.1
              subst hbq
              exact ih (Relation.TransGen.head' hqw hb1)
          have k_reach_mem : ∀ (A : Edges n) (r w : Fin n), Reaches A r w → w ∈ verts r A := by
            intro A r w h
            rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 h with h | ⟨c, _, hc⟩
            · subst h; simp [verts]
            · simp only [verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
              exact Or.inr (Or.inr ⟨(c, w), hc, rfl⟩)
          have k_inedge : ∀ (A : Edges n) (r w : Fin n), Reaches A r w → w ≠ r → ∃ q, (q, w) ∈ A := by
            intro A r w h hne
            rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 h with h | ⟨c, _, hc⟩
            · exact absurd h hne
            · exact ⟨c, hc⟩
          have k_arbo_card_eq : ∀ (A : Edges n) (r : Fin n), IsArbo r A →
              A.card = ((verts r A).erase r).card := by
            intro A r hA
            have himg : A.image Prod.snd = (verts r A).erase r := by
              ext w
              simp only [Finset.mem_image, Finset.mem_erase]
              constructor
              · rintro ⟨e, he, rfl⟩
                refine ⟨hA.1 e he, ?_⟩
                simp only [verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
                exact Or.inr (Or.inr ⟨e, he, rfl⟩)
              · rintro ⟨hne, hw⟩
                obtain ⟨q, hq⟩ := k_inedge A r w (hA.2.2 w hw) hne
                exact ⟨_, hq, rfl⟩
            rw [← himg, Finset.card_image_of_injOn]
            intro e he e' he' h
            exact hA.2.1 e he e' he' h
          have k_sep : ∀ (A : Edges n) (r : Fin n), IsArbo r A → ∀ c0 : ℕ, 1 ≤ c0 →
              2 * A.card ≤ 3 * c0 + 2 →
              ∃ v ∈ verts r A, ∃ R : Finset (Fin n), r ∉ R ∧ v ∉ R ∧ R ⊆ verts r A ∧
                (∀ e ∈ A, e.1 ∈ R → e.2 ∈ R) ∧ (∀ e ∈ A, e.2 ∈ R → e.1 ∈ R ∨ e.1 = v) ∧
                A.card ≤ c0 + R.card ∧ R.card ≤ c0 := by
            classical
            intro A r hA c0 hc0 hk2
            clear * - k_acyc k_reach_mem k_inedge k_arbo_card_eq hA hc0 hk2
            by_cases hk : A.card ≤ c0
            · refine ⟨r, Finset.mem_insert_self r _, ∅, Finset.notMem_empty r, Finset.notMem_empty r,
                Finset.empty_subset _, fun e _ h => absurd h (Finset.notMem_empty _),
                fun e _ h => absurd h (Finset.notMem_empty _), by rw [Finset.card_empty]; omega,
                by rw [Finset.card_empty]; exact Nat.zero_le _⟩
            set a := A.card - c0 with ha
            have ha1 : 1 ≤ a := by omega
            set Desc : Fin n → Finset (Fin n) := fun u => Finset.univ.filter (fun w => Reaches A u w) with hDesc
            have memD : ∀ u w, w ∈ Desc u ↔ Reaches A u w := by intro u w; simp [hDesc]
            set U := (verts r A).filter (fun u => a + 1 ≤ (Desc u).card) with hU
            have hDr : Desc r = verts r A := by
              ext w; rw [memD]; exact ⟨k_reach_mem A r w, hA.2.2 w⟩
            have hcardv : (verts r A).card = A.card + 1 := by
              rw [k_arbo_card_eq A r hA, Finset.card_erase_add_one (show r ∈ verts r A from Finset.mem_insert_self r _)]
            have hrU : r ∈ U := by
              exact Finset.mem_filter.2 ⟨Finset.mem_insert_self r _, by rw [hDr, hcardv]; omega⟩
            obtain ⟨u, huU, hmin⟩ := Finset.exists_min_image U (fun u => (Desc u).card) ⟨r, hrU⟩
            rw [hU, Finset.mem_filter] at huU
            obtain ⟨huV, hua⟩ := huU
            have hur : Reaches A r u := hA.2.2 u huV
            set Ch := (A.filter (fun e => e.1 = u)).image Prod.snd with hCh
            have hch : ∀ c ∈ Ch, (u, c) ∈ A := by
              intro c hc
              rw [hCh, Finset.mem_image] at hc
              obtain ⟨e, he, rfl⟩ := hc
              rw [Finset.mem_filter] at he
              have : e = (e.1, e.2) := rfl
              rw [← he.2]; exact he.1
            have hnotin : ∀ c ∈ Ch, u ∉ Desc c := by
              intro c hc h
              rw [memD] at h
              exact k_acyc A r hA u hur (Relation.TransGen.head' (hch c hc) h)
            have hsubD : ∀ c ∈ Ch, Desc c ⊆ Desc u := by
              intro c hc w hw
              rw [memD] at hw ⊢
              exact Relation.ReflTransGen.head (hch c hc) hw
            have hDc : ∀ c ∈ Ch, (Desc c).card ≤ a := by
              intro c hc
              by_contra hcon
              have hcU : c ∈ U := by
                rw [hU, Finset.mem_filter]
                refine ⟨k_reach_mem A r c (hur.tail (hch c hc)), by omega⟩
              have h1 := hmin c hcU
              have h2 : (Desc c).card < (Desc u).card := by
                apply Finset.card_lt_card
                rw [Finset.ssubset_iff_of_subset (hsubD c hc)]
                exact ⟨u, by rw [memD]; exact Relation.ReflTransGen.refl, hnotin c hc⟩
              omega
            have htot : a ≤ (Ch.biUnion Desc).card := by
              have hsub : Desc u ⊆ insert u (Ch.biUnion Desc) := by
                intro w hw
                rw [memD] at hw
                rcases (Relation.ReflTransGen.cases_head_iff).1 hw with h | ⟨c, hc, hcw⟩
                · rw [h]; exact Finset.mem_insert_self _ _
                · apply Finset.mem_insert_of_mem
                  rw [Finset.mem_biUnion]
                  refine ⟨c, ?_, by rw [memD]; exact hcw⟩
                  rw [hCh, Finset.mem_image]
                  exact ⟨(u, c), by simp [hc], rfl⟩
              have := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
              omega
            have greedy : ∀ F ⊆ Ch, a ≤ (F.biUnion Desc).card → ∃ G ⊆ F, a ≤ (G.biUnion Desc).card ∧
                (G.biUnion Desc).card ≤ max a (2 * a - 2) := by
              intro F
              induction F using Finset.induction_on with
              | empty => intro _ h; simp at h; omega
              | @insert x F hx ih =>
                intro hF h
                have hxC : x ∈ Ch := hF (Finset.mem_insert_self _ _)
                by_cases hF' : a ≤ (F.biUnion Desc).card
                · obtain ⟨G, hG, h1, h2⟩ := ih (fun y hy => hF (Finset.mem_insert_of_mem hy)) hF'
                  exact ⟨G, hG.trans (Finset.subset_insert _ _), h1, h2⟩
                · by_cases hxa : (Desc x).card = a
                  · refine ⟨{x}, by simp, by simp [hxa], by simp [hxa]⟩
                  · refine ⟨insert x F, subset_rfl, h, ?_⟩
                    have h1 := hDc x hxC
                    rw [Finset.biUnion_insert]
                    have := Finset.card_union_le (Desc x) (F.biUnion Desc)
                    apply le_max_of_le_right
                    omega
            obtain ⟨G, hG, hG1, hG2⟩ := greedy Ch subset_rfl htot
            refine ⟨u, huV, G.biUnion Desc, ?_, ?_, ?_, ?_, ?_, by omega, ?_⟩
            · intro h
              rw [Finset.mem_biUnion] at h
              obtain ⟨c, hc, h⟩ := h
              rw [memD] at h
              rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 h with h' | ⟨q, _, hq⟩
              · exact hA.1 _ (hch c (hG hc)) h'.symm
              · exact hA.1 _ hq rfl
            · intro h
              rw [Finset.mem_biUnion] at h
              obtain ⟨c, hc, h⟩ := h
              exact hnotin c (hG hc) h
            · intro w h
              rw [Finset.mem_biUnion] at h
              obtain ⟨c, hc, h⟩ := h
              rw [memD] at h
              exact k_reach_mem A r w ((hur.tail (hch c (hG hc))).trans h)
            · intro e he h
              rw [Finset.mem_biUnion] at h ⊢
              obtain ⟨c, hc, h⟩ := h
              refine ⟨c, hc, ?_⟩
              rw [memD] at h ⊢
              exact h.tail he
            · intro e he h
              rw [Finset.mem_biUnion] at h
              obtain ⟨c, hc, h⟩ := h
              rw [memD] at h
              rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 h with h' | ⟨q, hq1, hq⟩
              · right
                have := hA.2.1 _ he _ (hch c (hG hc)) h'
                rw [this]
              · left
                have := hA.2.1 _ he _ hq rfl
                rw [Finset.mem_biUnion]
                refine ⟨c, hc, ?_⟩
                rw [memD, this]; exact hq1
            · rcases le_max_iff.1 hG2 with h | h <;> omega
          have k_walk_reach : ∀ (len : Fin n → Fin n → ℕ) (T : Edges n) (r w : Fin n),
              Reaches T r w → ∃ m, HasWalkOfLength len T r w m := by
            intro len T r w h
            induction h with
            | refl => exact ⟨0, Relation.ReflTransGen.refl⟩
            | @tail b c _ hst ih =>
              obtain ⟨m, hm⟩ := ih
              exact ⟨m + len b c, Relation.ReflTransGen.tail hm (show WalkStep len T (b, m) (c, m + len b c) from ⟨hst, rfl⟩)⟩
          have k_reach_walk : ∀ (len : Fin n → Fin n → ℕ) (T : Edges n) (r w : Fin n) (m : ℕ),
              HasWalkOfLength len T r w m → Reaches T r w := by
            intro len T r w m h
            have : ∀ p, Relation.ReflTransGen (WalkStep len T) (r, 0) p → Reaches T r p.1 := by
              intro p hp
              induction hp with
              | refl => exact Relation.ReflTransGen.refl
              | tail _ hst ih => exact ih.tail hst.1
            exact this _ h
          have k_lenTo_le : ∀ (len : Fin n → Fin n → ℕ) (T : Edges n) (r w : Fin n) (m : ℕ),
              HasWalkOfLength len T r w m → lenTo len T r w ≤ m := by
            classical
            intro len T r w m h
            have hex : ∃ m, HasWalkOfLength len T r w m := ⟨m, h⟩
            unfold lenTo; rw [dif_pos hex]; exact Nat.find_min' hex h
          have k_lenTo_spec : ∀ (len : Fin n → Fin n → ℕ) (T : Edges n) (r w : Fin n),
              Reaches T r w → HasWalkOfLength len T r w (lenTo len T r w) := by
            classical
            intro len T r w h
            have hex := k_walk_reach len T r w h
            unfold lenTo; rw [dif_pos hex]; exact Nat.find_spec hex
          have k_lenTo_self : ∀ (len : Fin n → Fin n → ℕ) (T : Edges n) (r : Fin n),
              lenTo len T r r = 0 := by
            intro len T r
            have := k_lenTo_le len T r r 0 Relation.ReflTransGen.refl
            omega
          have k_walk_mono : ∀ (len : Fin n → Fin n → ℕ) (T T' : Edges n) (r w : Fin n) (m : ℕ),
              T ⊆ T' → HasWalkOfLength len T r w m → HasWalkOfLength len T' r w m := by
            intro len T T' r w m hs h
            exact Relation.ReflTransGen.mono (r := WalkStep len T) (fun p q (h : WalkStep len T p q) => (⟨hs h.1, h.2⟩ : WalkStep len T' p q)) _ _ h
          have k_walk_A1 : ∀ (len : Fin n → Fin n → ℕ) (A : Edges n) (R : Finset (Fin n)) (r w : Fin n) (m : ℕ),
              (∀ e ∈ A, e.1 ∈ R → e.2 ∈ R) → HasWalkOfLength len A r w m → w ∉ R →
              HasWalkOfLength len (A.filter (fun e => e.2 ∉ R)) r w m := by
            intro len A R r w m hdown h hw
            have : ∀ p, Relation.ReflTransGen (WalkStep len A) (r, 0) p → p.1 ∉ R →
                Relation.ReflTransGen (WalkStep len (A.filter (fun e => e.2 ∉ R))) (r, 0) p := by
              intro p hp
              induction hp with
              | refl => intro _; exact Relation.ReflTransGen.refl
              | @tail b c _ hst ih =>
                intro hc
                have hb : b.1 ∉ R := fun hb => hc (hdown _ hst.1 hb)
                exact (ih hb).tail ⟨Finset.mem_filter.2 ⟨hst.1, hc⟩, hst.2⟩
            exact this _ h hw
          have k_walk_A2 : ∀ (len : Fin n → Fin n → ℕ) (A : Edges n) (R : Finset (Fin n)) (r v w : Fin n) (m : ℕ),
              r ∉ R → (∀ e ∈ A, e.2 ∈ R → e.1 ∈ R ∨ e.1 = v) → HasWalkOfLength len A r w m → w ∈ R →
              ∃ m1 m2, m = m1 + m2 ∧ HasWalkOfLength len A r v m1 ∧
                HasWalkOfLength len (A.filter (fun e => e.2 ∈ R)) v w m2 := by
            intro len A R r v w m hr hup h hw
            have : ∀ p, Relation.ReflTransGen (WalkStep len A) (r, 0) p → p.1 ∈ R →
                ∃ m1 m2, p.2 = m1 + m2 ∧ HasWalkOfLength len A r v m1 ∧
                HasWalkOfLength len (A.filter (fun e => e.2 ∈ R)) v p.1 m2 := by
              intro p hp
              induction hp with
              | refl => intro h; exact absurd h hr
              | @tail b c hb hst ih =>
                intro hc
                rcases hup _ hst.1 hc with h1 | h1
                · obtain ⟨m1, m2, he, hw1, hw2⟩ := ih h1
                  refine ⟨m1, m2 + len b.1 c.1, by rw [hst.2, he]; ring, hw1, ?_⟩
                  exact hw2.tail (show WalkStep len _ (b.1, m2) (c.1, m2 + len b.1 c.1) from
                    ⟨Finset.mem_filter.2 ⟨hst.1, hc⟩, rfl⟩)
                · refine ⟨b.2, len b.1 c.1, hst.2, ?_, ?_⟩
                  · rw [← h1]; exact hb
                  · rw [← h1]
                    exact Relation.ReflTransGen.single (show WalkStep len _ (b.1, 0) (c.1, len b.1 c.1) from
                      ⟨Finset.mem_filter.2 ⟨hst.1, hc⟩, by simp⟩)
            exact this _ h hw
          have keystep : ∀ m, 1 ≤ m → (∀ (r : Fin n) (kr : ℕ) (Y : Finset (Fin n)) (D : Fin n → ℕ) (B L : ℕ)
              (X : Finset (Fin n)) (A : Edges n),
              CompatibleDC I r kr Y D B L ((3 / 2 : ℝ) ^ m) A →
              ∃ T, (rgdc I 1 .enum m r kr Y D B L X).1 = some T ∧
                FeasibleDC I r kr Y D B L T ∧ fX I.f X r A ≤ (m : ℝ) * fX I.f X r T) →
              ∀ (r : Fin n) (kr : ℕ) (Y : Finset (Fin n)) (D : Fin n → ℕ) (B L : ℕ)
              (X : Finset (Fin n)) (A : Edges n),
              CompatibleDC I r kr Y D B L ((3 / 2 : ℝ) ^ (m + 1)) A →
              ∃ v S d1 b l T1 T2, S ⊆ Y.erase r ∧ d1 ≤ L ∧
                    ¬ (∃ w ∈ Y.erase r \ (S ∪ {v}), D w < d1) ∧ b ≤ B ∧ l ≤ L ∧
                    (rgdc I 1 .enum m r kr ((S ∪ {v}) \ {r})
                      (fun w => if w = v then (if v ∈ Y.erase r then min d1 (D v) else d1) else D w) b l X).1
                      = some T1 ∧
                    (rgdc I 1 .enum m v (kr + lenTo I.len T1 r v) (Y.erase r \ (S ∪ {v})) (fun w => D w - d1)
                      (B - b) (L - l) (X ∪ verts r T1)).1 = some T2 ∧
                    fX I.f X r A ≤ ((m + 1 : ℕ) : ℝ) * fX I.f X r (T1 ∪ T2) := by
            intro m hm ih r kr Y D B L X A hA
            clear * - hmono hsub k_acyc k_reach_mem k_inedge k_arbo_card_eq k_sep k_walk_reach k_reach_walk k_lenTo_le k_lenTo_spec k_lenTo_self k_walk_mono k_walk_A1 k_walk_A2 k_vU ih hA hm
            obtain ⟨⟨hArbo, hYA, hcardA, hcostA⟩, hlenA, hDA⟩ := hA
            have hC1 : (3/2 : ℝ) ≤ (3/2 : ℝ) ^ m := by
              calc (3/2 : ℝ) = (3/2) ^ 1 := by norm_num
                _ ≤ (3/2) ^ m := pow_le_pow_right₀ (by norm_num) hm
            have hc01 : 1 ≤ ⌊(3/2 : ℝ) ^ m⌋₊ := Nat.le_floor (by push_cast; linarith)
            have hc0le : (⌊(3/2 : ℝ) ^ m⌋₊ : ℝ) ≤ (3/2 : ℝ) ^ m := Nat.floor_le (by linarith)
            have hk2 : 2 * A.card ≤ 3 * ⌊(3/2 : ℝ) ^ m⌋₊ + 2 := by
              have h1 : (A.card : ℝ) ≤ (3/2 : ℝ) ^ m * (3/2) := by rw [← pow_succ]; exact hcardA
              have h2 := Nat.lt_floor_add_one ((3/2 : ℝ) ^ m)
              have h3 : ((2 * A.card : ℕ) : ℝ) < ((3 * ⌊(3/2 : ℝ) ^ m⌋₊ + 3 : ℕ) : ℝ) := by
                push_cast; nlinarith
              have h4 : 2 * A.card < 3 * ⌊(3/2 : ℝ) ^ m⌋₊ + 3 := by exact_mod_cast h3
              omega
            obtain ⟨v, hvV, R, hrR, hvR, hRV, hdown, hup, hcard1, hcard2⟩ :=
              k_sep A r hArbo _ hc01 hk2
            have hreach1 : ∀ w, Reaches A r w → w ∉ R → Reaches (A.filter (fun e => e.2 ∉ R)) r w := by
              intro w hw hwR
              obtain ⟨m', hm'⟩ := k_walk_reach I.len A r w hw
              exact k_reach_walk I.len _ r w _ (k_walk_A1 I.len A R r w m' hdown hm' hwR)
            have hreach2 : ∀ w, Reaches A r w → w ∈ R → Reaches (A.filter (fun e => e.2 ∈ R)) v w := by
              intro w hw hwR
              obtain ⟨m', hm'⟩ := k_walk_reach I.len A r w hw
              obtain ⟨m1, m2, -, -, h2⟩ := k_walk_A2 I.len A R r v w m' hrR hup hm' hwR
              exact k_reach_walk I.len _ v w _ h2
            have hlen1 : ∀ w ∈ verts r A, w ∉ R →
                lenTo I.len (A.filter (fun e => e.2 ∉ R)) r w ≤ lenTo I.len A r w := by
              intro w hw hwR
              exact k_lenTo_le _ _ _ _ _ (k_walk_A1 I.len A R r w _ hdown
                (k_lenTo_spec I.len A r w (hArbo.2.2 w hw)) hwR)
            have hlen2 : ∀ w ∈ R, lenTo I.len A r v + lenTo I.len (A.filter (fun e => e.2 ∈ R)) v w
                ≤ lenTo I.len A r w := by
              intro w hwR
              obtain ⟨m1, m2, he, h1, h2⟩ := k_walk_A2 I.len A R r v w _ hrR hup
                (k_lenTo_spec I.len A r w (hArbo.2.2 w (hRV hwR))) hwR
              have := k_lenTo_le _ _ _ _ _ h1
              have := k_lenTo_le _ _ _ _ _ h2
              omega
            have hv1 : ∀ w ∈ verts r (A.filter (fun e => e.2 ∉ R)), w ∈ verts r A ∧ w ∉ R := by
              intro w hw
              simp only [verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
                Finset.mem_filter] at hw ⊢
              rcases hw with rfl | ⟨e, ⟨he, heR⟩, rfl⟩ | ⟨e, ⟨he, heR⟩, rfl⟩
              · exact ⟨Or.inl rfl, hrR⟩
              · exact ⟨Or.inr (Or.inl ⟨e, he, rfl⟩), fun h => heR (hdown e he h)⟩
              · exact ⟨Or.inr (Or.inr ⟨e, he, rfl⟩), heR⟩
            have hv2 : ∀ w ∈ (verts v (A.filter (fun e => e.2 ∈ R))).erase v, w ∈ R := by
              intro w hw
              rw [Finset.mem_erase] at hw
              obtain ⟨hne, hw⟩ := hw
              simp only [verts, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
                Finset.mem_filter] at hw
              rcases hw with rfl | ⟨e, ⟨he, heR⟩, rfl⟩ | ⟨e, ⟨he, heR⟩, rfl⟩
              · exact absurd rfl hne
              · rcases hup e he heR with h | h
                · exact h
                · exact absurd h hne
              · exact heR
            have arbo1 : IsArbo r (A.filter (fun e => e.2 ∉ R)) := by
              refine ⟨fun e he => hArbo.1 e (Finset.mem_filter.1 he).1,
                fun e he e' he' h => hArbo.2.1 e (Finset.mem_filter.1 he).1 e' (Finset.mem_filter.1 he').1 h,
                fun w hw => ?_⟩
              obtain ⟨h1, h2⟩ := hv1 w hw
              exact hreach1 w (hArbo.2.2 w h1) h2
            have arbo2 : IsArbo v (A.filter (fun e => e.2 ∈ R)) := by
              refine ⟨fun e he h => hvR (h ▸ (Finset.mem_filter.1 he).2),
                fun e he e' he' h => hArbo.2.1 e (Finset.mem_filter.1 he).1 e' (Finset.mem_filter.1 he').1 h,
                fun w hw => ?_⟩
              by_cases hwv : w = v
              · rw [hwv]; exact Relation.ReflTransGen.refl
              · have hwR := hv2 w (Finset.mem_erase.2 ⟨hwv, hw⟩)
                exact hreach2 w (hArbo.2.2 w (hRV hwR)) hwR
            have hA2card : (A.filter (fun e => e.2 ∈ R)).card = R.card := by
              have himg : (A.filter (fun e => e.2 ∈ R)).image Prod.snd = R := by
                ext w
                simp only [Finset.mem_image, Finset.mem_filter]
                constructor
                · rintro ⟨e, ⟨_, h⟩, rfl⟩; exact h
                · intro hw
                  have hwr : w ≠ r := fun h => hrR (h ▸ hw)
                  obtain ⟨q, hq⟩ := k_inedge A r w (hArbo.2.2 w (hRV hw)) hwr
                  exact ⟨_, ⟨hq, hw⟩, rfl⟩
              have hinj : Set.InjOn Prod.snd ((A.filter (fun e => e.2 ∈ R)) : Set (Fin n × Fin n)) := by
                intro e he e' he' h
                exact hArbo.2.1 e (Finset.mem_filter.1 he).1 e' (Finset.mem_filter.1 he').1 h
              have := Finset.card_image_of_injOn hinj
              rw [himg] at this
              exact this.symm
            have hcardsum := Finset.card_filter_add_card_filter_not (s := A) (fun e => e.2 ∈ R)
            have hcostsum : cost I.c (A.filter (fun e => e.2 ∈ R)) + cost I.c (A.filter (fun e => e.2 ∉ R))
                = cost I.c A := by
              unfold cost; exact Finset.sum_filter_add_sum_filter_not _ _ _
            have hlsum1 : lenSum I.len kr r (A.filter (fun e => e.2 ∉ R)) +
                ∑ w ∈ R, (kr + lenTo I.len A r w) ≤ lenSum I.len kr r A := by
              unfold lenSum
              have hdisj : Disjoint ((verts r (A.filter (fun e => e.2 ∉ R))).erase r) R := by
                rw [Finset.disjoint_left]
                intro w hw hwR
                exact (hv1 w (Finset.mem_of_mem_erase hw)).2 hwR
              calc ∑ w ∈ (verts r (A.filter (fun e => e.2 ∉ R))).erase r,
                    (kr + lenTo I.len (A.filter (fun e => e.2 ∉ R)) r w) + ∑ w ∈ R, (kr + lenTo I.len A r w)
                  ≤ ∑ w ∈ (verts r (A.filter (fun e => e.2 ∉ R))).erase r, (kr + lenTo I.len A r w)
                      + ∑ w ∈ R, (kr + lenTo I.len A r w) := by
                    apply Nat.add_le_add_right
                    apply Finset.sum_le_sum
                    intro w hw
                    have := hv1 w (Finset.mem_of_mem_erase hw)
                    have := hlen1 w this.1 this.2
                    omega
                _ = ∑ w ∈ (verts r (A.filter (fun e => e.2 ∉ R))).erase r ∪ R, (kr + lenTo I.len A r w) :=
                    (Finset.sum_union hdisj).symm
                _ ≤ ∑ w ∈ (verts r A).erase r, (kr + lenTo I.len A r w) := by
                    apply Finset.sum_le_sum_of_subset
                    intro w hw
                    rcases Finset.mem_union.1 hw with h | h
                    · rw [Finset.mem_erase] at h ⊢
                      exact ⟨h.1, (hv1 w h.2).1⟩
                    · rw [Finset.mem_erase]
                      exact ⟨fun e => hrR (e ▸ h), hRV h⟩
            have hlsum2 : ∀ k', k' ≤ kr + lenTo I.len A r v →
                lenSum I.len k' v (A.filter (fun e => e.2 ∈ R)) ≤ ∑ w ∈ R, (kr + lenTo I.len A r w) := by
              intro k' hk'
              unfold lenSum
              calc ∑ w ∈ (verts v (A.filter (fun e => e.2 ∈ R))).erase v,
                    (k' + lenTo I.len (A.filter (fun e => e.2 ∈ R)) v w)
                  ≤ ∑ w ∈ (verts v (A.filter (fun e => e.2 ∈ R))).erase v, (kr + lenTo I.len A r w) := by
                    apply Finset.sum_le_sum
                    intro w hw
                    have := hlen2 w (hv2 w hw)
                    omega
                _ ≤ ∑ w ∈ R, (kr + lenTo I.len A r w) := Finset.sum_le_sum_of_subset hv2
            have hd1L : lenTo I.len A r v ≤ L := by
              by_cases hvr : v = r
              · rw [hvr, k_lenTo_self]; exact Nat.zero_le _
              · have := Finset.single_le_sum (f := fun w => kr + lenTo I.len A r w)
                  (fun _ _ => Nat.zero_le _) (Finset.mem_erase.2 ⟨hvr, hvV⟩)
                unfold lenSum at hlenA
                omega
            have hYV : ∀ w ∈ Y.erase r, w ∈ verts r A := fun w hw => hYA (Finset.mem_of_mem_erase hw)
            -- the left call
            have compat1 : CompatibleDC I r kr (((Y.erase r).filter (fun w => w ∉ R) ∪ {v}) \ {r})
                (fun w => if w = v then (if v ∈ Y.erase r then min (lenTo I.len A r v) (D v)
                  else lenTo I.len A r v) else D w)
                (cost I.c (A.filter (fun e => e.2 ∉ R))) (lenSum I.len kr r (A.filter (fun e => e.2 ∉ R)))
                ((3/2 : ℝ) ^ m) (A.filter (fun e => e.2 ∉ R)) := by
              refine ⟨⟨arbo1, ?_, ?_, le_rfl⟩, le_rfl, ?_⟩
              · intro w hw
                simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton] at hw
                rcases hw.1 with ⟨hwY, hwR⟩ | rfl
                · exact k_reach_mem _ r w (hreach1 w (hArbo.2.2 w (hYV w hwY)) hwR)
                · exact k_reach_mem _ r w (hreach1 w (hArbo.2.2 w hvV) hvR)
              · have : (A.filter (fun e => e.2 ∉ R)).card ≤ ⌊(3/2 : ℝ) ^ m⌋₊ := by omega
                calc ((A.filter (fun e => e.2 ∉ R)).card : ℝ) ≤ (⌊(3/2 : ℝ) ^ m⌋₊ : ℝ) := by exact_mod_cast this
                  _ ≤ _ := hc0le
              · intro w hw
                simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter,
                  Finset.mem_singleton] at hw
                obtain ⟨hwr, hw1, -⟩ := hw
                by_cases hwv : w = v
                · subst hwv
                  dsimp only
                  rw [if_pos rfl]
                  have h1 := hlen1 w hvV hvR
                  split_ifs with hvY
                  · exact le_min h1 (h1.trans (hDA w hvY))
                  · exact h1
                · dsimp only
                  rw [if_neg hwv]
                  rcases hw1 with ⟨hwY, hwR⟩ | h
                  · exact (hlen1 w (hYV w (Finset.mem_erase.2 hwY)) hwR).trans (hDA w (Finset.mem_erase.2 hwY))
                  · exact absurd h hwv
            obtain ⟨T1, hT1, hF1, hf1⟩ := ih r kr _ _ _ _ X _ compat1
            have hT1v : lenTo I.len T1 r v ≤ lenTo I.len A r v ∧ v ∈ verts r T1 := by
              by_cases hvr : v = r
              · subst hvr; rw [k_lenTo_self]; exact ⟨Nat.zero_le _, by simp [verts]⟩
              · obtain ⟨⟨-, -, hY1T1⟩, A1', hA1'sub, hA1'arbo, hA1'verts, -, hA1'D⟩ := hF1
                have hvY1 : v ∈ (((Y.erase r).filter (fun w => w ∉ R) ∪ {v}) \ {r}) := by
                  simp [hvr]
                have hvT1 := hY1T1 hvY1
                refine ⟨?_, hvT1⟩
                have h1 := hA1'D v (Finset.mem_erase.2 ⟨hvr, hvY1⟩)
                simp only [if_true] at h1
                have h2 : lenTo I.len A1' r v ≤ lenTo I.len A r v := by
                  refine h1.trans ?_
                  split_ifs
                  · exact min_le_left _ _
                  · exact le_rfl
                refine le_trans (k_lenTo_le _ _ _ _ _ (k_walk_mono _ _ _ _ _ _ hA1'sub
                  (k_lenTo_spec I.len A1' r v (hA1'arbo.2.2 v (hA1'verts ▸ hvT1))))) h2
            -- the right call
            have compat2 : CompatibleDC I v (kr + lenTo I.len T1 r v)
                (Y.erase r \ ((Y.erase r).filter (fun w => w ∉ R) ∪ {v})) (fun w => D w - lenTo I.len A r v)
                (B - cost I.c (A.filter (fun e => e.2 ∉ R)))
                (L - lenSum I.len kr r (A.filter (fun e => e.2 ∉ R)))
                ((3/2 : ℝ) ^ m) (A.filter (fun e => e.2 ∈ R)) := by
              have hY2 : ∀ w ∈ Y.erase r \ ((Y.erase r).filter (fun w => w ∉ R) ∪ {v}), w ∈ R ∧ w ∈ Y.erase r := by
                intro w hw
                simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton,
                  not_or, not_and, not_not] at hw
                exact ⟨hw.2.1 hw.1, hw.1⟩
              refine ⟨⟨arbo2, ?_, ?_, ?_⟩, ?_, ?_⟩
              · intro w hw
                obtain ⟨hwR, hwY⟩ := hY2 w hw
                exact k_reach_mem _ v w (hreach2 w (hArbo.2.2 w (hRV hwR)) hwR)
              · calc ((A.filter (fun e => e.2 ∈ R)).card : ℝ) ≤ (⌊(3/2 : ℝ) ^ m⌋₊ : ℝ) := by
                      rw [hA2card]; exact_mod_cast hcard2
                  _ ≤ _ := hc0le
              · omega
              · have := hlsum2 (kr + lenTo I.len T1 r v) (by have := hT1v.1; omega)
                omega
              · intro w hw
                obtain ⟨hwR, hwY⟩ := hY2 w (Finset.mem_of_mem_erase hw)
                have h1 := hlen2 w hwR
                have h2 := hDA w hwY
                dsimp only
                omega
            obtain ⟨T2, hT2, hF2, hf2⟩ := ih v _ _ _ _ _ (X ∪ verts r T1) _ compat2
            refine ⟨v, (Y.erase r).filter (fun w => w ∉ R), lenTo I.len A r v,
              cost I.c (A.filter (fun e => e.2 ∉ R)), lenSum I.len kr r (A.filter (fun e => e.2 ∉ R)),
              T1, T2, Finset.filter_subset _ _, hd1L, ?_, by omega, by omega, hT1, hT2, ?_⟩
            · rintro ⟨w, hw, hlt⟩
              simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton,
                not_or, not_and, not_not] at hw
              have hwR := hw.2.1 hw.1
              have h1 := hlen2 w hwR
              have h2 := hDA w hw.1
              omega
            · -- submodularity
              have hmR : ∀ S T : Finset (Fin n), S ⊆ T → (I.f S : ℝ) ≤ I.f T := by
                intro S T h; exact_mod_cast hmono S T h
              have hVA : verts r A ⊆ verts r (A.filter (fun e => e.2 ∉ R)) ∪ verts v (A.filter (fun e => e.2 ∈ R)) := by
                intro w hw
                by_cases hwR : w ∈ R
                · exact Finset.mem_union_right _ (k_reach_mem _ v w (hreach2 w (hArbo.2.2 w hw) hwR))
                · exact Finset.mem_union_left _ (k_reach_mem _ r w (hreach1 w (hArbo.2.2 w hw) hwR))
              have hVT : verts r T1 ∪ verts v T2 ⊆ verts r (T1 ∪ T2) := k_vU r v T1 T2 hT1v.2
              unfold fX at hf1 hf2 ⊢
              set V1 := verts r (A.filter (fun e => e.2 ∉ R))
              set V2 := verts v (A.filter (fun e => e.2 ∈ R))
              set W1 := verts r T1
              set W2 := verts v T2
              have e1 := hmR (verts r A ∪ X) ((V1 ∪ X) ∪ (V2 ∪ (X ∪ W1))) (by
                intro w hw
                rcases Finset.mem_union.1 hw with h | h
                · rcases Finset.mem_union.1 (hVA h) with h' | h'
                  · simp [h']
                  · simp [h']
                · simp [h])
              have e2 := hsub (V1 ∪ X) (V2 ∪ (X ∪ W1))
              have e2' := hmR X ((V1 ∪ X) ∩ (V2 ∪ (X ∪ W1))) (by
                intro w hw; simp [hw])
              have e3 := hmR (X ∪ W1) (W2 ∪ (X ∪ W1)) Finset.subset_union_right
              have e3' := hmR X (X ∪ W1) Finset.subset_union_left
              have e4 := hmR (W2 ∪ (X ∪ W1)) (verts r (T1 ∪ T2) ∪ X) (by
                intro w hw
                rcases Finset.mem_union.1 hw with h | h
                · exact Finset.mem_union_left _ (hVT (Finset.mem_union_right _ h))
                · rcases Finset.mem_union.1 h with h' | h'
                  · exact Finset.mem_union_right _ h'
                  · exact Finset.mem_union_left _ (hVT (Finset.mem_union_left _ h')))
              have e5 : W1 ∪ X = X ∪ W1 := Finset.union_comm _ _
              rw [e5] at hf1
              simp only at e2
              have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
              have e6 := mul_nonneg hm0 (sub_nonneg.2 e4)
              push_cast
              linarith
          have main : ∀ m, 1 ≤ m → ∀ (r : Fin n) (kr : ℕ) (Y : Finset (Fin n)) (D : Fin n → ℕ) (B L : ℕ)
              (X : Finset (Fin n)) (A : Edges n),
              CompatibleDC I r kr Y D B L ((3 / 2 : ℝ) ^ m) A →
              ∃ T, (rgdc I 1 .enum m r kr Y D B L X).1 = some T ∧
                FeasibleDC I r kr Y D B L T ∧ fX I.f X r A ≤ (m : ℝ) * fX I.f X r T := by
            intro m hm
            induction m, hm using Nat.le_induction with
            | base => exact base
            | succ m hm ih =>
              intro r kr Y D B L X A hA
              have hcap : ¬ capImp 1 (m + 1) < ((Y.erase r).card : ℝ) := by
                rw [capImp, one_mul, not_lt]
                obtain ⟨⟨hArbo, hYA, hcardA, -⟩, -, -⟩ := hA
                have h1 := Finset.card_le_card (Finset.erase_subset_erase r hYA)
                have h2 := arbo_card A r hArbo
                have : ((Y.erase r).card : ℝ) ≤ A.card := by exact_mod_cast h1.trans h2
                linarith
              have hm0 : m ≠ 0 := by omega
              simp only [rgdc, hcap, hm0, if_false]
              have hcbeq : ∀ init cands, chooseBest I.f X r init cands = List.foldl (fun (p : Option (Edges n) × ℕ) T =>
                ((match p.1 with
                  | none => some T
                  | some old => if fX I.f X r old < fX I.f X r T then some T else p.1), p.2 + 1)) (init, 0) cands := by
                intro init cands; rfl
              rw [hcbeq]
              generalize hcands : List.map Prod.fst (expand I Mode.enum (rgdc I 1 Mode.enum m) 1 r kr (Y.erase r) D X B L true).1 = cands
              -- soundness: every candidate is feasible
              have hS : ∀ T ∈ cands, FeasibleDC I r kr Y D B L T := by
                intro T hT
                rw [← hcands, candMem] at hT
                obtain ⟨v, S, d1, b, l, T1, T2, hS, hd1, hskip, hb, hl, hT1, hT2, rfl⟩ := hT
                exact combine r kr Y D B L v S d1 b l T1 T2 hS hskip hb hl (sound m hm _ _ _ _ _ _ _ _ hT1)
                  (sound m hm _ _ _ _ _ _ _ _ hT2)
              -- completeness: some candidate is an (m+1)-approximation of A
              have hC : ∃ T ∈ cands, fX I.f X r A ≤ ((m + 1 : ℕ) : ℝ) * fX I.f X r T := by
                -- separator `v` of `A`, responsibilities `S`, guessed length `d1` and budgets `b, l`;
                -- the two recursive calls approximate the two halves of `A` (induction hypothesis `ih`)
                have key : ∃ v S d1 b l T1 T2, S ⊆ Y.erase r ∧ d1 ≤ L ∧
                    ¬ (∃ w ∈ Y.erase r \ (S ∪ {v}), D w < d1) ∧ b ≤ B ∧ l ≤ L ∧
                    (rgdc I 1 .enum m r kr ((S ∪ {v}) \ {r})
                      (fun w => if w = v then (if v ∈ Y.erase r then min d1 (D v) else d1) else D w) b l X).1
                      = some T1 ∧
                    (rgdc I 1 .enum m v (kr + lenTo I.len T1 r v) (Y.erase r \ (S ∪ {v})) (fun w => D w - d1)
                      (B - b) (L - l) (X ∪ verts r T1)).1 = some T2 ∧
                    fX I.f X r A ≤ ((m + 1 : ℕ) : ℝ) * fX I.f X r (T1 ∪ T2) :=
                  keystep m hm ih r kr Y D B L X A hA
                obtain ⟨v, S, d1, b, l, T1, T2, hS', hd1, hskip, hb, hl, hT1, hT2, hle⟩ := key
                refine ⟨T1 ∪ T2, ?_, hle⟩
                rw [← hcands, candMem]
                exact ⟨v, S, d1, b, l, T1, T2, hS', hd1, hskip, hb, hl, hT1, hT2, rfl⟩
              obtain ⟨T0, hT0, hle⟩ := hC
              obtain ⟨h1, h2, -⟩ := cb X r cands (if Y.erase r = ∅ then some ∅ else none) 0
              obtain ⟨T', e, le⟩ := h2 T0 hT0
              refine ⟨T', e, ?_, hle.trans (mul_le_mul_of_nonneg_left le (by positivity))⟩
              rcases h1 T' e with h | h
              · by_cases hY0 : Y.erase r = ∅
                · rw [if_pos hY0] at h; cases h
                  apply fs0
                  intro w hw
                  by_cases hwr : w = r
                  · simp [hwr]
                  · have : w ∈ Y.erase r := Finset.mem_erase.2 ⟨hwr, hw⟩
                    rw [hY0] at this; simp at this
                · rw [if_neg hY0] at h; cases h
              · exact hS T' h
          exact main i hi r kr Y D B L X A hA
