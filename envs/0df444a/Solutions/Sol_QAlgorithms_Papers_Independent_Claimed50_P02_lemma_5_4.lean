-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P02.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:35:11.537591+00:00
-- url     : https://prove2.me/submissions/50a4cb69-bde0-4fe3-b380-787b3b2733d1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P02
open QAlgorithms.Papers.Independent.Claimed50.P02

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P69 (Sites choi)

noncomputable section

lemma g58a_mem (s : YoungDiagram) (c : ℕ × ℕ) : c ∈ s.cells ↔ c ∈ s := Iff.rfl

lemma g58a_row_lt (s : YoungDiagram) (c : ℕ × ℕ) (hc : c ∈ s.cells) : c.1 < shapeRows s := by
  have : (c.1, 0) ∈ s := s.up_left_mem le_rfl (Nat.zero_le _) (show (c.1, c.2) ∈ s from hc)
  exact YoungDiagram.mem_iff_lt_colLen.mp this

lemma g58a_add_aux (s t' : YoungDiagram) (a a' : ℕ × ℕ) (ha : a ∉ s.cells)
    (ht' : t'.cells = insert a' s.cells) (h1 : a.1 ≤ a'.1)
    (hc : (a.2 : ℤ) - a.1 = (a'.2 : ℤ) - a'.1) : a = a' := by
  have h2 : a.2 ≤ a'.2 := by omega
  have hm : (a'.1, a'.2) ∈ t' := by
    show a' ∈ t'.cells
    rw [ht']; exact Finset.mem_insert_self _ _
  have := t'.up_left_mem h1 h2 hm
  change (a.1, a.2) ∈ t'.cells at this
  rw [ht'] at this
  rcases Finset.mem_insert.mp this with h | h
  · exact h
  · exact absurd h ha

lemma g58a_add_unique (s t t' : YoungDiagram) (a a' : ℕ × ℕ) (ha : a ∉ s.cells)
    (ha' : a' ∉ s.cells) (ht : t.cells = insert a s.cells) (ht' : t'.cells = insert a' s.cells)
    (hc : (a.2 : ℤ) - a.1 = (a'.2 : ℤ) - a'.1) : a = a' := by
  rcases le_total a.1 a'.1 with h | h
  · exact g58a_add_aux s t' a a' ha ht' h hc
  · exact (g58a_add_aux s t a' a ha' ht h hc.symm).symm

lemma g58a_rem_aux (s t : YoungDiagram) (c c' : ℕ × ℕ) (hc : c ∉ t.cells)
    (hs : s.cells = insert c t.cells) (hs' : c' ∈ s.cells) (h1 : c.1 ≤ c'.1)
    (he : (c.2 : ℤ) - c.1 = (c'.2 : ℤ) - c'.1) : c = c' := by
  by_contra hne
  have h2 : c.2 ≤ c'.2 := by omega
  rw [hs] at hs'
  rcases Finset.mem_insert.mp hs' with h | h
  · exact hne h.symm
  · have := t.up_left_mem h1 h2 (show (c'.1, c'.2) ∈ t from h)
    exact hc this

lemma g58a_rem_unique (s t t' : YoungDiagram) (c c' : ℕ × ℕ) (hc : c ∉ t.cells)
    (hc' : c' ∉ t'.cells) (hs : s.cells = insert c t.cells) (hs' : s.cells = insert c' t'.cells)
    (he : (c.2 : ℤ) - c.1 = (c'.2 : ℤ) - c'.1) : t = t' := by
  have : c = c' := by
    rcases le_total c.1 c'.1 with h | h
    · exact g58a_rem_aux s t c c' hc hs (by rw [hs']; exact Finset.mem_insert_self _ _) h he
    · exact (g58a_rem_aux s t' c' c hc' hs' (by rw [hs]; exact Finset.mem_insert_self _ _) h
        he.symm).symm
  subst this
  apply YoungDiagram.ext
  have e1 : t.cells = s.cells.erase c := by rw [hs, Finset.erase_insert hc]
  have e2 : t'.cells = s.cells.erase c := by rw [hs', Finset.erase_insert hc']
  rw [e1, e2]

lemma g58a_content_insert (s t : YoungDiagram) (a : ℕ × ℕ) (ha : a ∉ s.cells)
    (ht : t.cells = insert a s.cells) :
    shapeContent t = shapeContent s + ((a.2 : ℤ) - a.1) ∧
      (t.cells.card : ℤ) = s.cells.card + 1 := by
  unfold shapeContent
  rw [ht, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
  constructor
  · ring
  · push_cast; ring

/-- content of an edge from v to b -/
def g58a_ec (d : ℕ) (v b : Bipartition) : ℤ :=
  shapeContent b.1 - shapeContent v.1 + shapeContent b.2 - shapeContent v.2 +
    (d : ℤ) * ((b.2.cells.card : ℤ) - (v.2.cells.card : ℤ))

lemma g58a_step_left (d : ℕ) (v b b' : Bipartition)
    (hb : AddsCell v.1 b.1 ∧ v.2 = b.2) (hb' : AddsCell v.1 b'.1 ∧ v.2 = b'.2)
    (hc : g58a_ec d v b = g58a_ec d v b') : b = b' := by
  obtain ⟨⟨a, ha, hta⟩, h2⟩ := hb
  obtain ⟨⟨a', ha', hta'⟩, h2'⟩ := hb'
  obtain ⟨e1, -⟩ := g58a_content_insert _ _ a ha hta
  obtain ⟨e1', -⟩ := g58a_content_insert _ _ a' ha' hta'
  unfold g58a_ec at hc
  rw [← h2, ← h2', e1, e1'] at hc
  have : a = a' := g58a_add_unique v.1 b.1 b'.1 a a' ha ha' hta hta' (by linarith)
  subst this
  have : b.1 = b'.1 := YoungDiagram.ext (by rw [hta, hta'])
  exact Prod.ext this (h2.symm.trans h2')

lemma g58a_step_dual (d : ℕ) (v b b' : Bipartition)
    (hb : (AddsCell b.1 v.1 ∧ v.2 = b.2) ∨ (v.1 = b.1 ∧ AddsCell v.2 b.2))
    (hb' : (AddsCell b'.1 v.1 ∧ v.2 = b'.2) ∨ (v.1 = b'.1 ∧ AddsCell v.2 b'.2))
    (adm : shapeRows b.1 + shapeRows b.2 ≤ d) (adm' : shapeRows b'.1 + shapeRows b'.2 ≤ d)
    (hc : g58a_ec d v b = g58a_ec d v b') : b = b' := by
  unfold g58a_ec at hc
  rcases hb with ⟨⟨c, hcn, hvc⟩, h2⟩ | ⟨h1, ⟨e, hen, hbe⟩⟩ <;>
    rcases hb' with ⟨⟨c', hcn', hvc'⟩, h2'⟩ | ⟨h1', ⟨e', hen', hbe'⟩⟩
  · obtain ⟨E, -⟩ := g58a_content_insert _ _ c hcn hvc
    obtain ⟨E', -⟩ := g58a_content_insert _ _ c' hcn' hvc'
    rw [← h2, ← h2'] at hc
    have : b.1 = b'.1 := g58a_rem_unique v.1 b.1 b'.1 c c' hcn hcn' hvc hvc' (by linarith)
    exact Prod.ext this (h2.symm.trans h2')
  · -- remove left in b, add right in b'
    exfalso
    obtain ⟨E, -⟩ := g58a_content_insert _ _ c hcn hvc
    obtain ⟨E', C'⟩ := g58a_content_insert _ _ e' hen' hbe'
    rw [← h2, ← h1', E, E', C'] at hc
    have r1 : c.1 < shapeRows v.1 := g58a_row_lt _ c (by rw [hvc]; exact Finset.mem_insert_self _ _)
    have r2 : e'.1 < shapeRows b'.2 := g58a_row_lt _ e' (by rw [hbe']; exact Finset.mem_insert_self _ _)
    rw [← h1'] at adm'
    have : (shapeRows v.1 : ℤ) + shapeRows b'.2 ≤ d := by exact_mod_cast adm'
    have : (c.1 : ℤ) < shapeRows v.1 := by exact_mod_cast r1
    have : (e'.1 : ℤ) < shapeRows b'.2 := by exact_mod_cast r2
    have : (0 : ℤ) ≤ c.2 := by positivity
    have : (0 : ℤ) ≤ e'.2 := by positivity
    nlinarith
  · exfalso
    obtain ⟨E, -⟩ := g58a_content_insert _ _ c' hcn' hvc'
    obtain ⟨E', C'⟩ := g58a_content_insert _ _ e hen hbe
    rw [← h2', ← h1, E, E', C'] at hc
    have r1 : c'.1 < shapeRows v.1 := g58a_row_lt _ c' (by rw [hvc']; exact Finset.mem_insert_self _ _)
    have r2 : e.1 < shapeRows b.2 := g58a_row_lt _ e (by rw [hbe]; exact Finset.mem_insert_self _ _)
    rw [← h1] at adm
    have : (shapeRows v.1 : ℤ) + shapeRows b.2 ≤ d := by exact_mod_cast adm
    have : (c'.1 : ℤ) < shapeRows v.1 := by exact_mod_cast r1
    have : (e.1 : ℤ) < shapeRows b.2 := by exact_mod_cast r2
    have : (0 : ℤ) ≤ c'.2 := by positivity
    have : (0 : ℤ) ≤ e.2 := by positivity
    nlinarith
  · obtain ⟨E, C⟩ := g58a_content_insert _ _ e hen hbe
    obtain ⟨E', C'⟩ := g58a_content_insert _ _ e' hen' hbe'
    rw [← h1, ← h1', E, E', C, C'] at hc
    have : e = e' := g58a_add_unique v.2 b.2 b'.2 e e' hen hen' hbe hbe' (by linarith)
    subst this
    have : b.2 = b'.2 := YoungDiagram.ext (by rw [hbe, hbe'])
    exact Prod.ext (h1.symm.trans h1') this

theorem solution {d p q : ℕ} (hd : 2 ≤ d) (S T : PhysicalPath d p q) :
    S = T ↔ pathContent S = pathContent T := by
  constructor
  · rintro rfl; rfl
  · intro h
    have key : ∀ m (hm : m < p + q + 1), S.vertex ⟨m, hm⟩ = T.vertex ⟨m, hm⟩ := by
      intro m
      induction m with
      | zero =>
        intro hm
        have e0 : (⟨0, hm⟩ : Fin (p+q+1)) = 0 := rfl
        rw [e0]
        apply Prod.ext
        · exact YoungDiagram.ext (by rw [S.rootLeft, T.rootLeft])
        · exact YoungDiagram.ext (by rw [S.rootRight, T.rootRight])
      | succ m ih =>
        intro hm
        set k : Fin (p+q) := ⟨m, by omega⟩ with hk
        have ec : (⟨m, by omega⟩ : Fin (p+q+1)) = Fin.castSucc k := rfl
        have es : (⟨m+1, hm⟩ : Fin (p+q+1)) = Fin.succ k := rfl
        have hv := ih (by omega)
        rw [ec] at hv
        rw [es]
        have hck : g58a_ec d (S.vertex (Fin.castSucc k)) (S.vertex (Fin.succ k)) =
            g58a_ec d (T.vertex (Fin.castSucc k)) (T.vertex (Fin.succ k)) := by
          have := congrFun h k
          simp only [pathContent] at this
          unfold g58a_ec; linarith
        rw [hv] at hck
        have eS := S.edge k
        have eT := T.edge k
        simp only at eS eT
        rw [hv] at eS
        by_cases hkp : k.val < p
        · rw [if_pos hkp] at eS eT
          exact g58a_step_left d _ _ _ eS eT hck
        · rw [if_neg hkp] at eS eT
          exact g58a_step_dual d _ _ _ eS eT (S.admissible _) (T.admissible _) hck
    cases S with
    | mk vS rLS rRS aS eS =>
    cases T with
    | mk vT rLT rRT aT eT =>
    have : vS = vT := funext fun x => key x.val x.isLt
    subst this
    rfl

end
