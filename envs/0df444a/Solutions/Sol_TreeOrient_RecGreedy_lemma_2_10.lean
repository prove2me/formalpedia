-- Prove2me | solution 1 for TreeOrient.RecGreedy.lemma_2_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T05:48:49.273207+00:00
-- url     : https://prove2.me/submissions/58478ceb-1de9-4e70-ac8a-cb88a36fd439

import Mathlib
import Definitions.Def_TreeOrient_RecGreedy_Model

namespace TreeOrient.RecGreedy

open Relation

section ArboLib
variable {n : ℕ}

theorem TO_reaches_mono {T T' : Edges n} (h : T ⊆ T') {a b : Fin n} (hr : Reaches T a b) :
    Reaches T' a b :=
  by
    unfold Reaches at *
    induction hr with
    | refl => exact ReflTransGen.refl
    | tail _ hbc ih => exact ih.tail (h hbc)

theorem TO_reaches_edge {T : Edges n} {a b : Fin n} (h : (a, b) ∈ T) : Reaches T a b :=
  ReflTransGen.single h

theorem TO_reaches_trans {T : Edges n} {a b c : Fin n} (h1 : Reaches T a b)
    (h2 : Reaches T b c) : Reaches T a c :=
  ReflTransGen.trans h1 h2

theorem TO_reaches_refl {T : Edges n} {a : Fin n} : Reaches T a a := ReflTransGen.refl

theorem TO_mem_verts {r : Fin n} {T : Edges n} {w : Fin n} :
    w ∈ verts r T ↔ w = r ∨ ∃ e ∈ T, e.1 = w ∨ e.2 = w := by
  unfold verts
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨e, he, h⟩ | ⟨e, he, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e, he, Or.inl h⟩
    · exact Or.inr ⟨e, he, Or.inr h⟩
  · rintro (h | ⟨e, he, h | h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨e, he, h⟩)
    · exact Or.inr (Or.inr ⟨e, he, h⟩)

theorem TO_root_mem_verts (r : Fin n) (T : Edges n) : r ∈ verts r T :=
  TO_mem_verts.2 (Or.inl rfl)

theorem TO_fst_mem_verts {r : Fin n} {T : Edges n} {e : Fin n × Fin n} (he : e ∈ T) :
    e.1 ∈ verts r T :=
  TO_mem_verts.2 (Or.inr ⟨e, he, Or.inl rfl⟩)

theorem TO_snd_mem_verts {r : Fin n} {T : Edges n} {e : Fin n × Fin n} (he : e ∈ T) :
    e.2 ∈ verts r T :=
  TO_mem_verts.2 (Or.inr ⟨e, he, Or.inr rfl⟩)

theorem TO_verts_mono {r : Fin n} {T T' : Edges n} (h : T ⊆ T') : verts r T ⊆ verts r T' := by
  intro w hw
  rcases TO_mem_verts.1 hw with h1 | ⟨e, he, h2⟩
  · exact TO_mem_verts.2 (Or.inl h1)
  · exact TO_mem_verts.2 (Or.inr ⟨e, h he, h2⟩)

theorem TO_in_unique {r : Fin n} {A : Edges n} (hA : IsArbo r A) {p q x : Fin n}
    (h1 : (p, x) ∈ A) (h2 : (q, x) ∈ A) : p = q := by
  have := hA.2.1 _ h1 _ h2 rfl
  simpa using congrArg Prod.fst this

/-- Two ancestors of the same vertex are comparable. -/
theorem TO_chain {r : Fin n} {A : Edges n} (hA : IsArbo r A) {a b x : Fin n}
    (ha : Reaches A a x) (hb : Reaches A b x) : Reaches A a b ∨ Reaches A b a := by
  induction ha generalizing b with
  | refl => exact Or.inr hb
  | @tail y z hay hyz ih =>
    rcases ReflTransGen.cases_tail hb with h | ⟨y', hby', hy'z⟩
    · subst h; exact Or.inl (hay.tail hyz)
    · have : y' = y := TO_in_unique hA hy'z hyz
      subst this
      exact ih hby'

theorem TO_no_cycle {r : Fin n} {A : Edges n} (hA : IsArbo r A) {x : Fin n}
    (hx : Reaches A r x) : ¬ TransGen (fun a b => (a, b) ∈ A) x x := by
  induction hx with
  | refl =>
    intro h
    obtain ⟨p, -, hp⟩ := TransGen.tail'_iff.1 h
    exact hA.1 _ hp rfl
  | @tail q x hrq hqx ih =>
    intro h
    obtain ⟨p, hxp, hp⟩ := TransGen.tail'_iff.1 h
    have : p = q := TO_in_unique hA hp hqx
    subst this
    exact ih (TransGen.head' hqx hxp)

theorem TO_antisymm {r : Fin n} {A : Edges n} (hA : IsArbo r A) {a b : Fin n}
    (hra : Reaches A r a) (hab : Reaches A a b) (hba : Reaches A b a) : a = b := by
  by_contra hne
  rcases reflTransGen_iff_eq_or_transGen.1 hab with h | h
  · exact hne h.symm
  rcases reflTransGen_iff_eq_or_transGen.1 hba with h' | h'
  · exact hne h'
  exact TO_no_cycle hA hra (h.trans h')

theorem TO_reach_of_verts {r : Fin n} {A : Edges n} (hA : IsArbo r A) {w : Fin n}
    (hw : w ∈ verts r A) : Reaches A r w := hA.2.2 w hw

theorem TO_no_self {r : Fin n} {A : Edges n} (hA : IsArbo r A) {v : Fin n} :
    (v, v) ∉ A := by
  intro h
  exact TO_no_cycle hA (TO_reach_of_verts hA (TO_fst_mem_verts (r := r) h)) (TransGen.single h)

/-- Edges hanging below `w`. -/
noncomputable def TOsub (A : Edges n) (w : Fin n) : Edges n := by
  classical exact A.filter (fun e => Reaches A w e.1)

theorem TO_mem_sub {A : Edges n} {w : Fin n} {e : Fin n × Fin n} :
    e ∈ TOsub A w ↔ e ∈ A ∧ Reaches A w e.1 := by
  classical
  unfold TOsub
  simp [Finset.mem_filter]

theorem TO_sub_subset (A : Edges n) (w : Fin n) : TOsub A w ⊆ A := by
  intro e he; exact (TO_mem_sub.1 he).1

theorem TO_sub_root {r : Fin n} {A : Edges n} (hA : IsArbo r A) : TOsub A r = A := by
  apply Finset.Subset.antisymm (TO_sub_subset A r)
  intro e he
  exact TO_mem_sub.2 ⟨he, TO_reach_of_verts hA (TO_fst_mem_verts he)⟩

/-- Branch at child edge `e`: the edge itself and everything below its head. -/
noncomputable def TObranch (A : Edges n) (e : Fin n × Fin n) : Edges n :=
  insert e (TOsub A e.2)

noncomputable def TOch (A : Edges n) (v : Fin n) : Edges n := by
  classical exact A.filter (fun e => e.1 = v)

theorem TO_mem_ch {A : Edges n} {v : Fin n} {e : Fin n × Fin n} :
    e ∈ TOch A v ↔ e ∈ A ∧ e.1 = v := by
  classical
  unfold TOch
  simp [Finset.mem_filter]

theorem TO_branch_reach {A : Edges n} {e f : Fin n × Fin n} (he : e ∈ A)
    (hf : f ∈ TObranch A e) : f ∈ A ∧ Reaches A e.2 f.2 := by
  unfold TObranch at hf
  rcases Finset.mem_insert.1 hf with h | h
  · subst h; exact ⟨he, TO_reaches_refl⟩
  · have := TO_mem_sub.1 h
    exact ⟨this.1, this.2.tail this.1⟩

theorem TO_sub_decomp {A : Edges n} (v : Fin n) :
    TOsub A v = (TOch A v).biUnion (TObranch A) := by
  ext f
  simp only [Finset.mem_biUnion]
  constructor
  · intro hf
    obtain ⟨hfA, hvf⟩ := TO_mem_sub.1 hf
    rcases ReflTransGen.cases_head hvf with h | ⟨c, hvc, hcf⟩
    · refine ⟨f, TO_mem_ch.2 ⟨hfA, h.symm⟩, ?_⟩
      unfold TObranch; exact Finset.mem_insert_self _ _
    · refine ⟨(v, c), TO_mem_ch.2 ⟨hvc, rfl⟩, ?_⟩
      unfold TObranch
      exact Finset.mem_insert_of_mem (TO_mem_sub.2 ⟨hfA, hcf⟩)
  · rintro ⟨e, he, hf⟩
    obtain ⟨heA, hev⟩ := TO_mem_ch.1 he
    unfold TObranch at hf
    rcases Finset.mem_insert.1 hf with h | h
    · subst h; exact TO_mem_sub.2 ⟨heA, by rw [hev]; exact ReflTransGen.refl⟩
    · obtain ⟨hfA, hrf⟩ := TO_mem_sub.1 h
      refine TO_mem_sub.2 ⟨hfA, ?_⟩
      have : Reaches A v e.2 := by
        have := TO_reaches_edge (T := A) (a := e.1) (b := e.2) heA
        rw [hev] at this; exact this
      exact this.trans hrf

theorem TO_branch_disj {r : Fin n} {A : Edges n} (hA : IsArbo r A) {v : Fin n}
    {e e' : Fin n × Fin n} (he : e ∈ TOch A v) (he' : e' ∈ TOch A v) (hne : e ≠ e') :
    Disjoint (TObranch A e) (TObranch A e') := by
  rw [Finset.disjoint_left]
  intro f hf hf'
  obtain ⟨heA, hev⟩ := TO_mem_ch.1 he
  obtain ⟨heA', hev'⟩ := TO_mem_ch.1 he'
  obtain ⟨hfA, h1⟩ := TO_branch_reach heA hf
  obtain ⟨-, h2⟩ := TO_branch_reach heA' hf'
  have hc : e.2 ≠ e'.2 := by
    intro h; apply hne; exact Prod.ext (hev.trans hev'.symm) h
  -- generic: if Reaches c c' with c ≠ c', both children of v, contradiction
  have key : ∀ x y : Fin n × Fin n, x ∈ A → y ∈ A → x.1 = v → y.1 = v → x.2 ≠ y.2 →
      Reaches A x.2 y.2 → False := by
    intro x y hx hy hxv hyv hxy hreach
    rcases ReflTransGen.cases_tail hreach with h | ⟨p, hxp, hpy⟩
    · exact hxy h.symm
    · have hy' : (y.1, y.2) ∈ A := hy
      have hp : p = y.1 := TO_in_unique hA hpy hy'
      rw [hp, hyv] at hxp
      -- Reaches x.2 v and edge v → x.2 : cycle
      have hxA : (v, x.2) ∈ A := by rw [← hxv]; exact hx
      have hrv : Reaches A r v := TO_reach_of_verts hA (TO_fst_mem_verts (r := r) hxA)
      exact TO_no_cycle hA hrv (TransGen.head' hxA hxp)
  rcases TO_chain hA h1 h2 with h | h
  · exact key e e' heA heA' hev hev' hc h
  · exact key e' e heA' heA hev' hev (Ne.symm hc) h

theorem TO_branch_card {r : Fin n} {A : Edges n} (hA : IsArbo r A) {e : Fin n × Fin n}
    (he : e ∈ A) : (TObranch A e).card = 1 + (TOsub A e.2).card := by
  unfold TObranch
  rw [Finset.card_insert_of_notMem, add_comm]
  intro h
  obtain ⟨-, h2⟩ := TO_mem_sub.1 h
  have hrv : Reaches A r e.1 := TO_reach_of_verts hA (TO_fst_mem_verts he)
  exact TO_no_cycle hA hrv (TransGen.head' (show (e.1, e.2) ∈ A from he) h2)

theorem TO_sub_card {r : Fin n} {A : Edges n} (hA : IsArbo r A) (v : Fin n) (G : Edges n)
    (hG : G ⊆ TOch A v) :
    (G.biUnion (TObranch A)).card = ∑ e ∈ G, (1 + (TOsub A e.2).card) := by
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro e he
    exact TO_branch_card hA (TO_mem_ch.1 (hG he)).1
  · intro e he e' he' hne
    exact TO_branch_disj hA (hG he) (hG he') hne

theorem TO_child_sub_lt {r : Fin n} {A : Edges n} (hA : IsArbo r A) {v : Fin n}
    {e : Fin n × Fin n} (he : e ∈ TOch A v) :
    (TOsub A e.2).card < (TOsub A v).card := by
  obtain ⟨heA, hev⟩ := TO_mem_ch.1 he
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨e, TO_mem_sub.2 ⟨heA, by rw [hev]; exact ReflTransGen.refl⟩, ?_⟩
    intro h
    obtain ⟨-, h2⟩ := TO_mem_sub.1 h
    have hrv : Reaches A r e.1 := TO_reach_of_verts hA (TO_fst_mem_verts heA)
    exact TO_no_cycle hA hrv (TransGen.head' (show (e.1, e.2) ∈ A from heA) h2)
  · intro f hf
    obtain ⟨hfA, h⟩ := TO_mem_sub.1 hf
    refine TO_mem_sub.2 ⟨hfA, ?_⟩
    have : Reaches A v e.2 := by
      have := TO_reaches_edge (T := A) (a := e.1) (b := e.2) heA
      rw [hev] at this; exact this
    exact this.trans h

/-- Weighted subset selection used by the separator. -/
theorem TO_subset_select {α : Type} [DecidableEq α] (C : Finset α) (w : α → ℕ) (m : ℕ)
    (hm : 2 ≤ m) (hpos : ∀ e ∈ C, 1 ≤ w e) (hsmall : ∀ e ∈ C, 3 * w e ≤ m + 2)
    (htot : m ≤ 3 * ∑ e ∈ C, w e) :
    ∃ G ⊆ C, m ≤ 3 * ∑ e ∈ G, w e ∧ 3 * ∑ e ∈ G, w e ≤ 2 * m := by
  by_cases hbig : ∃ e ∈ C, m ≤ 3 * w e
  · obtain ⟨e, he, hme⟩ := hbig
    refine ⟨{e}, by simpa using he, ?_, ?_⟩
    · simpa using hme
    · have := hsmall e he; simp; omega
  · push Not at hbig
    let F := C.powerset.filter (fun G => m ≤ 3 * ∑ e ∈ G, w e)
    have hF : F.Nonempty := ⟨C, Finset.mem_filter.2 ⟨Finset.mem_powerset_self C, htot⟩⟩
    obtain ⟨G, hGF, hmin⟩ := Finset.exists_min_image F (fun G => ∑ e ∈ G, w e) hF
    obtain ⟨hGC, hGm⟩ := Finset.mem_filter.1 hGF
    have hGC' : G ⊆ C := Finset.mem_powerset.1 hGC
    refine ⟨G, hGC', hGm, ?_⟩
    have hGne : G.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl; simp at hGm; omega
    obtain ⟨e, he⟩ := hGne
    have hsplit := Finset.sum_erase_add G w he
    have hnot : ¬ m ≤ 3 * ∑ x ∈ G.erase e, w x := by
      intro h
      have := hmin (G.erase e) (Finset.mem_filter.2
        ⟨Finset.mem_powerset.2 ((Finset.erase_subset e G).trans hGC'), h⟩)
      have := hpos e (hGC' he)
      omega
    have := hbig e (hGC' he)
    omega

end ArboLib


section Fact22
variable {n : ℕ}

theorem TO_reach_in_sub {A : Edges n} {a b : Fin n} (h : Reaches A a b) :
    Reaches (TOsub A a) a b := by
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail y z hay hyz ih => exact ih.tail (TO_mem_sub.2 ⟨hyz, hay⟩)

theorem TO_split {r : Fin n} {A : Edges n} (hA : IsArbo r A) {v : Fin n}
    (hv : v ∈ verts r A) (G : Edges n) (hG : G ⊆ TOch A v) :
    IsArbo r (A \ G.biUnion (TObranch A)) ∧ v ∈ verts r (A \ G.biUnion (TObranch A)) ∧
      IsArbo v (G.biUnion (TObranch A)) := by
  set A2 := G.biUnion (TObranch A) with hA2
  have hrv : Reaches A r v := TO_reach_of_verts hA hv
  -- facts on A2
  have mem2 : ∀ f, f ∈ A2 → ∃ c ∈ G, c ∈ A ∧ c.1 = v ∧ f ∈ A ∧ Reaches A c.2 f.2 := by
    intro f hf
    obtain ⟨c, hc, hfc⟩ := Finset.mem_biUnion.1 hf
    obtain ⟨hcA, hcv⟩ := TO_mem_ch.1 (hG hc)
    obtain ⟨hfA, hr⟩ := TO_branch_reach hcA hfc
    exact ⟨c, hc, hcA, hcv, hfA, hr⟩
  have nobelow : ∀ c ∈ G, ¬ Reaches A c.2 v := by
    intro c hc h
    obtain ⟨hcA, hcv⟩ := TO_mem_ch.1 (hG hc)
    have hcA' : (v, c.2) ∈ A := by rw [← hcv]; exact hcA
    exact TO_no_cycle hA hrv (TransGen.head' hcA' h)
  have hA2sub : A2 ⊆ A := fun f hf => by obtain ⟨_, _, _, _, h, _⟩ := mem2 f hf; exact h
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_⟩⟩
  · intro e he; exact hA.1 e (Finset.mem_sdiff.1 he).1
  · intro e he e' he' h; exact hA.2.1 e (Finset.mem_sdiff.1 he).1 e' (Finset.mem_sdiff.1 he').1 h
  · -- reachability in A1
    have Q : ∀ x, Reaches A r x → (∀ c ∈ G, ¬ Reaches A c.2 x) →
        Reaches (A \ A2) r x := by
      intro x hx
      induction hx with
      | refl => intro _; exact ReflTransGen.refl
      | @tail p x hrp hpx ih =>
        intro hno
        have hp : ∀ c ∈ G, ¬ Reaches A c.2 p := fun c hc h => hno c hc (h.tail hpx)
        refine (ih hp).tail ?_
        refine Finset.mem_sdiff.2 ⟨hpx, ?_⟩
        intro h2
        obtain ⟨c, hc, -, -, -, hr⟩ := mem2 _ h2
        exact hno c hc hr
    have Q1 : ∀ e ∈ A \ A2, Reaches (A \ A2) r e.1 := by
      intro e he
      obtain ⟨heA, he2⟩ := Finset.mem_sdiff.1 he
      apply Q _ (TO_reach_of_verts hA (TO_fst_mem_verts heA))
      intro c hc h
      apply he2
      exact Finset.mem_biUnion.2 ⟨c, hc, by
        unfold TObranch; exact Finset.mem_insert_of_mem (TO_mem_sub.2 ⟨heA, h⟩)⟩
    intro w hw
    rcases TO_mem_verts.1 hw with h | ⟨e, he, h | h⟩
    · subst h; exact ReflTransGen.refl
    · subst h; exact Q1 e he
    · subst h; exact (Q1 e he).tail (show (e.1, e.2) ∈ A \ A2 from he)
  · -- v ∈ verts r A1
    rcases ReflTransGen.cases_tail hrv with h | ⟨p, -, hpv⟩
    · subst h; exact TO_root_mem_verts _ _
    · have : (p, v) ∈ A \ A2 := by
        refine Finset.mem_sdiff.2 ⟨hpv, ?_⟩
        intro h2
        obtain ⟨c, hc, -, -, -, hr⟩ := mem2 _ h2
        exact nobelow c hc hr
      exact TO_snd_mem_verts this
  · intro e he h
    obtain ⟨c, hc, -, -, -, hr⟩ := mem2 e he
    rw [h] at hr
    exact nobelow c hc hr
  · intro e he e' he' h; exact hA.2.1 e (hA2sub he) e' (hA2sub he') h
  · have R1 : ∀ f ∈ A2, Reaches A2 v f.1 := by
      intro f hf
      obtain ⟨c, hc, hfc⟩ := Finset.mem_biUnion.1 hf
      obtain ⟨hcA, hcv⟩ := TO_mem_ch.1 (hG hc)
      have hcA2 : c ∈ A2 := Finset.mem_biUnion.2 ⟨c, hc, by
        unfold TObranch; exact Finset.mem_insert_self _ _⟩
      unfold TObranch at hfc
      rcases Finset.mem_insert.1 hfc with h | h
      · subst h; rw [hcv]; exact ReflTransGen.refl
      · obtain ⟨-, hcf⟩ := TO_mem_sub.1 h
        have h1 : Reaches A2 v c.2 := by
          have := TO_reaches_edge (T := A2) (a := c.1) (b := c.2) hcA2
          rw [hcv] at this; exact this
        refine h1.trans (TO_reaches_mono ?_ (TO_reach_in_sub hcf))
        intro g hg
        exact Finset.mem_biUnion.2 ⟨c, hc, by unfold TObranch; exact Finset.mem_insert_of_mem hg⟩
    intro w hw
    rcases TO_mem_verts.1 hw with h | ⟨e, he, h | h⟩
    · subst h; exact ReflTransGen.refl
    · subst h; exact R1 e he
    · subst h; exact (R1 e he).tail (show (e.1, e.2) ∈ A2 from he)

theorem TO_fact_2_2 {r : Fin n} (A : Edges n)
    (hA : IsArbo r A) (h2 : 2 ≤ A.card) :
    ∃ v ∈ verts r A, ∃ A₁ A₂ : Edges n,
      Disjoint A₁ A₂ ∧ A₁ ∪ A₂ = A ∧ IsArbo r A₁ ∧ v ∈ verts r A₁ ∧
      IsArbo v A₂ ∧ 3 * A₁.card ≤ 2 * A.card ∧ 3 * A₂.card ≤ 2 * A.card := by
  classical
  set m := A.card with hm
  let F := (verts r A).filter (fun w => m ≤ 3 * (TOsub A w).card)
  have hF : F.Nonempty := ⟨r, Finset.mem_filter.2 ⟨TO_root_mem_verts _ _, by
    rw [TO_sub_root hA]; omega⟩⟩
  obtain ⟨v, hvF, hmin⟩ := Finset.exists_min_image F (fun w => (TOsub A w).card) hF
  obtain ⟨hv, hvm⟩ := Finset.mem_filter.1 hvF
  have hsmall : ∀ e ∈ TOch A v, 3 * (1 + (TOsub A e.2).card) ≤ m + 2 := by
    intro e he
    have hlt := TO_child_sub_lt hA he
    have hmem : e.2 ∈ verts r A := TO_snd_mem_verts (TO_mem_ch.1 he).1
    by_contra hc
    have : e.2 ∈ F := Finset.mem_filter.2 ⟨hmem, by omega⟩
    have := hmin _ this
    omega
  have htot : m ≤ 3 * ∑ e ∈ TOch A v, (1 + (TOsub A e.2).card) := by
    rw [← TO_sub_card hA v _ (Finset.Subset.refl _), ← TO_sub_decomp]; exact hvm
  obtain ⟨G, hGC, hG1, hG2⟩ := TO_subset_select (TOch A v) (fun e => 1 + (TOsub A e.2).card) m
    h2 (fun _ _ => by omega) hsmall htot
  have hcard2 := TO_sub_card hA v G hGC
  obtain ⟨hA1, hvA1, hA2⟩ := TO_split hA hv G hGC
  have hsub : G.biUnion (TObranch A) ⊆ A := by
    intro f hf
    obtain ⟨c, hc, hfc⟩ := Finset.mem_biUnion.1 hf
    exact (TO_branch_reach (TO_mem_ch.1 (hGC hc)).1 hfc).1
  refine ⟨v, hv, A \ G.biUnion (TObranch A), G.biUnion (TObranch A),
    Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hsub, hA1, hvA1, hA2, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hsub, hcard2]
    have := Finset.card_le_card hsub
    rw [hcard2] at this
    omega
  · rw [hcard2]; exact hG2

end Fact22

end TreeOrient.RecGreedy


namespace TreeOrient.RecGreedy

open Relation

section Unfold
variable {n : ℕ}

theorem TO_foldl_gen {α β : Type} (F : β × ℕ → α → β × ℕ) (h : β → α → β) (H : α → ℕ)
    (hF : ∀ b k a, F (b, k) a = (h b a, k + H a)) (l : List α) (b : β) (k : ℕ) :
    l.foldl F (b, k) = (l.foldl h b, k + (l.map H).sum) := by
  induction l generalizing b k with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, List.foldl_cons, hF, ih]
    simp [List.sum_cons]; omega

theorem TO_foldl_app {α γ : Type} (G : α → List γ) (l : List α) (c : List γ) :
    l.foldl (fun acc a => acc ++ G a) c = c ++ l.flatMap G := by
  induction l generalizing c with
  | nil => simp
  | cons a t ih => rw [List.foldl_cons, ih]; simp

/-- The incumbent update of `chooseBest`. -/
noncomputable def TOcb (f : Finset (Fin n) → ℕ) (X : Finset (Fin n)) (r : Fin n)
    (o : Option (Edges n)) (T : Edges n) : Option (Edges n) :=
  match o with
  | none => some T
  | some old => if fX f X r old < fX f X r T then some T else o

theorem TO_chooseBest_eq (f : Finset (Fin n) → ℕ) (X : Finset (Fin n)) (r : Fin n)
    (o : Option (Edges n)) (l : List (Edges n)) :
    chooseBest f X r o l = (l.foldl (TOcb f X r) o, l.length) := by
  unfold chooseBest
  rw [TO_foldl_gen _ (TOcb f X r) (fun _ => 1) (fun b k a => rfl)]
  simp

theorem TO_cb_spec (f : Finset (Fin n) → ℕ) (X : Finset (Fin n)) (r : Fin n)
    (o : Option (Edges n)) (T : Edges n) :
    ∃ T', TOcb f X r o T = some T' ∧ fX f X r T ≤ fX f X r T' ∧
      (T' = T ∨ o = some T') ∧ (∀ T0, o = some T0 → fX f X r T0 ≤ fX f X r T') := by
  cases o with
  | none => exact ⟨T, rfl, le_rfl, Or.inl rfl, by simp⟩
  | some old =>
    unfold TOcb
    by_cases h : fX f X r old < fX f X r T
    · refine ⟨T, by simp [h], le_rfl, Or.inl rfl, ?_⟩
      intro T0 h0; cases h0; exact h.le
    · refine ⟨old, by simp [h], not_lt.1 h, Or.inr rfl, ?_⟩
      intro T0 h0; cases h0; exact le_rfl

/-- Spec of a conditional best-so-far fold. -/
theorem TO_fold_best_spec (f : Finset (Fin n) → ℕ) (X : Finset (Fin n)) (r : Fin n)
    (P : Edges n → Prop) (h : Option (Edges n) → Edges n → Option (Edges n))
    (hP : ∀ o T, P T → h o T = TOcb f X r o T) (hnP : ∀ o T, ¬ P T → h o T = o)
    (l : List (Edges n)) (o : Option (Edges n)) :
    (∀ T, l.foldl h o = some T → o = some T ∨ (T ∈ l ∧ P T)) ∧
    (∀ T0, o = some T0 → ∃ T', l.foldl h o = some T' ∧ fX f X r T0 ≤ fX f X r T') ∧
    (∀ T ∈ l, P T → ∃ T', l.foldl h o = some T' ∧ fX f X r T ≤ fX f X r T') := by
  induction l generalizing o with
  | nil =>
    refine ⟨fun T hT => Or.inl hT, fun T0 h0 => ⟨T0, h0, le_rfl⟩, fun T hT => by simp at hT⟩
  | cons a t ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih (h o a)
    simp only [List.foldl_cons]
    refine ⟨?_, ?_, ?_⟩
    · intro T hT
      rcases ih1 T hT with h1 | ⟨h1, h2⟩
      · by_cases hPa : P a
        · rw [hP o a hPa] at h1
          obtain ⟨T', hT', -, hor, -⟩ := TO_cb_spec f X r o a
          rw [hT'] at h1; cases h1
          rcases hor with h3 | h3
          · subst h3; exact Or.inr ⟨List.mem_cons_self, hPa⟩
          · exact Or.inl h3
        · rw [hnP o a hPa] at h1; exact Or.inl h1
      · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩
    · intro T0 h0
      by_cases hPa : P a
      · obtain ⟨T', hT', -, -, hge⟩ := TO_cb_spec f X r o a
        rw [hP o a hPa] at ih2 ⊢
        obtain ⟨T'', h1, h2⟩ := ih2 T' hT'
        exact ⟨T'', h1, (hge T0 h0).trans h2⟩
      · rw [hnP o a hPa] at ih2 ⊢
        exact ih2 T0 h0
    · intro T hT hPT
      rcases List.mem_cons.1 hT with h1 | h1
      · subst h1
        obtain ⟨T', hT', hle, -, -⟩ := TO_cb_spec f X r o T
        rw [hP o T hPT] at ih2 ⊢
        obtain ⟨T'', h1, h2⟩ := ih2 T' hT'
        exact ⟨T'', h1, hle.trans h2⟩
      · exact ih3 T h1 hPT

theorem TO_cb_fold_spec (f : Finset (Fin n) → ℕ) (X : Finset (Fin n)) (r : Fin n)
    (l : List (Edges n)) (o : Option (Edges n)) :
    (∀ T, l.foldl (TOcb f X r) o = some T → o = some T ∨ T ∈ l) ∧
    (∀ T0, o = some T0 → ∃ T', l.foldl (TOcb f X r) o = some T' ∧
      fX f X r T0 ≤ fX f X r T') ∧
    (∀ T ∈ l, ∃ T', l.foldl (TOcb f X r) o = some T' ∧ fX f X r T ≤ fX f X r T') := by
  obtain ⟨h1, h2, h3⟩ := TO_fold_best_spec f X r (fun _ => True) (TOcb f X r)
    (fun _ _ _ => rfl) (fun _ _ h => absurd trivial h) l o
  exact ⟨fun T hT => (h1 T hT).imp id (fun h => h.1), h2, fun T hT => h3 T hT trivial⟩

/-! ### runPlan unfolding -/

theorem TO_runPlan_single (I : Inst n) (mode : Mode)
    (sub : Fin n → Finset (Fin n) → ℕ → Finset (Fin n) → Option (Edges n) × ℕ)
    (r : Fin n) (Y X : Finset (Fin n)) (Brem : ℕ) (acc : Edges n) :
    runPlan I mode sub [(r, Y)] X Brem acc =
      ((sub r Y Brem X).1.toList.map (fun T => acc ∪ T), (sub r Y Brem X).2) := by
  rw [runPlan.eq_2]

noncomputable def TOenumG (I : Inst n)
    (sub : Fin n → Finset (Fin n) → ℕ → Finset (Fin n) → Option (Edges n) × ℕ)
    (r : Fin n) (Y X : Finset (Fin n)) (tail : List (Fin n × Finset (Fin n))) (Brem : ℕ)
    (acc : Edges n) (b : ℕ) : List (Edges n) :=
  match (sub r Y b X).1 with
  | none => []
  | some T => (runPlan I .enum sub tail (X ∪ verts r T) (Brem - b) (acc ∪ T)).1

noncomputable def TOenumH (I : Inst n)
    (sub : Fin n → Finset (Fin n) → ℕ → Finset (Fin n) → Option (Edges n) × ℕ)
    (r : Fin n) (Y X : Finset (Fin n)) (tail : List (Fin n × Finset (Fin n))) (Brem : ℕ)
    (acc : Edges n) (b : ℕ) : ℕ :=
  (sub r Y b X).2 + match (sub r Y b X).1 with
  | none => 0
  | some T => (runPlan I .enum sub tail (X ∪ verts r T) (Brem - b) (acc ∪ T)).2

theorem TO_runPlan_enum (I : Inst n)
    (sub : Fin n → Finset (Fin n) → ℕ → Finset (Fin n) → Option (Edges n) × ℕ)
    (r : Fin n) (Y X : Finset (Fin n)) (tail : List (Fin n × Finset (Fin n)))
    (htail : tail ≠ []) (Brem : ℕ) (acc : Edges n) :
    runPlan I .enum sub ((r, Y) :: tail) X Brem acc =
      ((List.range (Brem + 1)).flatMap (TOenumG I sub r Y X tail Brem acc),
       ((List.range (Brem + 1)).map (TOenumH I sub r Y X tail Brem acc)).sum) := by
  rw [runPlan.eq_3 _ _ _ _ _ _ _ _ htail]
  rw [TO_foldl_gen _ (fun c b => c ++ TOenumG I sub r Y X tail Brem acc b)
    (TOenumH I sub r Y X tail Brem acc)]
  · rw [TO_foldl_app]; simp
  · intro c k b
    unfold TOenumG TOenumH
    rcases hs : sub r Y b X with ⟨o, t⟩
    cases o with
    | none => simp
    | some T =>
      rcases hr : runPlan I Mode.enum sub tail (X ∪ verts r T) (Brem - b) (acc ∪ T) with
        ⟨more, t'⟩
      simp; omega

/-- The value-threshold probe used by binary-search mode. -/
noncomputable def TOprobe (I : Inst n)
    (sub : Fin n → Finset (Fin n) → ℕ → Finset (Fin n) → Option (Edges n) × ℕ)
    (r : Fin n) (Y X : Finset (Fin n)) (u : ℝ) : ℕ → Bool × ℕ := fun b =>
  match sub r Y b X with
  | (o, t) =>
    match o with
    | none => (false, t)
    | some T => (decide (u ≤ fX I.f X r T), t + 1)

noncomputable def TObsG (I : Inst n) (U : ℕ)
    (sub : Fin n → Finset (Fin n) → ℕ → Finset (Fin n) → Option (Edges n) × ℕ)
    (r : Fin n) (Y X : Finset (Fin n)) (tail : List (Fin n × Finset (Fin n))) (Brem : ℕ)
    (acc : Edges n) (u : ℝ) : List (Edges n) :=
  match (bsearch (TOprobe I sub r Y X u) 0 Brem).1 with
  | none => []
  | some b =>
    match (sub r Y b X).1 with
    | none => []
    | some T => (runPlan I (.bsearch U) sub tail (X ∪ verts r T) (Brem - b) (acc ∪ T)).1

noncomputable def TObsH (I : Inst n) (U : ℕ)
    (sub : Fin n → Finset (Fin n) → ℕ → Finset (Fin n) → Option (Edges n) × ℕ)
    (r : Fin n) (Y X : Finset (Fin n)) (tail : List (Fin n × Finset (Fin n))) (Brem : ℕ)
    (acc : Edges n) (u : ℝ) : ℕ :=
  (bsearch (TOprobe I sub r Y X u) 0 Brem).2 +
  match (bsearch (TOprobe I sub r Y X u) 0 Brem).1 with
  | none => 0
  | some b =>
    (sub r Y b X).2 +
    match (sub r Y b X).1 with
    | none => 0
    | some T => (runPlan I (.bsearch U) sub tail (X ∪ verts r T) (Brem - b) (acc ∪ T)).2

theorem TO_runPlan_bs (I : Inst n) (U : ℕ)
    (sub : Fin n → Finset (Fin n) → ℕ → Finset (Fin n) → Option (Edges n) × ℕ)
    (r : Fin n) (Y X : Finset (Fin n)) (tail : List (Fin n × Finset (Fin n)))
    (htail : tail ≠ []) (Brem : ℕ) (acc : Edges n) :
    runPlan I (.bsearch U) sub ((r, Y) :: tail) X Brem acc =
      (((List.range (U + 1)).map (fun k : ℕ => (k : ℝ))).flatMap
          (TObsG I U sub r Y X tail Brem acc),
       (((List.range (U + 1)).map (fun k : ℕ => (k : ℝ))).map
          (TObsH I U sub r Y X tail Brem acc)).sum) := by
  rw [runPlan.eq_4 _ _ _ _ _ _ _ _ _ htail]
  have hl : (do let a ← List.range (U + 1); pure (a : ℝ) : List ℝ) =
      (List.range (U + 1)).map (fun k : ℕ => (k : ℝ)) := by
    simp only [List.bind_eq_flatMap, List.pure_def]
    induction (List.range (U + 1)) with
    | nil => simp
    | cons a t ih => simp [ih]
  rw [hl]
  rw [TO_foldl_gen _ (fun c u => c ++ TObsG I U sub r Y X tail Brem acc u)
    (TObsH I U sub r Y X tail Brem acc)]
  · rw [TO_foldl_app]; simp
  · intro c k u
    unfold TObsG TObsH
    dsimp only
    rcases hb : bsearch (TOprobe I sub r Y X u) 0 Brem with ⟨ob, pr⟩
    erw [hb]
    cases ob with
    | none => simp
    | some b =>
      rcases hs : sub r Y b X with ⟨o, t⟩
      cases o with
      | none => simp [hs]; omega
      | some T =>
        rcases hr : runPlan I (Mode.bsearch U) sub tail (X ∪ verts r T) (Brem - b) (acc ∪ T)
          with ⟨more, t'⟩
        simp [hs, hr]; omega

end Unfold

section Sound
variable {n : ℕ}

def TOrc (r : Fin n) (T : Edges n) : Prop := ∀ w ∈ verts r T, Reaches T r w

theorem TO_rc_empty (r : Fin n) : TOrc r (∅ : Edges n) := by
  intro w hw
  rcases TO_mem_verts.1 hw with h | ⟨e, he, -⟩
  · subst h; exact ReflTransGen.refl
  · simp at he

theorem TO_rc_union {r v : Fin n} {A T : Edges n} (hA : TOrc r A) (hv : v ∈ verts r A)
    (hT : TOrc v T) : TOrc r (A ∪ T) := by
  intro w hw
  rcases TO_mem_verts.1 hw with h | ⟨e, he, h⟩
  · subst h; exact ReflTransGen.refl
  · rcases Finset.mem_union.1 he with he | he
    · exact TO_reaches_mono Finset.subset_union_left
        (hA w (TO_mem_verts.2 (Or.inr ⟨e, he, h⟩)))
    · have h1 := TO_reaches_mono (Finset.subset_union_left (s₂ := T)) (hA v hv)
      have h2 := TO_reaches_mono (Finset.subset_union_right (s₁ := A))
        (hT w (TO_mem_verts.2 (Or.inr ⟨e, he, h⟩)))
      exact h1.trans h2

theorem TO_verts_union_left (r : Fin n) (A T : Edges n) : verts r A ⊆ verts r (A ∪ T) :=
  TO_verts_mono Finset.subset_union_left

theorem TO_verts_union_right {r v : Fin n} {A : Edges n} (T : Edges n) (hv : v ∈ verts r A) :
    verts v T ⊆ verts r (A ∪ T) := by
  intro w hw
  rcases TO_mem_verts.1 hw with h | ⟨e, he, h⟩
  · subst h; exact TO_verts_union_left r A T hv
  · exact TO_mem_verts.2 (Or.inr ⟨e, Finset.mem_union_right _ he, h⟩)

theorem TO_cost_union_le (c : Fin n → Fin n → ℕ) (A T : Edges n) :
    cost c (A ∪ T) ≤ cost c A + cost c T := by
  unfold cost
  have := Finset.sum_union_inter (s₁ := A) (s₂ := T) (f := fun e => c e.1 e.2)
  omega

theorem TO_cost_union_disj (c : Fin n → Fin n → ℕ) {A T : Edges n} (h : Disjoint A T) :
    cost c (A ∪ T) = cost c A + cost c T := by
  unfold cost
  exact Finset.sum_union h

theorem TO_cost_mono (c : Fin n → Fin n → ℕ) {A T : Edges n} (h : A ⊆ T) :
    cost c A ≤ cost c T := by
  unfold cost
  exact Finset.sum_le_sum_of_subset h

def TOys : List (Fin n × Finset (Fin n)) → Finset (Fin n)
  | [] => ∅
  | x :: t => x.2 ∪ TOys t

def TOrootsOK : Finset (Fin n) → List (Fin n × Finset (Fin n)) → Prop
  | _, [] => True
  | S, x :: t => x.1 ∈ S ∧ TOrootsOK (S ∪ x.2) t

theorem TO_ys_append (p q : List (Fin n × Finset (Fin n))) :
    TOys (p ++ q) = TOys p ∪ TOys q := by
  induction p with
  | nil => simp [TOys]
  | cons x t ih => simp [TOys, ih, Finset.union_assoc]

theorem TO_rootsOK_mono : ∀ (p : List (Fin n × Finset (Fin n))) (S S' : Finset (Fin n)),
    S ⊆ S' → TOrootsOK S p → TOrootsOK S' p
  | [], _, _, _, _ => trivial
  | x :: t, S, S', h, ⟨h1, h2⟩ =>
    ⟨h h1, TO_rootsOK_mono t _ _ (Finset.union_subset_union h le_rfl) h2⟩

theorem TO_rootsOK_append : ∀ (p q : List (Fin n × Finset (Fin n))) (S : Finset (Fin n)),
    TOrootsOK S p → TOrootsOK (S ∪ TOys p) q → TOrootsOK S (p ++ q)
  | [], q, S, _, h => by simpa [TOys] using h
  | x :: t, q, S, ⟨h1, h2⟩, h => by
    refine ⟨h1, TO_rootsOK_append t q _ h2 ?_⟩
    simpa [TOys, Finset.union_assoc] using h

theorem TO_rootsOK_roots : ∀ (p : List (Fin n × Finset (Fin n))) (S : Finset (Fin n)),
    TOrootsOK S p → ∀ x ∈ p, x.1 ∈ S ∪ TOys p
  | [], _, _, x, hx => by simp at hx
  | y :: t, S, ⟨h1, h2⟩, x, hx => by
    rcases List.mem_cons.1 hx with h | h
    · subst h; exact Finset.mem_union_left _ h1
    · have := TO_rootsOK_roots t _ h2 x h
      simp only [TOys, Finset.mem_union] at this ⊢
      tauto

theorem TO_leafPlans_props : ∀ (s : ℕ) (r : Fin n) (Y : Finset (Fin n))
    (p : List (Fin n × Finset (Fin n))), p ∈ leafPlans s r Y →
    TOrootsOK {r} p ∧ Y ⊆ insert r (TOys p) ∧ (∀ x ∈ p, x.2.card ≤ Y.card + s) ∧
      p.length = 2 ^ s
  | 0, r, Y, p, hp => by
    simp [leafPlans] at hp
    subst hp
    refine ⟨⟨by simp, trivial⟩, ?_, by simp, by simp⟩
    intro y hy; simp [TOys, hy]
  | s + 1, r, Y, p, hp => by
    rw [leafPlans.eq_2] at hp
    simp only [List.mem_flatMap, List.mem_map] at hp
    obtain ⟨v, -, S, hS, L, hL, R, hR, rfl⟩ := hp
    have hS' : S ⊆ Y := by simpa using hS
    obtain ⟨hL1, hL2, hL3, hL4⟩ := TO_leafPlans_props s r _ L hL
    obtain ⟨hR1, hR2, hR3, hR4⟩ := TO_leafPlans_props s v _ R hR
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply TO_rootsOK_append _ _ _ hL1
      apply TO_rootsOK_mono _ {v} _ _ hR1
      intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      by_cases hvr : w = r
      · subst hvr; simp
      · have : w ∈ (S ∪ {w}) \ {r} := by simp [hvr]
        have := hL2 this
        rw [Finset.mem_insert] at this
        rcases this with h | h
        · exact absurd h hvr
        · exact Finset.mem_union_right _ h
    · intro y hy
      rw [TO_ys_append]
      by_cases hy1 : y ∈ S ∪ {v}
      · by_cases hyr : y = r
        · subst hyr; simp
        · have : y ∈ (S ∪ {v}) \ {r} := by simp [hyr]; simpa using hy1
          have := hL2 this
          rw [Finset.mem_insert] at this
          rcases this with h | h
          · exact absurd h hyr
          · simp [h]
      · have : y ∈ Y \ (S ∪ {v}) := Finset.mem_sdiff.2 ⟨hy, hy1⟩
        have := hR2 this
        rw [Finset.mem_insert] at this
        rcases this with h | h
        · subst h; simp at hy1
        · simp [h]
    · intro x hx
      rcases List.mem_append.1 hx with h | h
      · have := hL3 x h
        have h1 : ((S ∪ {v}) \ {r}).card ≤ Y.card + 1 := by
          calc ((S ∪ {v}) \ {r}).card ≤ (S ∪ {v}).card := Finset.card_le_card Finset.sdiff_subset
            _ ≤ S.card + ({v} : Finset (Fin n)).card := Finset.card_union_le _ _
            _ ≤ Y.card + 1 := by simp [Finset.card_le_card hS']
        omega
      · have := hR3 x h
        have h1 : (Y \ (S ∪ {v})).card ≤ Y.card := Finset.card_le_card Finset.sdiff_subset
        omega
    · simp [hL4, hR4, pow_succ]; ring

/-! ### Binary search -/

theorem TO_bsearchAux_sound (P : ℕ → Bool × ℕ) : ∀ (fuel lo hi b : ℕ),
    (bsearchAux P fuel lo hi).1 = some b → lo ≤ b ∧ b ≤ hi ∧ (P b).1 = true
  | 0, lo, hi, b, h => by simp [bsearchAux] at h
  | fuel + 1, lo, hi, b, h => by
    rw [bsearchAux.eq_2] at h
    by_cases hlt : hi < lo
    · simp [hlt] at h
    · simp only [hlt, if_false] at h
      rcases hP : P (lo + (hi - lo) / 2) with ⟨ok, t⟩
      rw [hP] at h
      cases ok with
      | true =>
        simp only [if_true] at h
        by_cases hm : lo + (hi - lo) / 2 = lo
        · simp only [hm, if_true] at h
          cases h
          refine ⟨le_rfl, by omega, ?_⟩
          rw [← hm, hP]
        · simp only [hm, if_false] at h
          rcases hr : bsearchAux P fuel lo (lo + (hi - lo) / 2 - 1) with ⟨ob, t'⟩
          rw [hr] at h
          cases ob with
          | none =>
            simp at h; subst h
            refine ⟨by omega, by omega, by rw [hP]⟩
          | some x =>
            simp at h; subst h
            have := TO_bsearchAux_sound P fuel lo _ x (by rw [hr])
            exact ⟨this.1, by omega, this.2.2⟩
      | false =>
        simp only [Bool.false_eq_true, if_false] at h
        rcases hr : bsearchAux P fuel (lo + (hi - lo) / 2 + 1) hi with ⟨ob, t'⟩
        rw [hr] at h
        simp at h
        subst h
        have := TO_bsearchAux_sound P fuel _ hi b (by rw [hr])
        exact ⟨by omega, this.2.1, this.2.2⟩

theorem TO_bsearchAux_find (P : ℕ → Bool × ℕ) : ∀ (fuel lo hi bstar : ℕ),
    hi + 1 - lo ≤ fuel → lo ≤ bstar → bstar ≤ hi →
    (∀ b, bstar ≤ b → b ≤ hi → (P b).1 = true) →
    ∃ b, (bsearchAux P fuel lo hi).1 = some b ∧ b ≤ bstar
  | 0, lo, hi, bstar, hf, h1, h2, _ => by omega
  | fuel + 1, lo, hi, bstar, hf, h1, h2, hP => by
    rw [bsearchAux.eq_2]
    have hlt : ¬ hi < lo := by omega
    simp only [hlt, if_false]
    set mid := lo + (hi - lo) / 2 with hmid
    rcases hPm : P mid with ⟨ok, t⟩
    cases ok with
    | true =>
      simp only [if_true]
      by_cases hm : mid = lo
      · simp only [hm, if_true]
        exact ⟨lo, rfl, h1⟩
      · simp only [hm, if_false]
        rcases hr : bsearchAux P fuel lo (mid - 1) with ⟨ob, t'⟩
        cases ob with
        | none =>
          simp only [Option.orElse_none]
          refine ⟨mid, rfl, ?_⟩
          by_contra hc
          push Not at hc
          obtain ⟨b, hb, hb2⟩ := TO_bsearchAux_find P fuel lo (mid - 1) bstar (by omega)
            h1 (by omega) (fun b hb1 hb2 => hP b hb1 (by omega))
          rw [hr] at hb; simp at hb
        | some x =>
          simp only [Option.orElse_some]
          refine ⟨x, rfl, ?_⟩
          have hx := TO_bsearchAux_sound P fuel lo (mid - 1) x (by rw [hr])
          by_cases hc : bstar ≤ mid - 1
          · obtain ⟨b, hb, hb2⟩ := TO_bsearchAux_find P fuel lo (mid - 1) bstar (by omega)
              h1 hc (fun b hb1 hb2 => hP b hb1 (by omega))
            rw [hr] at hb; simp at hb; omega
          · omega
    | false =>
      simp only [Bool.false_eq_true, if_false]
      have hmb : mid < bstar := by
        by_contra hc
        push Not at hc
        have := hP mid hc (by omega)
        rw [hPm] at this; simp at this
      rcases hr : bsearchAux P fuel (mid + 1) hi with ⟨ob, t'⟩
      obtain ⟨b, hb, hb2⟩ := TO_bsearchAux_find P fuel (mid + 1) hi bstar (by omega)
        (by omega) h2 hP
      rw [hr] at hb
      simp at hb
      subst hb
      exact ⟨b, rfl, hb2⟩

end Sound

end TreeOrient.RecGreedy


namespace TreeOrient.RecGreedy

open Relation

section SoundRG
variable {n : ℕ}

abbrev TOSub (n : ℕ) := Fin n → Finset (Fin n) → ℕ → Finset (Fin n) → Option (Edges n) × ℕ

def TOsound (I : Inst n) (sub : TOSub n) : Prop :=
  ∀ r Y b X T, (sub r Y b X).1 = some T → Feasible I.c r Y b T

theorem TO_bsearch_sound (P : ℕ → Bool × ℕ) (Brem b : ℕ) (h : (bsearch P 0 Brem).1 = some b) :
    b ≤ Brem ∧ (P b).1 = true := by
  unfold bsearch at h
  have := TO_bsearchAux_sound P _ 0 Brem b h
  exact ⟨this.2.1, this.2.2⟩

theorem TO_runPlan_mem_cons2 (I : Inst n) (mode : Mode) (sub : TOSub n)
    (v : Fin n) (Y1 X : Finset (Fin n)) (tail : List (Fin n × Finset (Fin n)))
    (htail : tail ≠ []) (Brem : ℕ) (acc : Edges n) (T : Edges n)
    (hT : T ∈ (runPlan I mode sub ((v, Y1) :: tail) X Brem acc).1) :
    ∃ b T1, b ≤ Brem ∧ (sub v Y1 b X).1 = some T1 ∧
      T ∈ (runPlan I mode sub tail (X ∪ verts v T1) (Brem - b) (acc ∪ T1)).1 := by
  cases mode with
  | enum =>
    rw [TO_runPlan_enum I sub v Y1 X tail htail] at hT
    obtain ⟨b, hb, hT⟩ := List.mem_flatMap.1 hT
    unfold TOenumG at hT
    rcases hs : (sub v Y1 b X).1 with _ | T1
    · rw [hs] at hT; simp at hT
    · rw [hs] at hT
      exact ⟨b, T1, by simp at hb; omega, hs, hT⟩
  | bsearch U =>
    rw [TO_runPlan_bs I U sub v Y1 X tail htail] at hT
    obtain ⟨u, -, hT⟩ := List.mem_flatMap.1 hT
    unfold TObsG at hT
    rcases hb : (bsearch (TOprobe I sub v Y1 X u) 0 Brem).1 with _ | b
    · rw [hb] at hT; simp at hT
    · rw [hb] at hT
      dsimp only at hT
      have hbB := (TO_bsearch_sound _ Brem b hb).1
      rcases hs : (sub v Y1 b X).1 with _ | T1
      · rw [hs] at hT; simp at hT
      · rw [hs] at hT
        exact ⟨b, T1, hbB, hs, hT⟩

theorem TO_runPlan_sound (I : Inst n) (mode : Mode) (sub : TOSub n) (hsnd : TOsound I sub)
    (r0 : Fin n) (B : ℕ) : ∀ (plan : List (Fin n × Finset (Fin n))) (S X : Finset (Fin n))
    (Brem : ℕ) (acc : Edges n), TOrootsOK S plan → S ⊆ verts r0 acc → TOrc r0 acc →
    cost I.c acc + Brem ≤ B →
    ∀ T ∈ (runPlan I mode sub plan X Brem acc).1,
      TOrc r0 T ∧ cost I.c T ≤ B ∧ S ∪ TOys plan ⊆ verts r0 T ∧ acc ⊆ T
  | [], _, _, _, _, _, _, _, _, T, hT => by simp [runPlan.eq_1] at hT
  | [(v, Y1)], S, X, Brem, acc, hok, hS, hrc, hc, T, hT => by
    rw [TO_runPlan_single] at hT
    simp only [List.mem_map, Option.mem_toList] at hT
    obtain ⟨T1, hT1, rfl⟩ := hT
    obtain ⟨hf1, hf2, hf3⟩ := hsnd v Y1 Brem X T1 hT1
    have hv : v ∈ verts r0 acc := hS hok.1
    refine ⟨TO_rc_union hrc hv hf1, ?_, ?_, Finset.subset_union_left⟩
    · have := TO_cost_union_le I.c acc T1; omega
    · simp only [TOys, Finset.union_empty]
      apply Finset.union_subset
      · exact hS.trans (TO_verts_union_left r0 acc T1)
      · exact hf3.trans (TO_verts_union_right T1 hv)
  | (v, Y1) :: a :: t, S, X, Brem, acc, hok, hS, hrc, hc, T, hT => by
    obtain ⟨b, T1, hb, hT1, hT⟩ := TO_runPlan_mem_cons2 I mode sub v Y1 X (a :: t)
      (List.cons_ne_nil _ _) Brem acc T hT
    obtain ⟨hf1, hf2, hf3⟩ := hsnd v Y1 b X T1 hT1
    have hv : v ∈ verts r0 acc := hS hok.1
    have IH := TO_runPlan_sound I mode sub hsnd r0 B (a :: t) (S ∪ Y1) (X ∪ verts v T1)
      (Brem - b) (acc ∪ T1) hok.2 (Finset.union_subset
        (hS.trans (TO_verts_union_left r0 acc T1)) (hf3.trans (TO_verts_union_right T1 hv)))
      (TO_rc_union hrc hv hf1) (by have := TO_cost_union_le I.c acc T1; omega) T hT
    obtain ⟨h1, h2, h3, h4⟩ := IH
    refine ⟨h1, h2, ?_, Finset.subset_union_left.trans h4⟩
    have : S ∪ TOys ((v, Y1) :: a :: t) = S ∪ Y1 ∪ TOys (a :: t) := by
      simp only [TOys]; rw [Finset.union_assoc]
    rw [this]; exact h3

end SoundRG

section RGeqs
variable {n : ℕ}

theorem TO_rg_succ_eq (I : Inst n) (s : ℕ) (mode : Mode) (i : ℕ) (r : Fin n)
    (Y₀ : Finset (Fin n)) (B : ℕ) (X : Finset (Fin n)) (hi : i ≠ 0)
    (hcap : ¬ capImp s (i + 1) < ((Y₀.erase r).card : ℝ)) :
    rg I s mode (i + 1) r Y₀ B X =
      (((leafPlans s r (Y₀.erase r)).flatMap
          (fun p => (runPlan I mode (rg I s mode i) p X B ∅).1)).foldl (TOcb I.f X r)
          (if Y₀.erase r = ∅ then some ∅ else none),
       1 + ((leafPlans s r (Y₀.erase r)).map (fun p =>
          (runPlan I mode (rg I s mode i) p X B ∅).2 +
          (runPlan I mode (rg I s mode i) p X B ∅).1.length)).sum) := by
  rw [rg.eq_2]
  simp only [hcap, if_false, hi]
  rw [TO_foldl_gen _ (fun b p => (runPlan I mode (rg I s mode i) p X B ∅).1.foldl (TOcb I.f X r) b)
    (fun p => (runPlan I mode (rg I s mode i) p X B ∅).2 +
          (runPlan I mode (rg I s mode i) p X B ∅).1.length)]
  · rw [List.foldl_flatMap]
  · intro b k p
    rcases hr : runPlan I mode (rg I s mode i) p X B ∅ with ⟨c, t⟩
    simp only [TO_chooseBest_eq]
    rw [Nat.add_assoc]

open Classical in
theorem TO_rg_base_eq (I : Inst n) (s : ℕ) (mode : Mode) (r : Fin n)
    (Y₀ : Finset (Fin n)) (B : ℕ) (X : Finset (Fin n)) (hs : s ≠ 1)
    (hcap : ¬ capImp s (0 + 1) < ((Y₀.erase r).card : ℝ)) :
    rg I s mode (0 + 1) r Y₀ B X =
      ((edgeCandidates n (Nat.floor (capImp s 1))).foldl
          (fun b T => if IsArbo r T ∧ Y₀.erase r ⊆ verts r T ∧ cost I.c T ≤ B
            then TOcb I.f X r b T else b)
          (if Y₀.erase r = ∅ then some ∅ else none),
       1 + (edgeCandidates n (Nat.floor (capImp s 1))).length) := by
  rw [rg.eq_2]
  simp only [hcap, if_false, hs, if_true]
  rw [TO_foldl_gen _ (fun b T => if IsArbo r T ∧ Y₀.erase r ⊆ verts r T ∧ cost I.c T ≤ B
            then TOcb I.f X r b T else b) (fun _ => 1)]
  · simp
  · intro b k T
    by_cases hc : IsArbo r T ∧ Y₀.erase r ⊆ verts r T ∧ cost I.c T ≤ B
    · simp only [hc, if_true, TO_chooseBest_eq]; rfl
    · simp only [hc, if_false]

theorem TO_rg_one_eq (I : Inst n) (mode : Mode) (r : Fin n)
    (Y₀ : Finset (Fin n)) (B : ℕ) (X : Finset (Fin n))
    (hcap : ¬ capImp 1 (0 + 1) < ((Y₀.erase r).card : ℝ)) :
    rg I 1 mode (0 + 1) r Y₀ B X = rgBasic I mode 1 r (Y₀.erase r) B X := by
  rw [rg.eq_2]
  simp only [hcap, if_false, if_true]

theorem TO_rgBasic_eq (I : Inst n) (mode : Mode) (r : Fin n)
    (Y : Finset (Fin n)) (B : ℕ) (X : Finset (Fin n)) :
    rgBasic I mode 1 r Y B X =
      if capImp 1 (0 + 1) < ((Y.erase r).card : ℝ) then (none, 1)
      else if Y.erase r = ∅ then
        (((List.finRange n).filterMap (fun v =>
          if (decide (v = r) || decide (B < I.c r v)) = true then none
          else some ({(r, v)} : Edges n))).foldl (TOcb I.f X r) (some ∅), 1 + n)
      else
        ((match (Y.erase r).toList with
          | [v] => if I.c r v ≤ B then some ({(r, v)} : Edges n) else none
          | _ => none), 1 + n) := by
  rw [rgBasic.eq_2]
  simp only [if_true]
  split_ifs <;> simp [TO_chooseBest_eq] <;> rfl

end RGeqs

end TreeOrient.RecGreedy


namespace TreeOrient.RecGreedy

open Relation

section SoundAll
variable {n : ℕ}

theorem TO_cost_single (c : Fin n → Fin n → ℕ) (a b : Fin n) :
    cost c ({(a, b)} : Edges n) = c a b := by
  unfold cost; simp

theorem TO_Y_lift {r : Fin n} {Y S : Finset (Fin n)} (h : Y.erase r ⊆ S) (hr : r ∈ S) :
    Y ⊆ S := by
  intro y hy
  by_cases hyr : y = r
  · subst hyr; exact hr
  · exact h (Finset.mem_erase.2 ⟨hyr, hy⟩)

theorem TO_feas_lift {c : Fin n → Fin n → ℕ} {r : Fin n} {Y : Finset (Fin n)} {B : ℕ}
    {T : Edges n} (h : Feasible c r (Y.erase r) B T) : Feasible c r Y B T :=
  ⟨h.1, h.2.1, TO_Y_lift h.2.2 (TO_root_mem_verts r T)⟩

theorem TO_feas_empty (c : Fin n → Fin n → ℕ) (r : Fin n) {Y : Finset (Fin n)} (B : ℕ)
    (hY : Y.erase r = ∅) : Feasible c r Y B ∅ := by
  refine ⟨TO_rc_empty r, by simp [cost], ?_⟩
  apply TO_Y_lift (r := r) _ (TO_root_mem_verts r ∅)
  rw [hY]; exact Finset.empty_subset _

theorem TO_feas_single (c : Fin n → Fin n → ℕ) (r v : Fin n) {Y : Finset (Fin n)} {B : ℕ}
    (hc : c r v ≤ B) (hY : Y.erase r ⊆ {v}) : Feasible c r Y B {(r, v)} := by
  have hv : v ∈ verts r ({(r, v)} : Edges n) :=
    TO_snd_mem_verts (e := (r, v)) (Finset.mem_singleton_self _)
  refine ⟨?_, by rw [TO_cost_single]; exact hc, ?_⟩
  · intro w hw
    rcases TO_mem_verts.1 hw with h | ⟨e, he, h⟩
    · subst h; exact ReflTransGen.refl
    · rw [Finset.mem_singleton] at he; subst he
      rcases h with h | h
      · simp at h; subst h; exact ReflTransGen.refl
      · simp at h; subst h; exact TO_reaches_edge (Finset.mem_singleton_self _)
  · apply TO_Y_lift _ (TO_root_mem_verts r _)
    intro y hy; have := hY hy; rw [Finset.mem_singleton] at this; subst this; exact hv

theorem TO_rgBasic1_sound (I : Inst n) (mode : Mode) (r : Fin n) (Y : Finset (Fin n)) (B : ℕ)
    (X : Finset (Fin n)) (T : Edges n) (h : (rgBasic I mode 1 r Y B X).1 = some T) :
    Feasible I.c r Y B T := by
  rw [TO_rgBasic_eq] at h
  split_ifs at h with h1 h2
  · obtain ⟨hs1, -, -⟩ := TO_cb_fold_spec I.f X r _ (some ∅)
    rcases hs1 T h with h3 | h3
    · cases h3; exact TO_feas_empty _ _ _ h2
    · simp only [List.mem_filterMap, List.mem_finRange, true_and] at h3
      obtain ⟨v, hv⟩ := h3
      split_ifs at hv with hv'
      · cases hv
        have hc : I.c r v ≤ B := by
          by_contra hc'; exact hv' (by simp; omega)
        exact TO_feas_single _ _ _ hc (by rw [h2]; exact Finset.empty_subset _)
  · simp only at h
    rcases hl : (Y.erase r).toList with _ | ⟨v, _ | ⟨w, t⟩⟩
    · rw [hl] at h; simp at h
    · rw [hl] at h
      simp only at h
      split_ifs at h with hc
      · cases h
        apply TO_feas_single _ _ _ hc
        intro y hy
        have : y ∈ (Y.erase r).toList := Finset.mem_toList.2 hy
        rw [hl] at this; simpa using this
    · rw [hl] at h; simp at h

theorem TO_rg_sound (I : Inst n) (s : ℕ) (mode : Mode) : ∀ i, TOsound I (rg I s mode i)
  | 0 => by intro r Y b X T h; simp [rg.eq_1] at h
  | i + 1 => by
    intro r Y₀ B X T h
    by_cases hcap : capImp s (i + 1) < ((Y₀.erase r).card : ℝ)
    · rw [rg.eq_2] at h; simp [hcap] at h
    by_cases hi : i = 0
    · subst hi
      by_cases hs : s = 1
      · subst hs
        rw [TO_rg_one_eq I mode r Y₀ B X hcap] at h
        exact TO_feas_lift (TO_rgBasic1_sound I mode r _ B X T h)
      · classical
        rw [TO_rg_base_eq I s mode r Y₀ B X hs hcap] at h
        obtain ⟨hs1, -, -⟩ := TO_fold_best_spec I.f X r
          (fun T => IsArbo r T ∧ Y₀.erase r ⊆ verts r T ∧ cost I.c T ≤ B) _
          (fun o T hT => if_pos hT)
          (fun o T hT => if_neg hT) _ _
        rcases hs1 T h with h3 | ⟨-, h3⟩
        · split_ifs at h3 with hY
          · cases h3; exact TO_feas_empty _ _ _ hY
        · exact TO_feas_lift ⟨h3.1.2.2, h3.2.2, h3.2.1⟩
    · rw [TO_rg_succ_eq I s mode i r Y₀ B X hi hcap] at h
      obtain ⟨hs1, -, -⟩ := TO_cb_fold_spec I.f X r _ _
      rcases hs1 T h with h3 | h3
      · split_ifs at h3 with hY
        · cases h3; exact TO_feas_empty _ _ _ hY
      · obtain ⟨p, hp, hT⟩ := List.mem_flatMap.1 h3
        obtain ⟨hp1, hp2, -, -⟩ := TO_leafPlans_props s r _ p hp
        obtain ⟨h4, h5, h6, -⟩ := TO_runPlan_sound I mode (rg I s mode i) (TO_rg_sound I s mode i)
          r B p {r} X B ∅ hp1 (by simp [TO_root_mem_verts]) (TO_rc_empty r)
          (by simp [cost]) T hT
        refine TO_feas_lift ⟨h4, h5, ?_⟩
        intro y hy
        have := hp2 hy
        rw [Finset.mem_insert] at this
        rcases this with h7 | h7
        · subst h7; exact TO_root_mem_verts _ _
        · exact h6 (Finset.mem_union_right _ h7)

/-! ### Extracting an arborescence -/

theorem TO_exit_edge {T : Edges n} {W : Finset (Fin n)} {a w : Fin n} (h : Reaches T a w)
    (ha : a ∈ W) (hw : w ∉ W) : ∃ e ∈ T, e.1 ∈ W ∧ e.2 ∉ W := by
  induction h with
  | refl => exact absurd ha hw
  | @tail y z _ hyz ih =>
    by_cases hy : y ∈ W
    · exact ⟨(y, z), hyz, hy, hw⟩
    · exact ih hy

theorem TO_extract_aux {r : Fin n} {T : Edges n} (hT : TOrc r T) : ∀ k (A : Edges n),
    A ⊆ T → IsArbo r A → (verts r T).card - (verts r A).card ≤ k →
    ∃ A' ⊆ T, IsArbo r A' ∧ verts r A' = verts r T
  | 0, A, hAT, hA, hk => by
    refine ⟨A, hAT, hA, ?_⟩
    have hsub := TO_verts_mono (r := r) hAT
    exact Finset.eq_of_subset_of_card_le hsub (by omega)
  | k + 1, A, hAT, hA, hk => by
    have hsub := TO_verts_mono (r := r) hAT
    by_cases heq : verts r A = verts r T
    · exact ⟨A, hAT, hA, heq⟩
    obtain ⟨w, hwT, hwA⟩ : ∃ w ∈ verts r T, w ∉ verts r A := by
      by_contra hc; push Not at hc
      exact heq (Finset.Subset.antisymm hsub hc)
    obtain ⟨e, heT, he1, he2⟩ := TO_exit_edge (hT w hwT) (TO_root_mem_verts r A) hwA
    have hvins : verts r (insert e A) = insert e.2 (verts r A) := by
      ext x
      simp only [TO_mem_verts, Finset.mem_insert]
      constructor
      · rintro (h | ⟨f, hf, h⟩)
        · exact Or.inr (Or.inl h)
        · rcases hf with hf | hf
          · subst hf
            rcases h with h | h
            · right; rw [← h]; exact TO_mem_verts.1 he1
            · left; exact h.symm
          · exact Or.inr (Or.inr ⟨f, hf, h⟩)
      · rintro (h | h | ⟨f, hf, h⟩)
        · exact Or.inr ⟨e, Or.inl rfl, Or.inr h.symm⟩
        · exact Or.inl h
        · exact Or.inr ⟨f, Or.inr hf, h⟩
    have hA' : IsArbo r (insert e A) := by
      refine ⟨?_, ?_, ?_⟩
      · intro f hf
        rcases Finset.mem_insert.1 hf with h | h
        · subst h; intro h2; rw [h2] at he2; exact he2 (TO_root_mem_verts r A)
        · exact hA.1 f h
      · intro f hf f' hf' hff
        rcases Finset.mem_insert.1 hf with h | h <;> rcases Finset.mem_insert.1 hf' with h' | h'
        · rw [h, h']
        · subst h; exact absurd (hff ▸ TO_snd_mem_verts (r := r) h') he2
        · subst h'; exact absurd (hff.symm ▸ TO_snd_mem_verts (r := r) h) he2
        · exact hA.2.1 f h f' h' hff
      · intro x hx
        rw [hvins, Finset.mem_insert] at hx
        rcases hx with h | h
        · subst h
          exact (TO_reaches_mono (Finset.subset_insert e A) (hA.2.2 _ he1)).tail
            (show (e.1, e.2) ∈ insert e A from Finset.mem_insert_self e A)
        · exact TO_reaches_mono (Finset.subset_insert e A) (hA.2.2 _ h)
    apply TO_extract_aux hT k (insert e A) (Finset.insert_subset heT hAT) hA'
    rw [hvins, Finset.card_insert_of_notMem he2]
    omega

theorem TO_extract {r : Fin n} {T : Edges n} (hT : TOrc r T) :
    ∃ A' ⊆ T, IsArbo r A' ∧ verts r A' = verts r T := by
  have h0 : IsArbo r (∅ : Edges n) := ⟨by simp, by simp, TO_rc_empty r⟩
  exact TO_extract_aux hT _ ∅ (Finset.empty_subset _) h0 le_rfl

end SoundAll

end TreeOrient.RecGreedy


namespace TreeOrient.RecGreedy

open Relation

section Submod
variable {n : ℕ}

theorem TO_dimret (f : Finset (Fin n) → ℕ) (hmono : IsMonotone f)
    (hsub : NonmonotoneSubmod.Shared.Submodular (fun S => (f S : ℝ)))
    {Z Z' : Finset (Fin n)} (V : Finset (Fin n)) (hZ : Z ⊆ Z') :
    (f (V ∪ Z') : ℝ) - f Z' ≤ (f (V ∪ Z) : ℝ) - f Z := by
  have h := hsub (V ∪ Z) Z'
  have h1 : V ∪ Z ∪ Z' = V ∪ Z' := by
    rw [Finset.union_assoc, Finset.union_eq_right.2 hZ]
  have h2 : Z ⊆ (V ∪ Z) ∩ Z' := Finset.subset_inter Finset.subset_union_right hZ
  have h3 : (f Z : ℝ) ≤ f ((V ∪ Z) ∩ Z') := by exact_mod_cast hmono _ _ h2
  simp only at h
  rw [h1] at h
  linarith

theorem TO_mono_real (f : Finset (Fin n) → ℕ) (hmono : IsMonotone f) {S T : Finset (Fin n)}
    (h : S ⊆ T) : (f S : ℝ) ≤ f T := by exact_mod_cast hmono _ _ h

/-- Union over a list of vertex sets. -/
def TObig {α : Type} (V : α → Finset (Fin n)) : List α → Finset (Fin n)
  | [] => ∅
  | a :: t => V a ∪ TObig V t

theorem TO_mem_big {α : Type} (V : α → Finset (Fin n)) (L : List α) (w : Fin n) :
    w ∈ TObig V L ↔ ∃ a ∈ L, w ∈ V a := by
  induction L with
  | nil => simp [TObig]
  | cons a t ih =>
    simp only [TObig, Finset.mem_union, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨b, hb, h⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨b, Or.inr hb, h⟩
    · rintro ⟨b, hb | hb, h⟩
      · subst hb; exact Or.inl h
      · exact Or.inr ⟨b, hb, h⟩

theorem TO_union_bound {α : Type} (f : Finset (Fin n) → ℕ) (hmono : IsMonotone f)
    (hsub : NonmonotoneSubmod.Shared.Submodular (fun S => (f S : ℝ)))
    (V : α → Finset (Fin n)) : ∀ (L : List α) (Z : Finset (Fin n)),
    (f (Z ∪ TObig V L) : ℝ) - f Z ≤ (L.map (fun a => (f (V a ∪ Z) : ℝ) - f Z)).sum
  | [], Z => by simp [TObig]
  | a :: t, Z => by
    have ih := TO_union_bound f hmono hsub V t (Z ∪ V a)
    have hsum : (t.map (fun b => (f (V b ∪ (Z ∪ V a)) : ℝ) - f (Z ∪ V a))).sum ≤
        (t.map (fun b => (f (V b ∪ Z) : ℝ) - f Z)).sum := by
      apply List.sum_le_sum
      intro b _
      exact TO_dimret f hmono hsub (V b) Finset.subset_union_left
    have heq : Z ∪ TObig V (a :: t) = Z ∪ V a ∪ TObig V t := by
      simp only [TObig, Finset.union_assoc]
    rw [heq, List.map_cons, List.sum_cons]
    have hc : Z ∪ V a = V a ∪ Z := Finset.union_comm _ _
    rw [hc] at ih hsum ⊢
    linarith

def TOmodeOK (mode : Mode) (f : Finset (Fin n) → ℕ) (X : Finset (Fin n)) (r : Fin n)
    (A : Edges n) : Prop :=
  match mode with
  | .enum => True
  | .bsearch U => fX f X r A ≤ U

theorem TO_fX_nonneg (f : Finset (Fin n) → ℕ) (hmono : IsMonotone f) (X : Finset (Fin n))
    (r : Fin n) (T : Edges n) : 0 ≤ fX f X r T := by
  unfold fX
  have := TO_mono_real f hmono (Finset.subset_union_right (s₁ := verts r T) (s₂ := X))
  linarith

theorem TO_fX_nat (f : Finset (Fin n) → ℕ) (hmono : IsMonotone f) (X : Finset (Fin n))
    (r : Fin n) (T : Edges n) :
    fX f X r T = ((f (verts r T ∪ X) - f X : ℕ) : ℝ) := by
  unfold fX
  have := hmono _ _ (Finset.subset_union_right (s₁ := verts r T) (s₂ := X))
  push_cast [this]; ring

theorem TO_fX_mono (f : Finset (Fin n) → ℕ) (hmono : IsMonotone f)
    (hsub : NonmonotoneSubmod.Shared.Submodular (fun S => (f S : ℝ)))
    {X X' : Finset (Fin n)} {r r' : Fin n} {A P : Edges n} (hX : X ⊆ X')
    (hV : verts r' P ⊆ verts r A) : fX f X' r' P ≤ fX f X r A := by
  unfold fX
  have h1 := TO_dimret f hmono hsub (verts r' P) hX
  have h2 := TO_mono_real f hmono (Finset.union_subset_union hV (le_refl X))
  linarith

theorem TO_modeOK_mono (mode : Mode) (f : Finset (Fin n) → ℕ) (hmono : IsMonotone f)
    (hsub : NonmonotoneSubmod.Shared.Submodular (fun S => (f S : ℝ)))
    {X X' : Finset (Fin n)} {r r' : Fin n} {A P : Edges n} (hX : X ⊆ X')
    (hV : verts r' P ⊆ verts r A) (h : TOmodeOK mode f X r A) : TOmodeOK mode f X' r' P := by
  cases mode with
  | enum => trivial
  | bsearch U =>
    unfold TOmodeOK at *
    exact (TO_fX_mono f hmono hsub hX hV).trans h

end Submod

section Decomp
variable {n : ℕ}

theorem TO_verts_union_split {r v : Fin n} {A1 A2 : Edges n} :
    verts r (A1 ∪ A2) ⊆ verts r A1 ∪ verts v A2 := by
  intro w hw
  rcases TO_mem_verts.1 hw with h | ⟨e, he, h⟩
  · exact Finset.mem_union_left _ (TO_mem_verts.2 (Or.inl h))
  · rcases Finset.mem_union.1 he with he | he
    · exact Finset.mem_union_left _ (TO_mem_verts.2 (Or.inr ⟨e, he, h⟩))
    · exact Finset.mem_union_right _ (TO_mem_verts.2 (Or.inr ⟨e, he, h⟩))

theorem TO_decomp (c : Fin n → Fin n → ℕ) : ∀ (s : ℕ) (r : Fin n) (Y : Finset (Fin n))
    (A : Edges n) (K : ℝ), 1 ≤ K → IsArbo r A → Y ⊆ verts r A →
    (A.card : ℝ) ≤ (3 / 2 : ℝ) ^ s * K →
    ∃ L : List (Fin n × Finset (Fin n) × Edges n),
      L.map (fun x => (x.1, x.2.1)) ∈ leafPlans s r Y ∧
      (∀ x ∈ L, IsArbo x.1 x.2.2 ∧ x.2.1 ⊆ verts x.1 x.2.2 ∧ (x.2.2.card : ℝ) ≤ K ∧
        verts x.1 x.2.2 ⊆ verts r A) ∧
      (L.map (fun x => cost c x.2.2)).sum ≤ cost c A ∧
      (∀ w ∈ verts r A, ∃ x ∈ L, w ∈ verts x.1 x.2.2)
  | 0, r, Y, A, K, hK, hA, hY, hcard => by
    refine ⟨[(r, Y, A)], by simp [leafPlans], ?_, by simp, ?_⟩
    · intro x hx
      simp at hx; subst hx
      exact ⟨hA, hY, by simpa using hcard, le_rfl⟩
    · intro w hw; exact ⟨(r, Y, A), by simp, hw⟩
  | s + 1, r, Y, A, K, hK, hA, hY, hcard => by
    classical
    have hpow : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ s * K := by
      have : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
      nlinarith
    obtain ⟨v, hvA, A1, A2, hdisj, hunion, hA1, hvA1, hA2, hc1, hc2⟩ :
        ∃ v ∈ verts r A, ∃ A₁ A₂ : Edges n,
          Disjoint A₁ A₂ ∧ A₁ ∪ A₂ = A ∧ IsArbo r A₁ ∧ v ∈ verts r A₁ ∧
          IsArbo v A₂ ∧ (A₁.card : ℝ) ≤ (3 / 2 : ℝ) ^ s * K ∧
          (A₂.card : ℝ) ≤ (3 / 2 : ℝ) ^ s * K := by
      by_cases h2 : 2 ≤ A.card
      · obtain ⟨v, hv, A₁, A₂, h1, h2', h3, h4, h5, h6, h7⟩ := TO_fact_2_2 A hA h2
        refine ⟨v, hv, A₁, A₂, h1, h2', h3, h4, h5, ?_, ?_⟩
        · have : (3 * A₁.card : ℝ) ≤ 2 * A.card := by exact_mod_cast h6
          rw [pow_succ] at hcard
          nlinarith
        · have : (3 * A₂.card : ℝ) ≤ 2 * A.card := by exact_mod_cast h7
          rw [pow_succ] at hcard
          nlinarith
      · refine ⟨r, TO_root_mem_verts r A, A, ∅, by simp, by simp, hA, TO_root_mem_verts r A,
          ⟨by simp, by simp, TO_rc_empty r⟩, ?_, by simp; linarith⟩
        have : (A.card : ℝ) ≤ 1 := by exact_mod_cast (by omega : A.card ≤ 1)
        linarith
    have hA1sub : verts r A1 ⊆ verts r A := TO_verts_mono (hunion ▸ Finset.subset_union_left)
    have hA2sub : verts v A2 ⊆ verts r A := by
      intro w hw
      rcases TO_mem_verts.1 hw with h | ⟨e, he, h⟩
      · subst h; exact hvA
      · exact TO_mem_verts.2 (Or.inr ⟨e, hunion ▸ Finset.mem_union_right _ he, h⟩)
    have hsplit : verts r A ⊆ verts r A1 ∪ verts v A2 := by
      rw [← hunion]; exact TO_verts_union_split
    set S := Y.filter (fun y => y ∈ verts r A1) with hSdef
    have hYL : (S ∪ {v}) \ {r} ⊆ verts r A1 := by
      intro y hy
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton, hSdef,
        Finset.mem_filter] at hy
      rcases hy.1 with h | h
      · exact h.2
      · subst h; exact hvA1
    have hYR : Y \ (S ∪ {v}) ⊆ verts v A2 := by
      intro y hy
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton, hSdef,
        Finset.mem_filter, not_or, not_and] at hy
      rcases Finset.mem_union.1 (hsplit (hY hy.1)) with h | h
      · exact absurd h (hy.2.1 hy.1)
      · exact h
    obtain ⟨L1, hL1p, hL1a, hL1c, hL1v⟩ := TO_decomp c s r _ A1 K hK hA1 hYL hc1
    obtain ⟨L2, hL2p, hL2a, hL2c, hL2v⟩ := TO_decomp c s v _ A2 K hK hA2 hYR hc2
    refine ⟨L1 ++ L2, ?_, ?_, ?_, ?_⟩
    · rw [leafPlans.eq_2, List.map_append]
      simp only [List.mem_flatMap, List.mem_map]
      refine ⟨v, List.mem_finRange v, S, ?_, _, hL1p, _, hL2p, rfl⟩
      simp [hSdef, Finset.filter_subset]
    · intro x hx
      rcases List.mem_append.1 hx with h | h
      · obtain ⟨a1, a2, a3, a4⟩ := hL1a x h; exact ⟨a1, a2, a3, a4.trans hA1sub⟩
      · obtain ⟨a1, a2, a3, a4⟩ := hL2a x h; exact ⟨a1, a2, a3, a4.trans hA2sub⟩
    · rw [List.map_append, List.sum_append, ← hunion, TO_cost_union_disj c hdisj]
      omega
    · intro w hw
      rcases Finset.mem_union.1 (hsplit hw) with h | h
      · obtain ⟨x, hx, h'⟩ := hL1v w h; exact ⟨x, List.mem_append_left _ hx, h'⟩
      · obtain ⟨x, hx, h'⟩ := hL2v w h; exact ⟨x, List.mem_append_right _ hx, h'⟩

end Decomp

end TreeOrient.RecGreedy


namespace TreeOrient.RecGreedy

open Relation

section RunPlanApprox
variable {n : ℕ}

def TOapprox (I : Inst n) (mode : Mode) (sub : TOSub n) (K : ℝ) (i : ℕ) : Prop :=
  ∀ r Y b X A, Compatible I.c r Y b K A → TOmodeOK mode I.f X r A →
    ∃ T, (sub r Y b X).1 = some T ∧ fX I.f X r A ≤ i * fX I.f X r T

theorem TO_probe_true (I : Inst n) (sub : TOSub n) (r : Fin n) (Y X : Finset (Fin n)) (u : ℝ)
    (b : ℕ) : (TOprobe I sub r Y X u b).1 = true ↔
      ∃ T, (sub r Y b X).1 = some T ∧ u ≤ fX I.f X r T := by
  unfold TOprobe
  rcases hs : sub r Y b X with ⟨o, t⟩
  cases o with
  | none => simp
  | some T => simp

theorem TO_runPlan_enum_mem_of (I : Inst n) (sub : TOSub n) (v : Fin n) (Y1 X : Finset (Fin n))
    (tail : List (Fin n × Finset (Fin n))) (htail : tail ≠ []) (Brem : ℕ) (acc : Edges n)
    (b : ℕ) (T1 T : Edges n) (hb : b ≤ Brem) (hT1 : (sub v Y1 b X).1 = some T1)
    (hT : T ∈ (runPlan I .enum sub tail (X ∪ verts v T1) (Brem - b) (acc ∪ T1)).1) :
    T ∈ (runPlan I .enum sub ((v, Y1) :: tail) X Brem acc).1 := by
  rw [TO_runPlan_enum I sub v Y1 X tail htail]
  refine List.mem_flatMap.2 ⟨b, List.mem_range.2 (by omega), ?_⟩
  unfold TOenumG; rw [hT1]; exact hT

theorem TO_runPlan_bs_mem_of (I : Inst n) (U : ℕ) (sub : TOSub n) (v : Fin n)
    (Y1 X : Finset (Fin n))
    (tail : List (Fin n × Finset (Fin n))) (htail : tail ≠ []) (Brem : ℕ) (acc : Edges n)
    (k b : ℕ) (T1 T : Edges n) (hk : k ≤ U)
    (hb : (bsearch (TOprobe I sub v Y1 X (k : ℝ)) 0 Brem).1 = some b)
    (hT1 : (sub v Y1 b X).1 = some T1)
    (hT : T ∈ (runPlan I (.bsearch U) sub tail (X ∪ verts v T1) (Brem - b) (acc ∪ T1)).1) :
    T ∈ (runPlan I (.bsearch U) sub ((v, Y1) :: tail) X Brem acc).1 := by
  rw [TO_runPlan_bs I U sub v Y1 X tail htail]
  refine List.mem_flatMap.2 ⟨(k : ℝ), List.mem_map.2 ⟨k, List.mem_range.2 (by omega), rfl⟩, ?_⟩
  unfold TObsG; rw [hb]; dsimp only; rw [hT1]; exact hT

theorem TO_leaf_choice (I : Inst n) (hmono : IsMonotone I.f) (mode : Mode) (sub : TOSub n)
    (K : ℝ) (i : ℕ) (hi : 1 ≤ i) (happ : TOapprox I mode sub K i)
    (v : Fin n) (Y1 X : Finset (Fin n)) (P1 : Edges n) (tail : List (Fin n × Finset (Fin n)))
    (htail : tail ≠ []) (Brem : ℕ) (acc : Edges n)
    (hP1 : IsArbo v P1 ∧ Y1 ⊆ verts v P1 ∧ (P1.card : ℝ) ≤ K) (hcost : cost I.c P1 ≤ Brem)
    (hmode : TOmodeOK mode I.f X v P1) :
    ∃ b T1, b ≤ cost I.c P1 ∧ (sub v Y1 b X).1 = some T1 ∧
      fX I.f X v P1 ≤ i * fX I.f X v T1 ∧
      ∀ T, T ∈ (runPlan I mode sub tail (X ∪ verts v T1) (Brem - b) (acc ∪ T1)).1 →
        T ∈ (runPlan I mode sub ((v, Y1) :: tail) X Brem acc).1 := by
  cases mode with
  | enum =>
    obtain ⟨T1, hT1, hval⟩ := happ v Y1 (cost I.c P1) X P1
      ⟨hP1.1, hP1.2.1, hP1.2.2, le_rfl⟩ hmode
    exact ⟨cost I.c P1, T1, le_rfl, hT1, hval, fun T hT =>
      TO_runPlan_enum_mem_of I sub v Y1 X tail htail Brem acc _ T1 T hcost hT1 hT⟩
  | bsearch U =>
    set g := fX I.f X v P1 with hg
    have hg0 : 0 ≤ g := TO_fX_nonneg I.f hmono X v P1
    have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
    set θ : ℕ := ⌈g / i⌉₊ with hθ
    have hθU : θ ≤ U := by
      rw [hθ, Nat.ceil_le]
      have hU : g ≤ U := hmode
      have : g / i ≤ g := div_le_self hg0 hiR
      linarith
    have hθg : g ≤ i * θ := by
      have := Nat.le_ceil (g / i)
      rw [← hθ] at this
      have hpos : (0 : ℝ) < i := by linarith
      rw [div_le_iff₀ hpos] at this
      linarith
    -- probe is true from cost P1 on
    have hprobe : ∀ b, cost I.c P1 ≤ b → b ≤ Brem →
        (TOprobe I sub v Y1 X (θ : ℝ) b).1 = true := by
      intro b hb1 _
      obtain ⟨T, hT, hval⟩ := happ v Y1 b X P1 ⟨hP1.1, hP1.2.1, hP1.2.2, hb1⟩ hmode
      rw [TO_probe_true]
      refine ⟨T, hT, ?_⟩
      have hTn := TO_fX_nat I.f hmono X v T
      rw [hTn] at hval ⊢
      rw [hθ]
      have hpos : (0 : ℝ) < i := by linarith
      have : g / i ≤ ((I.f (verts v T ∪ X) - I.f X : ℕ) : ℝ) := by
        rw [div_le_iff₀ hpos]; rw [← hg] at hval; linarith
      exact_mod_cast Nat.ceil_le.2 this
    obtain ⟨b, hb, hbP⟩ := TO_bsearchAux_find (TOprobe I sub v Y1 X (θ : ℝ)) (Brem + 1 - 0) 0
      Brem (cost I.c P1) le_rfl (Nat.zero_le _) hcost hprobe
    have hb' : (bsearch (TOprobe I sub v Y1 X (θ : ℝ)) 0 Brem).1 = some b := hb
    have hsound := TO_bsearch_sound _ Brem b hb'
    obtain ⟨T1, hT1, hval⟩ := (TO_probe_true I sub v Y1 X _ b).1 hsound.2
    refine ⟨b, T1, hbP, hT1, ?_, fun T hT =>
      TO_runPlan_bs_mem_of I U sub v Y1 X tail htail Brem acc θ b T1 T hθU hb' hT1 hT⟩
    have hiR0 : (0 : ℝ) ≤ i := by linarith
    calc g ≤ i * θ := hθg
      _ ≤ i * fX I.f X v T1 := mul_le_mul_of_nonneg_left hval hiR0

theorem TO_runPlan_approx (I : Inst n) (hmono : IsMonotone I.f)
    (hsub : NonmonotoneSubmod.Shared.Submodular (fun S => (I.f S : ℝ)))
    (mode : Mode) (sub : TOSub n) (K : ℝ) (i : ℕ) (hi : 1 ≤ i)
    (happ : TOapprox I mode sub K i) :
    ∀ (L : List (Fin n × Finset (Fin n) × Edges n)), L ≠ [] →
    ∀ (X : Finset (Fin n)) (Brem : ℕ) (acc : Edges n),
    (∀ x ∈ L, IsArbo x.1 x.2.2 ∧ x.2.1 ⊆ verts x.1 x.2.2 ∧ (x.2.2.card : ℝ) ≤ K) →
    (L.map (fun x => cost I.c x.2.2)).sum ≤ Brem →
    (∀ x ∈ L, TOmodeOK mode I.f X x.1 x.2.2) →
    ∃ T ∈ (runPlan I mode sub (L.map (fun x => (x.1, x.2.1))) X Brem acc).1,
      ∃ D Z, T = acc ∪ D ∧ X ⊆ Z ∧
        (∀ w ∈ Z, w ∈ X ∨ (∃ x ∈ L, x.1 = w) ∨ (∃ e ∈ D, e.1 = w ∨ e.2 = w)) ∧
        (L.map (fun x => (I.f (verts x.1 x.2.2 ∪ Z) : ℝ) - I.f Z)).sum ≤
          i * ((I.f Z : ℝ) - I.f X)
  := by
  intro L
  induction L with
  | nil => intro h; exact absurd rfl h
  | cons x t ih =>
  intro _ X Brem acc hcomp hcost hmode
  rcases t with _ | ⟨y, t⟩
  · obtain ⟨v, Y1, P1⟩ := x
    have hc : IsArbo v P1 ∧ Y1 ⊆ verts v P1 ∧ (P1.card : ℝ) ≤ K :=
      hcomp (v, Y1, P1) List.mem_cons_self
    have hcost' : cost I.c P1 ≤ Brem := by simpa using hcost
    have hm : TOmodeOK mode I.f X v P1 := hmode (v, Y1, P1) List.mem_cons_self
    have hcp : Compatible I.c v Y1 Brem K P1 := ⟨hc.1, hc.2.1, hc.2.2, hcost'⟩
    obtain ⟨T1, hT1, hval⟩ := happ v Y1 Brem X P1 hcp hm
    refine ⟨acc ∪ T1, ?_, T1, X ∪ verts v T1, rfl, Finset.subset_union_left, ?_, ?_⟩
    · simp only [List.map_cons, List.map_nil]
      rw [TO_runPlan_single]
      simp [hT1]
    · intro w hw
      rcases Finset.mem_union.1 hw with h | h
      · exact Or.inl h
      · rcases TO_mem_verts.1 h with h' | h'
        · exact Or.inr (Or.inl ⟨(v, Y1, P1), List.mem_cons_self, h'.symm⟩)
        · exact Or.inr (Or.inr h')
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have h1 := TO_dimret I.f hmono hsub (verts v P1)
        (Finset.subset_union_left (s₁ := X) (s₂ := verts v T1))
      unfold fX at hval
      rw [Finset.union_comm X (verts v T1)] at h1 ⊢
      linarith
  · obtain ⟨v, Y1, P1⟩ := x
    have hc : IsArbo v P1 ∧ Y1 ⊆ verts v P1 ∧ (P1.card : ℝ) ≤ K :=
      hcomp (v, Y1, P1) List.mem_cons_self
    have hm : TOmodeOK mode I.f X v P1 := hmode (v, Y1, P1) List.mem_cons_self
    simp only [List.map_cons, List.sum_cons] at hcost
    have hcost1 : cost I.c P1 ≤ Brem := by omega
    obtain ⟨b, T1, hb, hT1, hval, hmem⟩ := TO_leaf_choice I hmono mode sub K i hi happ v Y1 X P1
      ((y :: t).map (fun x => (x.1, x.2.1))) (by simp) Brem acc hc hcost1 hm
    have hX' : X ⊆ X ∪ verts v T1 := Finset.subset_union_left
    obtain ⟨T, hT, D, Z, hTD, hXZ, hZ, hsum⟩ := ih
      (by simp) (X ∪ verts v T1) (Brem - b) (acc ∪ T1)
      (fun z hz => hcomp z (List.mem_cons_of_mem _ hz))
      (by simp only [List.map_cons, List.sum_cons]; omega)
      (fun z hz => TO_modeOK_mono mode I.f hmono hsub hX' le_rfl
        (hmode z (List.mem_cons_of_mem _ hz)))
    refine ⟨T, ?_, T1 ∪ D, Z, ?_, hX'.trans hXZ, ?_, ?_⟩
    · simp only [List.map_cons] at hmem ⊢
      exact hmem T hT
    · rw [hTD, Finset.union_assoc]
    · intro w hw
      rcases hZ w hw with h | ⟨z, hz, h⟩ | ⟨e, he, h⟩
      · rcases Finset.mem_union.1 h with h' | h'
        · exact Or.inl h'
        · rcases TO_mem_verts.1 h' with h'' | ⟨e, he, h''⟩
          · exact Or.inr (Or.inl ⟨(v, Y1, P1), List.mem_cons_self, h''.symm⟩)
          · exact Or.inr (Or.inr ⟨e, Finset.mem_union_left _ he, h''⟩)
      · exact Or.inr (Or.inl ⟨z, List.mem_cons_of_mem _ hz, h⟩)
      · exact Or.inr (Or.inr ⟨e, Finset.mem_union_right _ he, h⟩)
    · rw [List.map_cons, List.sum_cons]
      have h1 := TO_dimret I.f hmono hsub (verts v P1) (hX'.trans hXZ)
      unfold fX at hval
      have hiR : (0 : ℝ) ≤ i := by positivity
      rw [Finset.union_comm X (verts v T1)] at hsum
      have h3 : (i : ℝ) * ((I.f (verts v P1 ∪ X) : ℝ) - I.f X) ≤ 0 + (i : ℝ) * ((I.f (verts v P1 ∪ X) : ℝ) - I.f X) := by simp
      linarith

end RunPlanApprox

end TreeOrient.RecGreedy


namespace TreeOrient.RecGreedy

open Relation

section RGApprox
variable {n : ℕ}

theorem TO_card_Y {r : Fin n} {A : Edges n} (hA : IsArbo r A) {Y : Finset (Fin n)}
    (hY : Y ⊆ verts r A) : (Y.erase r).card ≤ A.card := by
  classical
  have hsub : Y.erase r ⊆ A.image Prod.snd := by
    intro y hy
    obtain ⟨hyr, hyY⟩ := Finset.mem_erase.1 hy
    rcases ReflTransGen.cases_tail (hA.2.2 y (hY hyY)) with h | ⟨p, -, hp⟩
    · exact absurd h hyr
    · exact Finset.mem_image.2 ⟨(p, y), hp, rfl⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem TO_single_arbo {r : Fin n} {e : Fin n × Fin n} (hA : IsArbo r {e}) :
    e.1 = r ∧ e.2 ≠ r := by
  refine ⟨?_, hA.1 e (Finset.mem_singleton_self e)⟩
  rcases ReflTransGen.cases_tail (hA.2.2 e.1 (TO_fst_mem_verts (Finset.mem_singleton_self e)))
    with h | ⟨p, -, hp⟩
  · exact h
  · rw [Finset.mem_singleton] at hp
    have h2 : e.2 = e.1 := by
      have := congrArg Prod.snd hp; simp only at this; exact this.symm
    exfalso
    apply TO_no_self (r := r) (A := {e}) hA (v := e.1)
    have : e = (e.1, e.1) := Prod.ext rfl h2
    rw [← this]; exact Finset.mem_singleton_self e

theorem TO_edgeCandidates_mem {A : Edges n} {q : ℕ} (hq : A.card ≤ q) :
    A ∈ edgeCandidates n q := by
  unfold edgeCandidates
  refine List.mem_flatMap.2 ⟨A.card, List.mem_range.2 (by omega), ?_⟩
  refine List.mem_map.2 ⟨fun i => (A.equivFin.symm i : Fin n × Fin n), by simp, ?_⟩
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩; exact (A.equivFin.symm i).2
  · intro hx; exact ⟨A.equivFin ⟨x, hx⟩, by simp⟩

theorem TO_capImp_one_le (s i : ℕ) : (1 : ℝ) ≤ capImp s i := by
  unfold capImp; exact one_le_pow₀ (by norm_num)

theorem TO_rg_approx_base (I : Inst n) (hmono : IsMonotone I.f) (s : ℕ) (hs : 1 ≤ s)
    (mode : Mode) : TOapprox I mode (rg I s mode (0 + 1)) (capImp s (0 + 1)) (0 + 1) := by
  intro r Y₀ B X A hcomp hmode
  obtain ⟨hA, hY, hcard, hcost⟩ := hcomp
  have hYc := TO_card_Y hA hY
  have hcap : ¬ capImp s (0 + 1) < ((Y₀.erase r).card : ℝ) := by
    have : ((Y₀.erase r).card : ℝ) ≤ A.card := by exact_mod_cast hYc
    linarith
  simp only [Nat.cast_add, Nat.cast_zero, zero_add, Nat.cast_one, one_mul]
  by_cases hs1 : s = 1
  · subst hs1
    rw [TO_rg_one_eq I mode r Y₀ B X hcap, TO_rgBasic_eq, Finset.erase_idem, if_neg hcap]
    have hA1 : A.card ≤ 1 := by
      have : (A.card : ℝ) < 2 := by
        have : capImp 1 (0 + 1) = 3 / 2 := by unfold capImp; norm_num
        linarith
      have : A.card < 2 := by exact_mod_cast this
      omega
    rcases Nat.lt_or_ge A.card 1 with h0 | h1
    · have hAe : A = ∅ := Finset.card_eq_zero.1 (by omega)
      subst hAe
      have hYe : Y₀.erase r = ∅ := by
        have := hYc; simp at this; exact this
      rw [if_pos hYe]
      obtain ⟨-, hs2, -⟩ := TO_cb_fold_spec I.f X r _ (some ∅)
      obtain ⟨T', hT', hle⟩ := hs2 ∅ rfl
      exact ⟨T', hT', hle⟩
    · obtain ⟨e, rfl⟩ := Finset.card_eq_one.1 (by omega : A.card = 1)
      obtain ⟨he1, he2⟩ := TO_single_arbo hA
      obtain ⟨u, v⟩ := e
      simp only at he1 he2
      subst he1
      have hcv : I.c u v ≤ B := by rw [TO_cost_single] at hcost; exact hcost
      by_cases hYe : Y₀.erase u = ∅
      · rw [if_pos hYe]
        obtain ⟨-, -, hs3⟩ := TO_cb_fold_spec I.f X u _ (some ∅)
        refine hs3 {(u, v)} ?_
        simp only [List.mem_filterMap, List.mem_finRange, true_and]
        refine ⟨v, ?_⟩
        have : ¬ ((decide (v = u) || decide (B < I.c u v)) = true) := by
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
          exact ⟨he2, by omega⟩
        rw [if_neg this]
      · rw [if_neg hYe]
        have hYv : Y₀.erase u = {v} := by
          apply Finset.eq_singleton_iff_unique_mem.2
          obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.2 hYe
          have hyv : ∀ y ∈ Y₀.erase u, y = v := by
            intro y hy
            obtain ⟨hyu, hyY⟩ := Finset.mem_erase.1 hy
            rcases TO_mem_verts.1 (hY hyY) with h | ⟨e, he, h⟩
            · exact absurd h hyu
            · rw [Finset.mem_singleton] at he; subst he
              rcases h with h | h
              · exact absurd h.symm hyu
              · exact h.symm
          refine ⟨?_, hyv⟩
          have := hyv y hy; subst this; exact hy
        rw [hYv, Finset.toList_singleton]
        simp only [hcv, if_true]
        exact ⟨_, rfl, le_rfl⟩
  · classical
    rw [TO_rg_base_eq I s mode r Y₀ B X hs1 hcap]
    obtain ⟨-, -, hs3⟩ := TO_fold_best_spec I.f X r
      (fun T => IsArbo r T ∧ Y₀.erase r ⊆ verts r T ∧ cost I.c T ≤ B) _
      (fun o T hT => if_pos hT) (fun o T hT => if_neg hT) _ _
    refine hs3 A (TO_edgeCandidates_mem ?_) ⟨hA, (Finset.erase_subset r Y₀).trans hY, hcost⟩
    apply Nat.le_floor
    have : capImp s (0 + 1) = capImp s 1 := rfl
    rw [← this]; exact hcard

theorem TO_rg_approx (I : Inst n) (hmono : IsMonotone I.f)
    (hsub : NonmonotoneSubmod.Shared.Submodular (fun S => (I.f S : ℝ))) (s : ℕ) (hs : 1 ≤ s)
    (mode : Mode) : ∀ i, TOapprox I mode (rg I s mode (i + 1)) (capImp s (i + 1)) (i + 1)
  | 0 => TO_rg_approx_base I hmono s hs mode
  | i + 1 => by
    have ih := TO_rg_approx I hmono hsub s hs mode i
    intro r Y₀ B X A hcomp hmode
    obtain ⟨hA, hY, hcard, hcost⟩ := hcomp
    have hYc := TO_card_Y hA hY
    have hcap : ¬ capImp s (i + 1 + 1) < ((Y₀.erase r).card : ℝ) := by
      have : ((Y₀.erase r).card : ℝ) ≤ A.card := by exact_mod_cast hYc
      linarith
    rw [TO_rg_succ_eq I s mode (i + 1) r Y₀ B X (by omega) hcap]
    set K := capImp s (i + 1) with hKdef
    have hK : 1 ≤ K := TO_capImp_one_le s (i + 1)
    have hcard' : (A.card : ℝ) ≤ (3 / 2 : ℝ) ^ s * K := by
      have : capImp s (i + 1 + 1) = (3 / 2 : ℝ) ^ s * K := by
        rw [hKdef]; unfold capImp; rw [← pow_add]; congr 1; ring
      rw [← this]; exact hcard
    obtain ⟨L, hLp, hLa, hLc, hLv⟩ := TO_decomp I.c s r (Y₀.erase r) A K hK hA
      ((Finset.erase_subset r Y₀).trans hY) hcard'
    set plan := L.map (fun x => (x.1, x.2.1)) with hplan
    obtain ⟨hp1, hp2, -, hp4⟩ := TO_leafPlans_props s r _ plan hLp
    have hLne : L ≠ [] := by
      intro h; rw [hplan, h] at hp4; simp at hp4; exact absurd hp4.symm (by positivity)
    obtain ⟨T, hT, D, Z, hTD, hXZ, hZ, hsum⟩ := TO_runPlan_approx I hmono hsub mode
      (rg I s mode (i + 1)) K (i + 1) (by omega) ih L hLne X B ∅
      (fun x hx => ⟨(hLa x hx).1, (hLa x hx).2.1, (hLa x hx).2.2.1⟩) (hLc.trans hcost)
      (fun x hx => TO_modeOK_mono mode I.f hmono hsub le_rfl (hLa x hx).2.2.2 hmode)
    obtain ⟨-, -, h6, -⟩ := TO_runPlan_sound I mode (rg I s mode (i + 1))
      (TO_rg_sound I s mode (i + 1)) r B plan {r} X B ∅ hp1 (by simp [TO_root_mem_verts])
      (TO_rc_empty r) (by simp [cost]) T hT
    have hroots : ∀ x ∈ L, x.1 ∈ verts r T := by
      intro x hx
      have := TO_rootsOK_roots plan {r} hp1 (x.1, x.2.1)
        (List.mem_map.2 ⟨x, hx, rfl⟩)
      exact h6 this
    have hZT : Z ⊆ verts r T ∪ X := by
      intro w hw
      rcases hZ w hw with h | ⟨x, hx, h⟩ | ⟨e, he, h⟩
      · exact Finset.mem_union_right _ h
      · subst h; exact Finset.mem_union_left _ (hroots x hx)
      · refine Finset.mem_union_left _ (TO_mem_verts.2 (Or.inr ⟨e, ?_, h⟩))
        rw [hTD]; exact Finset.mem_union_right _ he
    -- the value chain
    set F : Finset (Fin n) → ℝ := fun S => (I.f S : ℝ) with hF
    have hcov : verts r A ∪ X ⊆ Z ∪ TObig (fun x : Fin n × Finset (Fin n) × Edges n =>
        verts x.1 x.2.2) L := by
      intro w hw
      rcases Finset.mem_union.1 hw with h | h
      · obtain ⟨x, hx, hw'⟩ := hLv w h
        exact Finset.mem_union_right _ ((TO_mem_big _ L w).2 ⟨x, hx, hw'⟩)
      · exact Finset.mem_union_left _ (hXZ h)
    have h1 := TO_mono_real I.f hmono hcov
    have h2 := TO_union_bound I.f hmono hsub
      (fun x : Fin n × Finset (Fin n) × Edges n => verts x.1 x.2.2) L Z
    have h3 := TO_mono_real I.f hmono hZT
    have h4 := TO_mono_real I.f hmono hXZ
    have hpos : (0 : ℝ) ≤ (i : ℝ) + 1 + 1 := by positivity
    have h5 : ((i : ℝ) + 1 + 1) * ((I.f Z : ℝ) - I.f X) ≤
        ((i : ℝ) + 1 + 1) * ((I.f (verts r T ∪ X) : ℝ) - I.f X) :=
      mul_le_mul_of_nonneg_left (by linarith) hpos
    have hval : fX I.f X r A ≤ ((i + 1 + 1 : ℕ) : ℝ) * fX I.f X r T := by
      unfold fX
      push_cast at hsum ⊢
      linarith
    obtain ⟨-, -, hs3⟩ := TO_cb_fold_spec I.f X r
      ((leafPlans s r (Y₀.erase r)).flatMap
          (fun p => (runPlan I mode (rg I s mode (i + 1)) p X B ∅).1))
      (if Y₀.erase r = ∅ then some ∅ else none)
    obtain ⟨T', hT', hle⟩ := hs3 T (List.mem_flatMap.2 ⟨plan, hLp, hT⟩)
    refine ⟨T', hT', hval.trans ?_⟩
    exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- Combined guarantee: the grouped recursive greedy returns a feasible solution containing a
spanning arborescence, with the `1/i` value guarantee. -/
theorem TO_rg_main (I : Inst n) (hmono : IsMonotone I.f)
    (hsub : NonmonotoneSubmod.Shared.Submodular (fun S => (I.f S : ℝ))) (s : ℕ) (hs : 1 ≤ s)
    (mode : Mode) (i : ℕ) (hi : 1 ≤ i) (r : Fin n) (Y X : Finset (Fin n)) (B : ℕ)
    (A : Edges n) (hA : Compatible I.c r Y B (capImp s i) A)
    (hmode : TOmodeOK mode I.f X r A) :
    ∃ T, (rg I s mode i r Y B X).1 = some T ∧
      Feasible I.c r Y B T ∧
      (∃ A' : Edges n, A' ⊆ T ∧ IsArbo r A' ∧ verts r A' = verts r T) ∧
      fX I.f X r A ≤ (i : ℝ) * fX I.f X r T := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨T, hT, hval⟩ := TO_rg_approx I hmono hsub s hs mode j r Y B X A hA hmode
  have hF := TO_rg_sound I s mode (j + 1) r Y B X T hT
  obtain ⟨A', h1, h2, h3⟩ := TO_extract hF.1
  exact ⟨T, hT, hF, ⟨A', h1, h2, h3⟩, hval⟩

end RGApprox

end TreeOrient.RecGreedy

open TreeOrient.RecGreedy

theorem solution {n : ℕ} (I : Inst n) (r : Fin n)
    (Y X : Finset (Fin n)) (B s i : ℕ) (A : Edges n)
    (hmono : IsMonotone I.f)
    (hsub : NonmonotoneSubmod.Shared.Submodular (fun S => (I.f S : ℝ)))
    (hs : 1 ≤ s) (hi : 1 ≤ i)
    (hA : Compatible I.c r Y B (capImp s i) A) :
    ∃ T, (rg I s .enum i r Y B X).1 = some T ∧
      Feasible I.c r Y B T ∧
      (∃ A' : Edges n, A' ⊆ T ∧ IsArbo r A' ∧ verts r A' = verts r T) ∧
      fX I.f X r A ≤ (i : ℝ) * fX I.f X r T :=
  TO_rg_main I hmono hsub s hs .enum i hi r Y X B A hA trivial
