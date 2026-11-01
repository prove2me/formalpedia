-- Prove2me | solution 1 for TreeOrient.RecGreedy.fact_2_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T05:26:06.341272+00:00
-- url     : https://prove2.me/submissions/b8091796-9da8-4130-9e1c-75013ce9cf94

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

open TreeOrient.RecGreedy

theorem solution {n : ℕ} (r : Fin n) (A : Edges n)
    (hA : IsArbo r A) (h2 : 2 ≤ A.card) :
    ∃ v ∈ verts r A, ∃ A₁ A₂ : Edges n,
      Disjoint A₁ A₂ ∧ A₁ ∪ A₂ = A ∧ IsArbo r A₁ ∧ v ∈ verts r A₁ ∧
      IsArbo v A₂ ∧ 3 * A₁.card ≤ 2 * A.card ∧ 3 * A₂.card ≤ 2 * A.card :=
  TO_fact_2_2 A hA h2
