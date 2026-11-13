-- Prove2me | solution 1 for RepellingPairs.claim_8_path_switching
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T20:07:21.133835+00:00
-- url     : https://prove2.me/submissions/885e393a-e7ef-45a3-999c-abb973a70303

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_OSInstance
import Definitions.Def_RepellingPairs_PathStructure
import Definitions.Def_RepellingPairs_CyclicallyOrdered
import Theorems.Thm_RepellingPairs_walks_meet_of_cyclicallyOrdered
universe u v

section
set_option autoImplicit false

namespace RepellingPairs.Dev.Claim8


open RepellingPairs.Multigraph

variable {V : Type u} {E : Type v} {G : RepellingPairs.Multigraph V E}

theorem start_mem {a b : V} (p : G.Walk a b) : a ∈ p.support := by
  cases p <;> simp [Walk.support]

theorem end_mem {a b : V} (p : G.Walk a b) : b ∈ p.support := by
  induction p with
  | nil v => simp [Walk.support]
  | cons e h p ih => simp [Walk.support, ih]

theorem mem_append {a b c x : V} (p : G.Walk a b) (q : G.Walk b c) :
    x ∈ (p.append q).support ↔ x ∈ p.support ∨ x ∈ q.support := by
  induction p with
  | nil v =>
    simp only [Walk.append, Walk.support, List.mem_singleton]
    constructor
    · exact Or.inr
    · rintro (rfl | h)
      · exact start_mem q
      · exact h
  | cons e h p ih =>
    simp only [Walk.append, Walk.support, List.mem_cons]
    rw [ih q]
    tauto

theorem nodup_right {a b c : V} (p : G.Walk a b) (q : G.Walk b c)
    (hn : (p.append q).support.Nodup) : q.support.Nodup := by
  induction p with
  | nil v => exact hn
  | cons e h p ih =>
    simp only [Walk.append, Walk.support, List.nodup_cons] at hn
    exact ih q hn.2

theorem nodup_left {a b c : V} (p : G.Walk a b) (q : G.Walk b c)
    (hn : (p.append q).support.Nodup) : p.support.Nodup := by
  induction p with
  | nil v => simp [Walk.support]
  | cons e h p ih =>
    simp only [Walk.append, Walk.support, List.nodup_cons] at hn ⊢
    exact ⟨fun hm => hn.1 ((mem_append p q).2 (Or.inl hm)), ih q hn.2⟩

theorem mem_both {a b c x : V} (p : G.Walk a b) (q : G.Walk b c)
    (hn : (p.append q).support.Nodup) (hp : x ∈ p.support) (hq : x ∈ q.support) : x = b := by
  induction p with
  | nil v => simpa [Walk.support] using hp
  | cons e h p ih =>
    simp only [Walk.append, Walk.support, List.nodup_cons] at hn
    simp only [Walk.support, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact absurd ((mem_append p q).2 (Or.inr hq)) hn.1
    · exact ih q hn.2 hp hq

theorem closed_nil {a : V} (p : G.Walk a a) (hn : p.support.Nodup) : p = Walk.nil a := by
  cases p with
  | nil => rfl
  | cons e h q =>
    simp only [Walk.support, List.nodup_cons] at hn
    exact absurd (end_mem q) hn.1

theorem split {a b x : V} (p : G.Walk a b) (hx : x ∈ p.support) :
    ∃ (p₁ : G.Walk a x) (p₂ : G.Walk x b), p = p₁.append p₂ := by
  induction p with
  | nil v =>
    simp only [Walk.support, List.mem_singleton] at hx
    subst hx
    exact ⟨Walk.nil _, Walk.nil _, rfl⟩
  | cons e h p ih =>
    simp only [Walk.support, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨Walk.nil _, _, rfl⟩
    · obtain ⟨p₁, p₂, rfl⟩ := ih hx
      exact ⟨Walk.cons e h p₁, p₂, rfl⟩

theorem append_assoc {a b c d : V} (p : G.Walk a b) (q : G.Walk b c) (r : G.Walk c d) :
    (p.append q).append r = p.append (q.append r) := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [Walk.append, ih]

theorem append_nil {a b : V} (p : G.Walk a b) : p.append (Walk.nil b) = p := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [Walk.append, ih]

theorem append_cancel {a b c : V} (p₁ q₁ : G.Walk a b) (p₂ q₂ : G.Walk b c)
    (h : p₁.append p₂ = q₁.append q₂) (hn : (p₁.append p₂).support.Nodup) :
    p₁ = q₁ ∧ p₂ = q₂ := by
  induction p₁ with
  | nil v =>
    have hq : q₁ = Walk.nil v := closed_nil q₁ (nodup_left q₁ q₂ (h ▸ hn))
    subst hq
    exact ⟨rfl, h⟩
  | cons e he p ih =>
    cases q₁ with
    | nil w =>
      have := closed_nil _ (nodup_left _ _ hn)
      cases this
    | cons e' he' q =>
      simp only [Walk.append] at h
      injection h with h1 h2 h3 h4 h5
      subst h2
      subst h4
      have h3' := eq_of_heq h5
      simp only [Walk.append, Walk.support, List.nodup_cons] at hn
      obtain ⟨r1, r2⟩ := ih q p₂ q₂ h3' hn.2
      subst r1
      exact ⟨rfl, r2⟩

theorem support_append {a b c : V} (p : G.Walk a b) (q : G.Walk b c) :
    (p.append q).support = p.support ++ q.support.tail := by
  induction p with
  | nil v => cases q <;> rfl
  | cons e h p ih => simp [Walk.append, Walk.support, ih]

theorem support_reverse {a b : V} (p : G.Walk a b) : p.reverse.support = p.support.reverse := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp [Walk.reverse, support_append, ih, Walk.support]

theorem mem_reverse {a b x : V} (p : G.Walk a b) : x ∈ p.reverse.support ↔ x ∈ p.support := by
  rw [support_reverse, List.mem_reverse]

theorem reverse_append {a b c : V} (p : G.Walk a b) (q : G.Walk b c) :
    (p.append q).reverse = q.reverse.append p.reverse := by
  induction p with
  | nil => simp [Walk.append, Walk.reverse, append_nil]
  | cons e h p ih => simp [Walk.append, Walk.reverse, ih, append_assoc]

theorem reverse_reverse {a b : V} (p : G.Walk a b) : p.reverse.reverse = p := by
  induction p with
  | nil => rfl
  | cons e h p ih =>
    simp only [Walk.reverse, reverse_append, ih]
    rfl

theorem prefix_meet {a b c : V} (p : G.Walk a b) (q : G.Walk a c)
    (hp : p.support.Nodup) (hq : q.support.Nodup) (hm : p.MeetInSubpath q) :
    ∃ (w : V) (z : G.Walk a w) (p' : G.Walk w b) (q' : G.Walk w c),
      p = z.append p' ∧ q = z.append q' ∧ ∀ v, v ∈ p'.support → v ∈ q'.support → v = w := by
  rcases hm with hd | ⟨x, y, r, hI, ⟨p₁, p₂, hp'⟩, hq'⟩
  · exact absurd (start_mem q) (hd a (start_mem p))
  · have har : a ∈ r.support := (hI.1 a).2 ⟨start_mem p, start_mem q⟩
    subst hp'
    have hax : a = x := mem_both p₁ _ hp (start_mem p₁) ((mem_append r p₂).2 (Or.inl har))
    subst hax
    have h1 := closed_nil p₁ (nodup_left _ _ hp)
    subst h1
    have hrp : (r.append p₂).support.Nodup := hp
    rcases hq' with ⟨q₁, q₂, hq'⟩ | ⟨q₁, q₂, hq'⟩
    · subst hq'
      have h2 := closed_nil q₁ (nodup_left _ _ hq)
      subst h2
      refine ⟨y, r, p₂, q₂, rfl, rfl, fun v hv1 hv2 => ?_⟩
      have hvr : v ∈ r.support :=
        (hI.1 v).2 ⟨(mem_append r p₂).2 (Or.inr hv1), (mem_append r q₂).2 (Or.inr hv2)⟩
      exact mem_both r p₂ hrp hvr hv1
    · subst hq'
      have hay := mem_both q₁ _ hq (start_mem q₁)
        ((mem_append _ q₂).2 (Or.inl ((mem_reverse r).2 har)))
      subst hay
      have h3 := closed_nil r (nodup_left _ _ hrp)
      subst h3
      have h2 := closed_nil q₁ (nodup_left _ _ hq)
      subst h2
      refine ⟨_, Walk.nil _, p₂, q₂, rfl, rfl, fun v hv1 hv2 => ?_⟩
      have hvr := (hI.1 v).2 ⟨hv1, hv2⟩
      simpa [Walk.support] using hvr

theorem suffix_meet {a b c : V} (p : G.Walk a b) (q : G.Walk c b)
    (hp : p.support.Nodup) (hq : q.support.Nodup) (hm : p.reverse.MeetInSubpath q.reverse) :
    ∃ (w : V) (s : G.Walk w b) (p' : G.Walk a w) (q' : G.Walk c w),
      p = p'.append s ∧ q = q'.append s ∧ ∀ v, v ∈ p'.support → v ∈ q'.support → v = w := by
  obtain ⟨w, z, p', q', h1, h2, h3⟩ := prefix_meet p.reverse q.reverse
    (by rw [support_reverse]; exact List.nodup_reverse.2 hp)
    (by rw [support_reverse]; exact List.nodup_reverse.2 hq) hm
  refine ⟨w, z.reverse, p'.reverse, q'.reverse, ?_, ?_, ?_⟩
  · calc p = p.reverse.reverse := (reverse_reverse p).symm
      _ = _ := by rw [h1, reverse_append]
  · calc q = q.reverse.reverse := (reverse_reverse q).symm
      _ = _ := by rw [h2, reverse_append]
  · intro v hv1 hv2
    exact h3 v ((mem_reverse _).1 hv1) ((mem_reverse _).1 hv2)

theorem switch {A B C D x y u w : V} (Pa : G.Walk A x) (r : G.Walk x y) (Pb : G.Walk y B)
    (Qd : G.Walk D x) (Qc : G.Walk y C) (Z : G.Walk A C)
    (hX : (Pa.append (r.append Pb)).support.Nodup)
    (hY : (Qd.append (r.append Qc)).support.Nodup) (hZ : Z.support.Nodup)
    (z₁ : G.Walk A u) (z' : G.Walk u C) (x' : G.Walk u B)
    (hZ1 : Z = z₁.append z') (hX1 : Pa.append (r.append Pb) = z₁.append x')
    (hu : ∀ v, v ∈ z'.support → v ∈ x'.support → v = u)
    (s : G.Walk w C) (z'' : G.Walk A w) (y'' : G.Walk D w)
    (hZ2 : Z = z''.append s) (hY2 : Qd.append (r.append Qc) = y''.append s)
    (hw : ∀ v, v ∈ z''.support → v ∈ y''.support → v = w)
    (hcross : ∀ (p : G.Walk A C) (q : G.Walk D B), ∃ v, v ∈ p.support ∧ v ∈ q.support) :
    Z = Pa.append (r.append Qc) := by
  have hZX : ∀ v, v ∈ Z.support → v ∈ (Pa.append (r.append Pb)).support → v ∈ z₁.support := by
    intro v h1 h2
    rw [hZ1, mem_append] at h1
    rw [hX1, mem_append] at h2
    rcases h1 with h1 | h1
    · exact h1
    rcases h2 with h2 | h2
    · exact h2
    rw [hu v h1 h2]; exact end_mem z₁
  have hZY : ∀ v, v ∈ Z.support → v ∈ (Qd.append (r.append Qc)).support → v ∈ s.support := by
    intro v h1 h2
    rw [hZ2, mem_append] at h1
    rw [hY2, mem_append] at h2
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · rw [hw v h1 h2]; exact start_mem s
      · exact h2
    · exact h1
  have hyX : y ∈ (Pa.append (r.append Pb)).support :=
    (mem_append _ _).2 (Or.inr ((mem_append _ _).2 (Or.inl (end_mem r))))
  have hyY : y ∈ (Qd.append (r.append Qc)).support :=
    (mem_append _ _).2 (Or.inr ((mem_append _ _).2 (Or.inl (end_mem r))))
  have hyZ : y ∈ Z.support := by
    by_contra hy
    have hy1 : y ∉ z₁.support := fun h => hy (by rw [hZ1, mem_append]; exact Or.inl h)
    have hy2 : y ∉ s.support := fun h => hy (by rw [hZ2, mem_append]; exact Or.inr h)
    have h1 : ∀ v, v ∈ z₁.support → v ∉ Pb.support := by
      intro v hv1 hv2
      obtain ⟨z₁a, z₁b, rfl⟩ := split z₁ hv1
      obtain ⟨Pb1, Pb2, rfl⟩ := split Pb hv2
      have e1 : (Pa.append (r.append Pb1)).append Pb2 = z₁a.append (z₁b.append x') := by
        simpa only [append_assoc] using hX1
      have c := append_cancel _ _ _ _ e1 (by simpa only [append_assoc] using hX)
      apply hy1
      rw [mem_append, ← c.1, mem_append, mem_append]
      exact Or.inl (Or.inr (Or.inl (end_mem r)))
    have h2 : ∀ v, v ∈ s.support → v ∉ (Qd.append r).support := by
      intro v hv1 hv2
      obtain ⟨s1, s2, rfl⟩ := split s hv1
      obtain ⟨m1, m2, hm⟩ := split (Qd.append r) hv2
      have e1 : m1.append (m2.append Qc) = (y''.append s1).append s2 := by
        rw [← append_assoc, ← hm, append_assoc, hY2, append_assoc]
      have c := append_cancel _ _ _ _ e1
        (by rw [← append_assoc, ← hm, append_assoc]; exact hY)
      apply hy2
      rw [mem_append, ← c.2, mem_append]
      exact Or.inr (Or.inl (end_mem m2))
    obtain ⟨v, hv1, hv2⟩ := hcross Z (Qd.append (r.append Pb))
    rw [mem_append, mem_append] at hv2
    rcases hv2 with hv2 | hv2 | hv2
    · refine h2 v (hZY v hv1 ?_) ((mem_append _ _).2 (Or.inl hv2))
      exact (mem_append _ _).2 (Or.inl hv2)
    · refine h2 v (hZY v hv1 ?_) ((mem_append _ _).2 (Or.inr hv2))
      exact (mem_append _ _).2 (Or.inr ((mem_append _ _).2 (Or.inl hv2)))
    · refine h1 v (hZX v hv1 ?_) hv2
      exact (mem_append _ _).2 (Or.inr ((mem_append _ _).2 (Or.inr hv2)))
  have hy1 : y ∈ z₁.support := hZX y hyZ hyX
  have hy2 : y ∈ s.support := hZY y hyZ hyY
  obtain ⟨Z1, t, rfl⟩ := split z₁ hy1
  obtain ⟨t', Z2, rfl⟩ := split s hy2
  have c1 := append_cancel (Pa.append r) Z1 Pb (t.append x')
    (by rw [append_assoc, hX1, append_assoc]) (by rw [append_assoc]; exact hX)
  have c2 := append_cancel (Qd.append r) (y''.append t') Qc Z2
    (by rw [append_assoc, hY2, append_assoc]) (by rw [append_assoc]; exact hY)
  have c3 := append_cancel Z1 (z''.append t') (t.append z') Z2
    (by rw [← append_assoc, ← hZ1, hZ2, append_assoc])
    (by rw [← append_assoc, ← hZ1]; exact hZ)
  rw [hZ1, append_assoc, ← c1.1, c3.2, ← c2.2, append_assoc]

theorem step1 {A B C D x y : V} (Pa : G.Walk A x) (r : G.Walk x y) (Pb : G.Walk y B)
    (Qd : G.Walk D y) (Qc : G.Walk x C)
    (hX : (Pa.append (r.append Pb)).support.Nodup)
    (hY : (Qd.append (r.reverse.append Qc)).support.Nodup)
    (hI : ∀ v, v ∈ (Pa.append (r.append Pb)).support →
      v ∈ (Qd.append (r.reverse.append Qc)).support → v ∈ r.support)
    (hcross : ∀ (p : G.Walk A C) (q : G.Walk B D), ∃ v, v ∈ p.support ∧ v ∈ q.support) :
    x = y := by
  obtain ⟨v, hv1, hv2⟩ := hcross (Pa.append Qc) (Pb.reverse.append Qd.reverse)
  rw [mem_append] at hv1
  rw [mem_append, mem_reverse, mem_reverse] at hv2
  have hrP : (r.append Pb).support.Nodup := nodup_right _ _ hX
  have hrQ : (r.reverse.append Qc).support.Nodup := nodup_right _ _ hY
  rcases hv1 with h1 | h1 <;> rcases hv2 with h2 | h2
  · have e1 : v = x := mem_both Pa _ hX h1 ((mem_append _ _).2 (Or.inr h2))
    exact mem_both r Pb hrP (start_mem r) (e1 ▸ h2)
  · have hvr : v ∈ r.support := hI v ((mem_append _ _).2 (Or.inl h1))
      ((mem_append _ _).2 (Or.inl h2))
    have e1 : v = x := mem_both Pa _ hX h1 ((mem_append _ _).2 (Or.inl hvr))
    have e2 : v = y := mem_both Qd _ hY h2 ((mem_append _ _).2 (Or.inl ((mem_reverse r).2 hvr)))
    exact e1.symm.trans e2
  · have hvr : v ∈ r.support :=
      hI v ((mem_append _ _).2 (Or.inr ((mem_append _ _).2 (Or.inr h2))))
        ((mem_append _ _).2 (Or.inr ((mem_append _ _).2 (Or.inr h1))))
    have e1 : v = y := mem_both r Pb hrP hvr h2
    have e2 : v = x := mem_both r.reverse Qc hrQ ((mem_reverse r).2 hvr) h1
    exact e2.symm.trans e1
  · have e1 : v = y := mem_both Qd _ hY h2 ((mem_append _ _).2 (Or.inr h1))
    exact (mem_both r.reverse Qc hrQ (start_mem r.reverse) (e1 ▸ h1)).symm

end RepellingPairs.Dev.Claim8

namespace RepellingPairs


open RepellingPairs.Dev.Claim8 RepellingPairs.Multigraph

theorem chk_claim_8_path_switching {V : Type u} {E : Type v} {k : ℕ} [Fintype V] [Fintype E]
    (G : OSInstance V E k) (P : PathStructure G) {a b c d : Fin k}
    (horder : CyclicallyOrdered a b c d)
    (hint : ¬ (P.path a b).1.VertexDisjoint (P.path d c).1) :
    ∃ (x y : V) (R : G.graph.Walk x y)
      (Pa : G.graph.Walk (G.term a) x) (Pb : G.graph.Walk y (G.term b))
      (Qd : G.graph.Walk (G.term d) x) (Qc : G.graph.Walk y (G.term c)),
      (P.path a b).1 = Pa.append (R.append Pb) ∧
      (P.path d c).1 = Qd.append (R.append Qc) ∧
      Multigraph.Walk.IsIntersection (P.path a b).1 (P.path d c).1 R ∧
      (P.path a c).1 = Pa.append (R.append Qc) ∧
      (P.path d b).1 = Qd.append (R.append Pb) := by
  have hcross0 : ∀ (p : G.graph.Walk (G.term a) (G.term c))
      (q : G.graph.Walk (G.term b) (G.term d)), ∃ v, v ∈ p.support ∧ v ∈ q.support :=
    fun p q => walks_meet_of_cyclicallyOrdered G horder p q
  have hcross1 : ∀ (p : G.graph.Walk (G.term a) (G.term c))
      (q : G.graph.Walk (G.term d) (G.term b)), ∃ v, v ∈ p.support ∧ v ∈ q.support := by
    intro p q
    obtain ⟨v, h1, h2⟩ := walks_meet_of_cyclicallyOrdered G horder p q.reverse
    exact ⟨v, h1, (mem_reverse q).1 h2⟩
  have hcross2 : ∀ (p : G.graph.Walk (G.term d) (G.term b))
      (q : G.graph.Walk (G.term a) (G.term c)), ∃ v, v ∈ p.support ∧ v ∈ q.support := by
    intro p q
    obtain ⟨v, h1, h2⟩ := walks_meet_of_cyclicallyOrdered G horder q p.reverse
    exact ⟨v, (mem_reverse p).1 h2, h1⟩
  have hab : (P.path a b).1.support.Nodup := (P.path a b).2
  have hdc : (P.path d c).1.support.Nodup := (P.path d c).2
  have hac : (P.path a c).1.support.Nodup := (P.path a c).2
  have hdb : (P.path d b).1.support.Nodup := (P.path d b).2
  rcases P.meet a b d c with hd | ⟨x, y, r, hI, ⟨Pa, Pb, hPab⟩, hdir⟩
  · exact absurd hd hint
  have hab' : (Pa.append (r.append Pb)).support.Nodup := hPab ▸ hab
  have hdir' : ∃ (Qd : G.graph.Walk (G.term d) x) (Qc : G.graph.Walk y (G.term c)),
      (P.path d c).1 = Qd.append (r.append Qc) := by
    rcases hdir with ⟨Qd, Qc, h⟩ | ⟨Qd, Qc, h⟩
    · exact ⟨Qd, Qc, h⟩
    · have hdc' : (Qd.append (r.reverse.append Qc)).support.Nodup := h ▸ hdc
      have hxy : x = y := step1 Pa r Pb Qd Qc hab' hdc'
        (fun v h1 h2 => (hI.1 v).2 ⟨hPab ▸ h1, h ▸ h2⟩) hcross0
      subst hxy
      have hr := closed_nil r (nodup_left _ _ (nodup_right _ _ hab'))
      subst hr
      exact ⟨Qd, Qc, h⟩
  obtain ⟨Qd, Qc, hPdc⟩ := hdir'
  have hdc' : (Qd.append (r.append Qc)).support.Nodup := hPdc ▸ hdc
  refine ⟨x, y, r, Pa, Pb, Qd, Qc, hPab, hPdc, hI, ?_, ?_⟩
  · obtain ⟨u, z₁, z', x', h1, h2, h3⟩ :=
      prefix_meet (P.path a c).1 (P.path a b).1 hac hab (P.meet a c a b)
    have hm := P.meet c a c d
    rw [P.path_symm a c, P.path_symm d c] at hm
    obtain ⟨w, s, z'', y'', h4, h5, h6⟩ :=
      suffix_meet (P.path a c).1 (P.path d c).1 hac hdc hm
    exact switch Pa r Pb Qd Qc _ hab' hdc' hac z₁ z' x' h1 (hPab ▸ h2) h3 s z'' y'' h4
      (hPdc ▸ h5) h6 hcross1
  · obtain ⟨u, z₁, z', x', h1, h2, h3⟩ :=
      prefix_meet (P.path d b).1 (P.path d c).1 hdb hdc (P.meet d b d c)
    have hm := P.meet b d b a
    rw [P.path_symm d b, P.path_symm a b] at hm
    obtain ⟨w, s, z'', y'', h4, h5, h6⟩ :=
      suffix_meet (P.path d b).1 (P.path a b).1 hdb hab hm
    exact switch Qd r Qc Pa Pb _ hdc' hab' hdb z₁ z' x' h1 (hPdc ▸ h2) h3 s z'' y'' h4
      (hPab ▸ h5) h6 hcross2

end RepellingPairs
end

theorem solution : type_of% @RepellingPairs.chk_claim_8_path_switching := @RepellingPairs.chk_claim_8_path_switching
