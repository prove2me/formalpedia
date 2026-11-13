-- Prove2me | solution 1 for RepellingPairs.cost_inequality_of_trivial_pair
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T20:14:45.684923+00:00
-- url     : https://prove2.me/submissions/55ed0827-e4c2-4c72-b585-5c1cff1c77d6

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_OSInstance
import Definitions.Def_RepellingPairs_PathStructure
import Definitions.Def_RepellingPairs_IsMetric
import Definitions.Def_RepellingPairs_IsKalmanson
import Definitions.Def_RepellingPairs_TerminalPath
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_IntegralFlow
import Theorems.Thm_RepellingPairs_claim_9_flow_dominance
import Theorems.Thm_RepellingPairs_lemma_10_dominance_implies_uncrossing
import Theorems.Thm_RepellingPairs_config_eq_of_dist_eq
import Theorems.Thm_RepellingPairs_step_1_maximal_switching
universe u v

section
set_option autoImplicit false

namespace RepellingPairs.Dev.TrivLeaf


open RepellingPairs.Multigraph

section walks

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

theorem edges_append {u w x : V} (p : G.Walk u w) (q : G.Walk w x) :
    (p.append q).edges = p.edges ++ q.edges := by
  induction p with
  | nil v => simp [Walk.append, Walk.edges]
  | cons e h p ih => simp [Walk.append, Walk.edges, ih]

/-- the edges incident to `v` -/
noncomputable def incid [Fintype E] (G : RepellingPairs.Multigraph V E) (v : V) : Finset E := by
  classical exact Finset.univ.filter (fun e => v ∈ G.ends e)

theorem mem_incid [Fintype E] (v : V) (e : E) : e ∈ incid G v ↔ v ∈ G.ends e := by
  classical
  unfold incid
  simp

/-- number of edges of a list (with multiplicity) in `S` -/
def cv [DecidableEq E] (S : Finset E) (l : List E) : ℕ := ∑ e ∈ S, l.count e

theorem cv_nil [DecidableEq E] (S : Finset E) : cv S [] = 0 := by simp [cv]

theorem cv_cons [DecidableEq E] (S : Finset E) (a : E) (l : List E) :
    cv S (a :: l) = cv S l + (if a ∈ S then 1 else 0) := by
  unfold cv
  simp only [List.count_cons, Finset.sum_add_distrib, beq_iff_eq]
  rw [Finset.sum_ite_eq]

theorem cv_path [Fintype E] [DecidableEq E] [DecidableEq V] (v : V) {a b : V} (p : G.Walk a b)
    (hp : p.support.Nodup) :
    cv (incid G v) p.edges + (if a = v then 1 else 0) + (if b = v then 1 else 0) =
      2 * (if v ∈ p.support then 1 else 0) := by
  classical
  induction p with
  | nil w =>
    simp only [Walk.edges, cv_nil, Walk.support, List.mem_singleton]
    by_cases h : w = v
    · subst h; simp
    · simp [h, Ne.symm h]
  | cons e h p ih =>
    rename_i u m w
    simp only [Walk.support, List.nodup_cons] at hp
    have ih' := ih hp.2
    simp only [Walk.edges, cv_cons, Walk.support, List.mem_cons]
    have hmem : e ∈ incid G v ↔ v = u ∨ v = m := by
      rw [mem_incid, h, Sym2.mem_iff]
    have hm : m ∈ p.support := start_mem p
    have hw : w ∈ p.support := end_mem p
    by_cases h1 : v = u
    · subst h1
      have hm' : m ≠ v := fun hh => hp.1 (hh ▸ hm)
      have hw' : w ≠ v := fun hh => hp.1 (hh ▸ hw)
      simp only [hp.1, hm', hw', if_false, if_true, true_or] at ih' ⊢
      rw [if_pos (hmem.2 (Or.inl rfl))]
      omega
    · have hu : ¬ u = v := Ne.symm h1
      by_cases h3 : v = m
      · rw [if_pos (hmem.2 (Or.inr h3))]
        subst h3
        simp only [hu, h1, hm, if_true, if_false, or_true] at ih' ⊢
        omega
      · rw [if_neg (fun hh => (hmem.1 hh).elim h1 h3)]
        simp only [hu, h1, if_false, false_or, Ne.symm h3] at ih' ⊢
        omega

end walks

section os

variable {V : Type u} {E : Type v} {k : ℕ}

theorem term_inj (G : OSInstance V E k) : Function.Injective G.term := by
  intro i j h
  have h1 := G.pos_term i
  have h2 := G.pos_term j
  rw [h, h2] at h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h1
  have him := congrArg Complex.im hn
  simp at him
  have a1 := G.θ_nonneg i
  have a2 := G.θ_nonneg j
  have b1 := G.θ_lt_two_pi i
  have b2 := G.θ_lt_two_pi j
  have hpi := Real.pi_pos
  have hn1 : (n : ℝ) < 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  have hn2 : (-1 : ℝ) < n := by
    by_contra hc
    push Not at hc
    nlinarith
  have hn0 : n = 0 := by
    have : n < 1 := by exact_mod_cast hn1
    have : -1 < n := by exact_mod_cast hn2
    omega
  subst hn0
  simp at him
  exact G.θ_strictMono.injective him.symm

theorem split_count [DecidableEq E] {G : OSInstance V E k} (P : PathStructure G) (x y t : Fin k)
    (hv : G.term t ∈ (P.path x y).1.support) (e : E) :
    (P.path x y).1.edges.count e = (P.path x t).1.edges.count e + (P.path t y).1.edges.count e := by
  have nxt : (P.path x t).1.support.Nodup := (P.path x t).2
  have nxy : (P.path x y).1.support.Nodup := (P.path x y).2
  have nty : (P.path t y).1.support.Nodup := (P.path t y).2
  obtain ⟨w, z, p', q', h1, h2, h3⟩ := prefix_meet (P.path x t).1 (P.path x y).1 nxt nxy
    (P.meet x t x y)
  have hvz : G.term t ∈ z.support := by
    have : G.term t ∈ (z.append q').support := h2 ▸ hv
    rcases (mem_append z q').1 this with hh | hh
    · exact hh
    · rw [h3 _ (end_mem p') hh]; exact end_mem z
  have hvw : G.term t = w := mem_both z p' (h1 ▸ nxt) hvz (end_mem p')
  subst hvw
  have hp' := closed_nil p' (nodup_right z p' (h1 ▸ nxt))
  subst hp'
  rw [append_nil] at h1
  have hm := P.meet y x y t
  rw [P.path_symm x y, P.path_symm t y] at hm
  obtain ⟨w2, s, p'', q'', h4, h5, h6⟩ := suffix_meet (P.path x y).1 (P.path t y).1 nxy nty hm
  have hvs : G.term t ∈ s.support := by
    have : G.term t ∈ (p''.append s).support := h4 ▸ hv
    rcases (mem_append p'' s).1 this with hh | hh
    · rw [h6 _ hh (start_mem q'')]; exact start_mem s
    · exact hh
  have hvw2 : G.term t = w2 := mem_both q'' s (h5 ▸ nty) (start_mem q'') hvs
  subst hvw2
  have hq'' := closed_nil q'' (nodup_left q'' s (h5 ▸ nty))
  subst hq''
  have h5' : (P.path t y).1 = s := h5
  have hc := append_cancel z p'' q' s (h2.symm.trans h4) (h2 ▸ nxy)
  rw [h2, edges_append, List.count_append, h1, h5', hc.2]

end os

end RepellingPairs.Dev.TrivLeaf
end

section
set_option autoImplicit false

namespace RepellingPairs.Dev.TrivLeaf

open RepellingPairs


variable {k : ℕ}

/-- cost of a configuration for a symmetric `D` -/
def ccost (D : Fin k → Fin k → ℝ) (hs : ∀ i j, D i j = D j i) (C : Config k) : ℝ :=
  (C.map (Sym2.lift ⟨D, hs⟩)).sum

theorem ccost_cons (D : Fin k → Fin k → ℝ) (hs : ∀ i j, D i j = D j i) (x y : Fin k) (C : Config k) :
    ccost D hs (s(x, y) ::ₘ C) = D x y + ccost D hs C := by
  simp [ccost]

/-- Kalmanson for any cyclically ordered quadruple -/
theorem kal_cyc (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D) {p q r s : Fin k}
    (h : CyclicallyOrdered p q r s) :
    D p q + D r s ≤ D p r + D q s ∧ D p s + D q r ≤ D p r + D q s := by
  have hs := hD.symm
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have := hK p q r s h1 h2 h3
    simp only [max_le_iff] at this
    exact this
  · have := hK q r s p h1 h2 h3
    simp only [max_le_iff] at this
    rw [hs s p, hs q p, hs r p] at this
    constructor <;> linarith [this.1, this.2, hs r s, hs q r, hs p s, hs p q, hs p r]
  · have := hK r s p q h1 h2 h3
    simp only [max_le_iff] at this
    constructor <;> linarith [this.1, this.2, hs r s, hs q r, hs p s, hs p q, hs p r, hs r p,
      hs s q, hs q s, hs s p, hs q p, hs r q, hs s r]
  · have := hK s p q r h1 h2 h3
    simp only [max_le_iff] at this
    constructor <;> linarith [this.1, this.2, hs r s, hs q r, hs p s, hs p q, hs p r, hs r p,
      hs s q, hs q s, hs s p, hs q p, hs r q, hs s r]

theorem step_le (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D) {C C₁ : Config k}
    (h : Config.UncrossStep C C₁ ∨ Config.DegenerateStep C C₁) :
    ccost D hD.symm C₁ ≤ ccost D hD.symm C := by
  have hs := hD.symm
  rcases h with ⟨x, y, z, w, rest, hc, rfl, h1 | h1⟩ | ⟨x, y, w, rest, hxy, hxw, rfl, rfl⟩
  · subst h1
    simp only [ccost_cons]
    rcases hc with hc | hc
    · have := kal_cyc D hD hK hc
      linarith [this.1, hs z y, hs w y, hs w z, hs y w, hs z w]
    · have := kal_cyc D hD hK hc
      linarith [this.1, this.2, hs z y, hs w y, hs w z, hs y w, hs z w, hs y z]
  · subst h1
    simp only [ccost_cons]
    rcases hc with hc | hc
    · have := kal_cyc D hD hK hc
      linarith [this.1, this.2, hs z y, hs w y, hs w z, hs y w, hs z w, hs y z]
    · have := kal_cyc D hD hK hc
      linarith [this.1, this.2, hs z y, hs w y, hs w z, hs y w, hs z w, hs y z]
  · simp only [ccost_cons]
    have := hD.triangle y x w
    have h0 := hD.self x
    linarith [hs x y]

theorem reaches_le (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D) {C C' : Config k}
    (h : Config.Reaches C C') : ccost D hD.symm C' ≤ ccost D hD.symm C := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact (step_le D hD hK hs).trans ih


theorem ccost_chords_F (D : Fin k → Fin k → ℝ) (hs : ∀ i j, D i j = D j i) (F : DesignatedFlow k) :
    ccost D hs (DesignatedFlow.chords F) = DesignatedFlow.cost D F := by
  simp [ccost, DesignatedFlow.chords, DesignatedFlow.cost, Multiset.map_map, Function.comp_def]

theorem ccost_chords_F' {V : Type u} {E : Type v} {G : OSInstance V E k}
    (D : Fin k → Fin k → ℝ) (hs : ∀ i j, D i j = D j i) (F' : PathFlow G) :
    ccost D hs (PathFlow.chords F') = PathFlow.cost D F' := by
  simp [ccost, PathFlow.chords, PathFlow.cost, Multiset.map_map, Function.comp_def]

/-- the case of no trivial unit in `F` -/
theorem noTrivial_case {V : Type u} {E : Type v} {k : ℕ}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : OSInstance V E k) (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D)
    (P : PathStructure G) (hgood : P.IsGood D) (F : DesignatedFlow k) (F' : PathFlow G)
    (h2 : Property2 P F F') (h4 : Property4 F F') (h5 : Property5 P F) (hF : NoTrivialPair F) :
    PathFlow.cost D F' ≤ DesignatedFlow.cost D F := by
  have hdom := RepellingPairs.claim_9_flow_dominance G D hD hK P hgood F F' h2 h4 h5 hF
  rw [← ccost_chords_F D hD.symm, ← ccost_chords_F' D hD.symm]
  by_cases hstrict : ∃ i j, Config.dist (PathFlow.chords F') i j < Config.dist (DesignatedFlow.chords F) i j
  · have hloop : ∀ a, s(a, a) ∉ DesignatedFlow.chords F := by
      intro a ha
      simp only [DesignatedFlow.chords, Multiset.mem_map] at ha
      obtain ⟨p, hp, hpa⟩ := ha
      have h : p = (a, a) := by simpa using hpa
      exact hF p hp (by rw [h])
    have hr := RepellingPairs.lemma_10_dominance_implies_uncrossing (DesignatedFlow.chords F)
      (PathFlow.chords F') hloop h4 ⟨hdom, hstrict⟩
    exact reaches_le D hD hK hr
  · simp only [not_exists, not_lt] at hstrict
    have heq := RepellingPairs.config_eq_of_dist_eq (DesignatedFlow.chords F) (PathFlow.chords F') h4
      (fun i j => le_antisymm (hstrict i j) (hdom i j))
    rw [heq]


end RepellingPairs.Dev.TrivLeaf
end

section
set_option autoImplicit false

namespace RepellingPairs.Dev.TrivLeaf

open RepellingPairs


section main

variable {V : Type u} {E : Type v} {k : ℕ} {G : OSInstance V E k}

/-- number of units of `F` on a trivial pair -/
def ntriv (F : DesignatedFlow k) : ℕ := Multiset.countP (fun p : Fin k × Fin k => p.1 = p.2) F

def cnt [DecidableEq E] (P : PathStructure G) (a : Fin k × Fin k) (e : E) : ℕ :=
  (P.path a.1 a.2).1.edges.count e

theorem load_cons [DecidableEq E] (P : PathStructure G) (a : Fin k × Fin k) (F : DesignatedFlow k)
    (e : E) : DesignatedFlow.load P (a ::ₘ F) e = cnt P a e + DesignatedFlow.load P F e := by
  simp [DesignatedFlow.load, cnt]

theorem cost_cons {D : Fin k → Fin k → ℝ} (a : Fin k × Fin k) (F : DesignatedFlow k) :
    DesignatedFlow.cost D (a ::ₘ F) = D a.1 a.2 + DesignatedFlow.cost D F := by
  simp [DesignatedFlow.cost]

theorem deg_cons (c : Sym2 (Fin k)) (C : Config k) (t : Fin k) :
    Config.deg (c ::ₘ C) t = Config.chordDeg t c + Config.deg C t := by
  simp [Config.deg]

theorem chords_cons (a : Fin k × Fin k) (F : DesignatedFlow k) :
    DesignatedFlow.chords (a ::ₘ F) = s(a.1, a.2) ::ₘ DesignatedFlow.chords F := by
  simp [DesignatedFlow.chords]

theorem chordDeg_mk (t x y : Fin k) :
    Config.chordDeg t s(x, y) = (if x = t then 1 else 0) + (if y = t then 1 else 0) := by
  simp [Config.chordDeg]

theorem cnt_triv [DecidableEq E] (P : PathStructure G) (t : Fin k) (e : E) : cnt P (t, t) e = 0 := by
  unfold cnt
  rw [closed_nil (P.path t t).1 (P.path t t).2]
  simp [Multigraph.Walk.edges]

theorem sum_load_F [DecidableEq E] (P : PathStructure G) (S : Finset E) (F : DesignatedFlow k) :
    ∑ e ∈ S, DesignatedFlow.load P F e =
      (F.map fun p => cv S (P.path p.1 p.2).1.edges).sum := by
  induction F using Multiset.induction_on with
  | empty => simp [DesignatedFlow.load]
  | cons a F ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ← ih]
    simp only [load_cons, Finset.sum_add_distrib]
    rfl

theorem sum_load_F' [DecidableEq E] (S : Finset E) (F' : PathFlow G) :
    ∑ e ∈ S, PathFlow.load F' e = (F'.map fun q => cv S q.path.1.edges).sum := by
  induction F' using Multiset.induction_on with
  | empty => simp [PathFlow.load]
  | cons a F ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ← ih]
    simp only [PathFlow.load, Multiset.map_cons, Multiset.sum_cons, Finset.sum_add_distrib]
    rfl

theorem deg_F (F : DesignatedFlow k) (t : Fin k) :
    Config.deg (DesignatedFlow.chords F) t =
      (F.map fun p => (if p.1 = t then 1 else 0) + (if p.2 = t then 1 else 0)).sum := by
  simp [Config.deg, DesignatedFlow.chords, Multiset.map_map, chordDeg_mk]

theorem deg_F' (F' : PathFlow G) (t : Fin k) :
    Config.deg (PathFlow.chords F') t =
      (F'.map fun q => (if q.src = t then 1 else 0) + (if q.tgt = t then 1 else 0)).sum := by
  simp [Config.deg, PathFlow.chords, Multiset.map_map, chordDeg_mk]

/-- Counting at the vertex `term t`: some non-trivial unit of `F` passes through it. -/
theorem exists_interior [Fintype E] [DecidableEq E] (P : PathStructure G) (F : DesignatedFlow k)
    (F' : PathFlow G) (h2 : Property2 P F F') (h4 : Property4 F F') (t : Fin k)
    (ht : (t, t) ∈ F) (hF' : ∀ q ∈ F', ¬ (q.src = t ∧ q.tgt = t)) :
    ∃ p ∈ F, p.1 ≠ t ∧ p.2 ≠ t ∧ G.term t ∈ (P.path p.1 p.2).1.support := by
  classical
  by_contra hcon
  push Not at hcon
  have hF_el : ∀ p ∈ F,
      cv (incid G.graph (G.term t)) (P.path p.1 p.2).1.edges + 2 * (if p = (t, t) then 1 else 0) ≤
        (if p.1 = t then 1 else 0) + (if p.2 = t then 1 else 0) := by
    rintro ⟨a, b⟩ hp
    have hc := cv_path (G.term t) (P.path a b).1 (P.path a b).2
    simp only [(term_inj G).eq_iff] at hc
    have hx := hcon (a, b) hp
    simp only [Prod.mk.injEq] at hx ⊢
    split_ifs at hc ⊢ <;> first | omega | exact absurd ‹G.term t ∈ _› (hx ‹¬a = t› ‹¬b = t›)
  have hF'_el : ∀ q ∈ F',
      (if q.src = t then 1 else 0) + (if q.tgt = t then 1 else 0) ≤
        cv (incid G.graph (G.term t)) q.path.1.edges := by
    rintro ⟨a, b, w⟩ hq
    have hc := cv_path (G.term t) w.1 w.2
    simp only [(term_inj G).eq_iff] at hc
    have hx := hF' _ hq
    simp only at hx ⊢
    split_ifs at hc ⊢ <;> omega
  have s1 := Multiset.sum_map_le_sum_map _ _ hF_el
  rw [Multiset.sum_map_add, Multiset.sum_map_mul_left, ← deg_F] at s1
  have s2 := Multiset.sum_map_le_sum_map _ _ hF'_el
  rw [← deg_F'] at s2
  have s3 : ∑ e ∈ incid G.graph (G.term t), PathFlow.load F' e ≤
      ∑ e ∈ incid G.graph (G.term t), DesignatedFlow.load P F e :=
    Finset.sum_le_sum fun e _ => h2 e
  rw [sum_load_F, sum_load_F'] at s3
  have s4 : 1 ≤ (F.map fun p => if p = (t, t) then 1 else 0).sum := by
    rw [← Multiset.cons_erase ht, Multiset.map_cons, Multiset.sum_cons]
    simp
  have := h4 t
  omega

theorem general [Fintype V] [Fintype E] [DecidableEq E]
    (G : OSInstance V E k) (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D)
    (P : PathStructure G) (hgood : P.IsGood D) :
    ∀ (n : ℕ) (F : DesignatedFlow k) (F' : PathFlow G), ntriv F = n →
      Property2 P F F' → Property4 F F' → PathFlow.cost D F' ≤ DesignatedFlow.cost D F := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F F' hn h2 h4
  by_cases hF : NoTrivialPair F
  · by_contra h3
    push Not at h3
    obtain ⟨F₁, g2, g3, g4, g5, g6⟩ :=
      RepellingPairs.step_1_maximal_switching G D hD hK P hgood F F' h2 h3 h4
    exact absurd g3 (not_lt.2 (noTrivial_case G D hD hK P hgood F₁ F' g2 g4 g5 (g6 hF)))
  simp only [NoTrivialPair, not_forall, not_not] at hF
  obtain ⟨⟨t, b⟩, ht, hpt⟩ := hF
  simp only at hpt
  subst hpt
  by_cases hq : ∃ q ∈ F', q.src = t ∧ q.tgt = t
  · obtain ⟨q, hqm, hqs, hqt⟩ := hq
    obtain ⟨R, rfl⟩ := Multiset.exists_cons_of_mem ht
    obtain ⟨R', rfl⟩ := Multiset.exists_cons_of_mem hqm
    have hlt : ntriv R < n := by
      rw [← hn]; simp [ntriv]
    have hq0 : ∀ e, q.path.1.edges.count e = 0 := by
      intro e
      obtain ⟨a, c, w⟩ := q
      simp only at hqs hqt
      subst hqs hqt
      rw [closed_nil w.1 w.2]
      simp [Multigraph.Walk.edges]
    have hres := ih _ hlt R R' rfl
      (by
        intro e
        have h := h2 e
        rw [load_cons, cnt_triv] at h
        simpa [PathFlow.load, hq0 e] using h)
      (by
        intro s
        have h := h4 s
        rw [chords_cons, deg_cons] at h
        simp only [PathFlow.chords, Multiset.map_cons, deg_cons, hqs, hqt] at h
        simpa [PathFlow.chords] using h)
    rw [cost_cons, hD.self, zero_add]
    simpa [PathFlow.cost, hqs, hqt, hD.self] using hres
  · push Not at hq
    obtain ⟨⟨x, y⟩, hxyF, hx, hy, hv⟩ := exists_interior P F F' h2 h4 t ht
      (fun q hqm hh => hq q hqm hh.1 hh.2)
    simp only at hx hy hv
    have hne : (x, y) ≠ (t, t) := fun h => hx (Prod.mk.inj h).1
    have hmem : (x, y) ∈ F.erase (t, t) := (Multiset.mem_erase_of_ne hne).2 hxyF
    obtain ⟨R, hR⟩ : ∃ R, F = (t, t) ::ₘ (x, y) ::ₘ R :=
      ⟨_, by rw [Multiset.cons_erase hmem, Multiset.cons_erase ht]⟩
    subst hR
    have hnr : ¬ Repel D x y t t := fun hr =>
      hgood x y t t hr (G.term t) hv (start_mem _)
    unfold Repel at hnr
    have hle := le_of_not_gt hnr
    have hm := le_max_left (D x t + D y t) (D x t + D t y)
    have htri := hD.triangle x t y
    have hDeq : D x t + D t y = D x y := by
      linarith [hD.self t, hD.symm y t]
    have hlt : ntriv ((x, t) ::ₘ (t, y) ::ₘ R) < n := by
      rw [← hn]
      simp [ntriv, Multiset.countP_cons, hx, Ne.symm hy]
    have hres := ih _ hlt ((x, t) ::ₘ (t, y) ::ₘ R) F' rfl
      (by
        intro e
        have h := h2 e
        rw [load_cons, load_cons, cnt_triv] at h
        rw [load_cons, load_cons]
        have := split_count P x y t hv e
        simp only [cnt] at h ⊢
        omega)
      (by
        intro s
        rw [← h4 s]
        simp only [chords_cons, deg_cons, chordDeg_mk]
        split_ifs <;> omega)
    rw [cost_cons, cost_cons] at hres ⊢
    simp only at hres ⊢
    linarith [hD.self t]

end main

end RepellingPairs.Dev.TrivLeaf

namespace RepellingPairs


theorem chk_cost_inequality_of_trivial_pair {V : Type u} {E : Type v} {k : ℕ}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : OSInstance V E k) (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D)
    (P : PathStructure G) (hgood : P.IsGood D) (F : DesignatedFlow k) (F' : PathFlow G)
    (h2 : Property2 P F F') (h4 : Property4 F F') (h5 : Property5 P F)
    (t : Fin k) (ht : (t, t) ∈ F) (hF' : ∀ q ∈ F', ¬ (q.src = t ∧ q.tgt = t)) :
    PathFlow.cost D F' ≤ DesignatedFlow.cost D F :=
  Dev.TrivLeaf.general G D hD hK P hgood _ F F' rfl h2 h4

end RepellingPairs
end

theorem solution : type_of% @RepellingPairs.chk_cost_inequality_of_trivial_pair := @RepellingPairs.chk_cost_inequality_of_trivial_pair
