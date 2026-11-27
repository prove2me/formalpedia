-- Prove2me | solution 1 for RobersonCx.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @세리나
-- created : 2026-11-27T01:56:28.598704+00:00
-- url     : https://prove2.me/submissions/cc4ac095-84d4-4dc3-801c-8bc07c62e9b5

import Definitions.Def_RobersonCx_IsImmersion
import Definitions.Def_RobersonCx_IsTopMinor

set_option autoImplicit false

open RobersonCx

private theorem incident_first {V : Type} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hne : u ≠ v) : ∃ x, G.Adj u x ∧ s(u, x) ∈ p.edges := by
  cases p with
  | nil => exact (hne rfl).elim
  | @cons a b c edge rest => exact ⟨b, edge, by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_self⟩

private theorem incident_internal {V : Type} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (hp : p.IsPath) (hw : w ∈ p.support) (hwu : w ≠ u) (hwv : w ≠ v) :
    ∃ a b, a ≠ b ∧ G.Adj w a ∧ G.Adj w b ∧ s(w, a) ∈ p.edges ∧ s(w, b) ∈ p.edges := by
  induction p with
  | nil => exact (hwu (by simpa using hw)).elim
  | @cons x y z e p ih =>
    have hm : w ∈ p.support := by
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
      exact hw.resolve_left hwu
    by_cases hwy : w = y
    · subst w
      cases p with
      | nil => exact (hwv rfl).elim
      | @cons a b c f q =>
        have hn := hp.support_nodup
        rw [SimpleGraph.Walk.support_cons] at hn
        have hne : x ≠ b := by
          intro he
          apply hn.notMem
          rw [SimpleGraph.Walk.support_cons, he]
          exact List.mem_cons_of_mem _ q.start_mem_support
        refine ⟨x, b, hne, e.symm, f, ?_, ?_⟩
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons.2 (.inl (Sym2.eq_iff.2 (.inr ⟨rfl, rfl⟩)))
        · rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ List.mem_cons_self
    · obtain ⟨a, b, hne, ha, hb, hea, heb⟩ := ih hp.of_cons hm hwy hwv
      exact ⟨a, b, hne, ha, hb, List.mem_cons_of_mem _ hea, List.mem_cons_of_mem _ heb⟩

private theorem distinct_incident {V : Type} (w a b : V) {P Q : List (Sym2 V)}
    (d : P.Disjoint Q) (ha : s(w, a) ∈ P) (hb : s(w, b) ∈ Q) : a ≠ b := by
  intro e
  exact (List.disjoint_left.1 d) ha (e.symm ▸ hb)

private theorem no_four_neighbors {V : Type} [Finite V] (G : SimpleGraph V)
    (w a b c d : V) (cap : (G.neighborSet w).ncard ≤ 3)
    (ea : G.Adj w a) (eb : G.Adj w b) (ec : G.Adj w c) (ed : G.Adj w d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    False := by
  classical
  let s : Finset V := {a, b, c, d}
  have ha : a ∉ ({b, c, d} : Finset V) := by simp [hab, hac, had]
  have hb : b ∉ ({c, d} : Finset V) := by simp [hbc, hbd]
  have hc : c ∉ ({d} : Finset V) := by simpa using hcd
  have hcard : s.card = 4 := by simp [s, Finset.card_insert_of_notMem, ha, hb, hc]
  have hsub : (s : Set V) ⊆ G.neighborSet w := by
    intro x hx
    change x ∈ s at hx
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ea
    · exact eb
    · exact ec
    · exact ed
  have hc := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset, hcard] at hc
  omega

theorem solution {W V : Type} [Fintype W] [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    [DecidableRel H.Adj] [DecidableRel G.Adj] (hH : H.IsRegularOfDegree 3) (hG : ∀ v, G.degree v ≤ 3)
    (h : IsImmersion H G) : IsTopMinor H G := by
  classical
  have cap (w : V) : (G.neighborSet w).ncard ≤ 3 := by
    rw [← G.coe_neighborFinset, Set.ncard_coe_finset, G.card_neighborFinset_eq_degree]
    exact hG w
  have two_adjacent (c : W) : ∃ u v, u ≠ v ∧ H.Adj c u ∧ H.Adj c v := by
    have hc : 1 < (H.neighborSet c).ncard := by
      rw [← H.coe_neighborFinset, Set.ncard_coe_finset, H.card_neighborFinset_eq_degree]
      exact (hH c).symm ▸ (by decide : 1 < 3)
    obtain ⟨u, v, hu, hv, hne⟩ := (Set.one_lt_ncard_iff (H.neighborSet c).toFinite).mp hc
    exact ⟨u,v,hne,hu,hv⟩
  obtain ⟨ι, P, inj, path, sep⟩ := h
  have end_ne {x y : W} (he : H.Adj x y) : ι x ≠ ι y := fun e => he.ne (inj e)
  have no_image (x y c : W) (e : H.Adj x y) (hpx : ι c ∈ (P x y e).support)
      (hcx : ι c ≠ ι x) (hcy : ι c ≠ ι y) : False := by
    obtain ⟨a, b, hab, ea, eb, ha, hb⟩ := incident_internal (P x y e) (path x y e) hpx hcx hcy
    obtain ⟨u, v, huv, eu, ev⟩ := two_adjacent c
    obtain ⟨d, ed, hd⟩ := incident_first (P c u eu) (end_ne eu)
    obtain ⟨f, ef, hf⟩ := incident_first (P c v ev) (end_ne ev)
    have different (z : W) : s(x, y) ≠ s(c, z) := by
      intro ee
      rcases Sym2.eq_iff.1 ee with ⟨hh, _⟩ | ⟨_, hh⟩
      · exact hcx (congrArg ι hh.symm)
      · exact hcy (congrArg ι hh.symm)
    have du := sep x y e c u eu (different u)
    have dv := sep x y e c v ev (different v)
    have duv := sep c u eu c v ev (by
      intro heq
      rcases Sym2.eq_iff.1 heq with ⟨_, he⟩ | ⟨he, _⟩
      · exact huv he
      · exact ev.ne he)
    exact no_four_neighbors G _ a b d f (cap _) ea eb ed ef hab
      (distinct_incident _ _ _ du ha hd) (distinct_incident _ _ _ dv ha hf)
      (distinct_incident _ _ _ du hb hd) (distinct_incident _ _ _ dv hb hf)
      (distinct_incident _ _ _ duv hd hf)
  refine ⟨ι, P, inj, path, ?_, ?_⟩
  · rintro x y e z hz c rfl
    by_contra! contra
    exact no_image x y c e hz (fun he => contra.1 (inj he)) (fun he => contra.2 (inj he))
  · intro x y e x' y' e' diff z hz hz'
    by_cases branch : ∃ c : W, z = ι c
    · exact branch
    · have not_image (a : W) : z ≠ ι a := fun he => branch ⟨a,he⟩
      obtain ⟨a,b,hab,ea,eb,ha,hb⟩ := incident_internal (P x y e) (path _ _ _) hz (not_image x) (not_image y)
      obtain ⟨c,d,hcd,ec,ed,hc,hd⟩ := incident_internal (P x' y' e') (path _ _ _) hz' (not_image x') (not_image y')
      have dis := sep x y e x' y' e' diff
      exact (no_four_neighbors G z a b c d (cap z) ea eb ec ed hab
        (distinct_incident _ _ _ dis ha hc) (distinct_incident _ _ _ dis ha hd)
        (distinct_incident _ _ _ dis hb hc) (distinct_incident _ _ _ dis hb hd) hcd).elim
