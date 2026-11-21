-- Prove2me | solution 1 for ResourceScheduling.Poly.p2_min_makespan_matching
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:00:20.929073+00:00
-- url     : https://prove2.me/submissions/4a14d5d3-1670-4271-a505-51ef41644ebd

import Mathlib
import Definitions.Def_ResourceScheduling_Poly_Model
import Definitions.Def_ResourceScheduling_Poly_CompatibilityGraph

set_option autoImplicit false

namespace Aux_P2Match
open ResourceScheduling.Poly

/-! ### Generic facts about schedules -/

theorem transGen_false {α : Type*} {R : α → α → Prop} (h : ∀ a b, ¬ R a b) {a b : α}
    (hab : Relation.TransGen R a b) : False := by
  induction hab with
  | single h' => exact h _ _ h'
  | tail _ h' _ => exact h _ _ h'

theorem proc_pos (I : Instance) (i : Fin I.m) : 0 < I.procTime i := by
  unfold Instance.procTime
  exact one_div_pos.mpr (I.q_pos i)

theorem start_lt_completion {I : Instance} (σ : Schedule I) (j : Fin I.n) :
    σ.start j < σ.completion j := by
  unfold Schedule.completion
  linarith [proc_pos I (σ.machine j)]

theorem mem_filter_any {α : Type*} [Fintype α] (p : α → Prop) (d : DecidablePred p) (a : α) :
    a ∈ @Finset.filter α p d Finset.univ ↔ p a := by
  simp

theorem mem_active {I : Instance} (σ : Schedule I) (t : ℝ) (j : Fin I.n) :
    j ∈ σ.activeSet t ↔ σ.start j ≤ t ∧ t < σ.completion j := by
  unfold Schedule.activeSet
  exact mem_filter_any _ _ j

theorem le_makespan {I : Instance} (σ : Schedule I) (j : Fin I.n) :
    σ.completion j ≤ σ.makespan := by
  unfold Schedule.makespan
  split_ifs with hne
  · exact Finset.le_sup' σ.completion (Finset.mem_univ j)
  · exact (hne ⟨j, Finset.mem_univ j⟩).elim

theorem makespan_le {I : Instance} (σ : Schedule I) (M : ℝ) (h : ∀ j, σ.completion j ≤ M)
    (h0 : 0 ≤ M) : σ.makespan ≤ M := by
  unfold Schedule.makespan
  split_ifs with hne
  · exact Finset.sup'_le hne _ (fun j _ => h j)
  · exact h0

theorem makespan_nonneg {I : Instance} (σ : Schedule I) (hσ : ∀ j, 0 ≤ σ.start j) :
    0 ≤ σ.makespan := by
  unfold Schedule.makespan
  split_ifs with hne
  · obtain ⟨j, -⟩ := id hne
    exact le_trans (le_trans (hσ j) (start_lt_completion σ j).le)
      (Finset.le_sup' σ.completion (Finset.mem_univ j))
  · exact le_rfl

theorem sum_le_of_pairs {ι : Type*} [DecidableEq ι] (A : Finset ι) (r : ι → ℕ) (s : ℕ)
    (h1 : ∀ a ∈ A, r a ≤ s) (h2 : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → r a + r b ≤ s)
    (h3 : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c → False) :
    ∑ a ∈ A, r a ≤ s := by
  rcases A.eq_empty_or_nonempty with hA | ⟨a, ha⟩
  · rw [hA, Finset.sum_empty]; exact Nat.zero_le _
  · by_cases hb : ∃ b ∈ A, b ≠ a
    · obtain ⟨b, hb, hba⟩ := hb
      have hsub : A ⊆ {a, b} := by
        intro c hc
        by_contra hc'
        rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hc'
        exact h3 a ha b hb c hc (Ne.symm hba) (Ne.symm hc'.1) (Ne.symm hc'.2)
      calc ∑ x ∈ A, r x ≤ ∑ x ∈ ({a, b} : Finset ι), r x := Finset.sum_le_sum_of_subset hsub
        _ = r a + r b := Finset.sum_pair (Ne.symm hba)
        _ ≤ s := h2 a ha b hb (Ne.symm hba)
    · push_neg at hb
      have hsub : A ⊆ {a} := by
        intro c hc
        rw [Finset.mem_singleton]
        exact hb c hc
      calc ∑ x ∈ A, r x ≤ ∑ x ∈ ({a} : Finset ι), r x := Finset.sum_le_sum_of_subset hsub
        _ = r a := Finset.sum_singleton _ _
        _ ≤ s := h1 a ha

theorem fin2_eq {m : ℕ} (hm : m = 2) (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) : y = z := by
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  have h1 : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  have h2 : x.val ≠ z.val := fun h => hxz (Fin.ext h)
  exact Fin.ext (by omega)

theorem active_sum_le {I : Instance} (hm : I.m = 2) (σ : Schedule I)
    (hdisj : ∀ j k, j ≠ k → σ.machine j = σ.machine k →
      σ.completion j ≤ σ.start k ∨ σ.completion k ≤ σ.start j)
    (r : Fin I.n → ℕ) (s : ℕ) (t : ℝ) (h1 : ∀ a, r a ≤ s)
    (h2 : ∀ a b, a ∈ σ.activeSet t → b ∈ σ.activeSet t → σ.machine a ≠ σ.machine b →
      r a + r b ≤ s) :
    ∑ a ∈ σ.activeSet t, r a ≤ s := by
  have hnb : ∀ a b, a ∈ σ.activeSet t → b ∈ σ.activeSet t → a ≠ b →
      σ.machine a ≠ σ.machine b := by
    intro a b ha hb hab hmab
    rw [mem_active] at ha hb
    rcases hdisj a b hab hmab with h | h
    · linarith [ha.2, hb.1]
    · linarith [ha.1, hb.2]
  apply sum_le_of_pairs
  · intro a _
    exact h1 a
  · intro a ha b hb hab
    exact h2 a b ha hb (hnb a b ha hb hab)
  · intro a ha b hb c hc hab hac hbc
    exact hnb b c hb hc hbc (fin2_eq hm _ _ _ (hnb a b ha hb hab) (hnb a c ha hc hac))

/-! ### Unit processing times -/

theorem compl_eq (I : Instance) (hq : ∀ i, I.q i = 1) (σ : Schedule I) (j : Fin I.n) :
    σ.completion j = σ.start j + 1 := by
  unfold Schedule.completion Instance.procTime
  rw [hq, div_one]

/-! ### Lower bound: a feasible schedule yields a large matching -/

/-- `P` is a set of vertex-disjoint compatible pairs of jobs of `T`. -/
def Good (I : Instance) (T : Finset (Fin I.n)) (P : Finset (Fin I.n × Fin I.n)) : Prop :=
  (∀ e ∈ P, e.1 ∈ T ∧ e.2 ∈ T ∧ I.compatGraph.Adj e.1 e.2) ∧
  (∀ e ∈ P, ∀ e' ∈ P, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2)

theorem lower (I : Instance) (hm : I.m = 2) (hq : ∀ i, I.q i = 1) (σ : Schedule I)
    (hσ : σ.Feasible) :
    ∀ (N : ℕ) (T : Finset (Fin I.n)), T.card ≤ N → ∀ (t0 C : ℝ),
      (∀ j ∈ T, t0 ≤ σ.start j) → (∀ j ∈ T, σ.start j + 1 ≤ C) → t0 ≤ C →
      ∃ P, Good I T P ∧ (T.card : ℝ) ≤ C - t0 + P.card := by
  obtain ⟨_, hdisj, _, hres⟩ := hσ
  have hc := compl_eq I hq σ
  intro N
  induction N with
  | zero =>
    intro T hT t0 C _ _ htC
    refine ⟨∅, ⟨fun e he => absurd he (by simp), fun e he => absurd he (by simp)⟩, ?_⟩
    have h0 : T.card = 0 := by omega
    rw [h0, Finset.card_empty, Nat.cast_zero]
    linarith
  | succ N ih =>
    intro T hT t0 C hst hco htC
    rcases T.eq_empty_or_nonempty with hE | hne
    · refine ⟨∅, ⟨fun e he => absurd he (by simp), fun e he => absurd he (by simp)⟩, ?_⟩
      rw [hE, Finset.card_empty, Finset.card_empty, Nat.cast_zero]
      linarith
    obtain ⟨j, hj, hmin⟩ := T.exists_min_image σ.start hne
    by_cases hA : ∃ k ∈ T, σ.machine k ≠ σ.machine j ∧ σ.start k < σ.start j + 1
    · obtain ⟨k, hk, hmk, hsk⟩ := hA
      have hjk : j ≠ k := by
        intro h
        rw [h] at hmk
        exact hmk rfl
      have hadj : I.compatGraph.Adj j k := by
        refine ⟨hjk, fun h => ?_⟩
        have hjt : j ∈ σ.activeSet (σ.start k) :=
          (mem_active σ _ j).mpr ⟨hmin k hk, by rw [hc]; exact hsk⟩
        have hkt : k ∈ σ.activeSet (σ.start k) :=
          (mem_active σ _ k).mpr ⟨le_rfl, start_lt_completion σ k⟩
        have hsub : ({j, k} : Finset (Fin I.n)) ⊆ σ.activeSet (σ.start k) := by
          intro x hx
          rw [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with hx | hx
          · rw [hx]; exact hjt
          · rw [hx]; exact hkt
        have h1 := Finset.sum_le_sum_of_subset (f := I.r h) hsub
        rw [Finset.sum_pair hjk] at h1
        exact le_trans h1 (hres _ h)
      have hmemT' : ∀ i ∈ (T.erase j).erase k, i ≠ j ∧ i ≠ k ∧ i ∈ T := by
        intro i hi
        have h1 := Finset.ne_of_mem_erase hi
        have h2 := Finset.mem_of_mem_erase hi
        exact ⟨Finset.ne_of_mem_erase h2, h1, Finset.mem_of_mem_erase h2⟩
      have hst' : ∀ i ∈ (T.erase j).erase k, σ.start j + 1 ≤ σ.start i := by
        intro i hi
        obtain ⟨hij, hik, hiT⟩ := hmemT' i hi
        have hmi := hmin i hiT
        have hmk' := hmin k hk
        by_cases hmij : σ.machine i = σ.machine j
        · rcases hdisj j i (Ne.symm hij) hmij.symm with h | h
          · rw [hc] at h
            exact h
          · rw [hc] at h
            linarith
        · have hmik : σ.machine i = σ.machine k :=
            fin2_eq hm (σ.machine j) _ _ (Ne.symm hmij) (Ne.symm hmk)
          rcases hdisj k i (Ne.symm hik) hmik.symm with h | h
          · rw [hc] at h
            linarith
          · rw [hc] at h
            linarith
      have hcard : ((T.erase j).erase k).card + 2 = T.card := by
        have h1 := Finset.card_erase_of_mem hj
        have h2 : k ∈ T.erase j := Finset.mem_erase.mpr ⟨Ne.symm hjk, hk⟩
        have h3 := Finset.card_erase_of_mem h2
        have h4 : 2 ≤ T.card := by
          have hs : ({j, k} : Finset (Fin I.n)) ⊆ T := by
            intro x hx
            rw [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with hx | hx
            · rw [hx]; exact hj
            · rw [hx]; exact hk
          have h5 := Finset.card_le_card hs
          rwa [Finset.card_pair hjk] at h5
        omega
      obtain ⟨P', hP', hP'c⟩ := ih ((T.erase j).erase k) (by omega) (σ.start j + 1) C hst'
        (fun i hi => hco i (hmemT' i hi).2.2) (by have := hco j hj; linarith)
      have hjkP : (j, k) ∉ P' := by
        intro hin
        have h1 := (hP'.1 _ hin).1
        exact (hmemT' _ h1).1 rfl
      refine ⟨insert (j, k) P', ⟨?_, ?_⟩, ?_⟩
      · intro e he
        rw [Finset.mem_insert] at he
        rcases he with he | he
        · rw [he]
          exact ⟨hj, hk, hadj⟩
        · obtain ⟨h1, h2, h3⟩ := hP'.1 e he
          exact ⟨(hmemT' _ h1).2.2, (hmemT' _ h2).2.2, h3⟩
      · intro e he e' he' hne
        rw [Finset.mem_insert] at he he'
        rcases he with he | he <;> rcases he' with he' | he'
        · exact absurd (he.trans he'.symm) hne
        · rw [he]
          obtain ⟨h1, h2, _⟩ := hP'.1 e' he'
          obtain ⟨a1, a2, _⟩ := hmemT' _ h1
          obtain ⟨b1, b2, _⟩ := hmemT' _ h2
          exact ⟨Ne.symm a1, Ne.symm b1, Ne.symm a2, Ne.symm b2⟩
        · rw [he']
          obtain ⟨h1, h2, _⟩ := hP'.1 e he
          obtain ⟨a1, a2, _⟩ := hmemT' _ h1
          obtain ⟨b1, b2, _⟩ := hmemT' _ h2
          exact ⟨a1, a2, b1, b2⟩
        · exact hP'.2 e he e' he' hne
      · rw [Finset.card_insert_of_notMem hjkP]
        have hTc : (T.card : ℝ) = (((T.erase j).erase k).card : ℝ) + 2 := by
          exact_mod_cast hcard.symm
        have h1 := hst j hj
        push_cast
        linarith
    · push_neg at hA
      have hst' : ∀ i ∈ T.erase j, σ.start j + 1 ≤ σ.start i := by
        intro i hi
        have hij := Finset.ne_of_mem_erase hi
        have hiT := Finset.mem_of_mem_erase hi
        have hmi := hmin i hiT
        by_cases hmij : σ.machine i = σ.machine j
        · rcases hdisj j i (Ne.symm hij) hmij.symm with h | h
          · rw [hc] at h
            exact h
          · rw [hc] at h
            linarith
        · exact hA i hiT hmij
      have hcard : (T.erase j).card + 1 = T.card := Finset.card_erase_add_one hj
      obtain ⟨P', hP', hP'c⟩ := ih (T.erase j) (by omega) (σ.start j + 1) C hst'
        (fun i hi => hco i (Finset.mem_of_mem_erase hi)) (by have := hco j hj; linarith)
      refine ⟨P', ⟨fun e he => ?_, hP'.2⟩, ?_⟩
      · obtain ⟨h1, h2, h3⟩ := hP'.1 e he
        exact ⟨Finset.mem_of_mem_erase h1, Finset.mem_of_mem_erase h2, h3⟩
      · have hTc : (T.card : ℝ) = ((T.erase j).card : ℝ) + 1 := by
          exact_mod_cast hcard.symm
        have h1 := hst j hj
        linarith

/-- The subgraph of `G` whose edges are the pairs in `P`. -/
def toSub (I : Instance) (P : Finset (Fin I.n × Fin I.n))
    (hP : ∀ e ∈ P, I.compatGraph.Adj e.1 e.2) : I.compatGraph.Subgraph where
  verts := {v | ∃ e ∈ P, v = e.1 ∨ v = e.2}
  Adj a b := ∃ e ∈ P, (a = e.1 ∧ b = e.2) ∨ (a = e.2 ∧ b = e.1)
  adj_sub := by
    intro a b hab
    obtain ⟨e, he, h⟩ := hab
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact hP e he
    · rw [h1, h2]
      exact (hP e he).symm
  edge_vert := by
    intro a b hab
    obtain ⟨e, he, h⟩ := hab
    show ∃ e' ∈ P, a = e'.1 ∨ a = e'.2
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact ⟨e, he, Or.inl h1⟩
    · exact ⟨e, he, Or.inr h1⟩
  symm := ⟨fun a b hab => by
    obtain ⟨e, he, h⟩ := hab
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨e, he, Or.inr ⟨h2, h1⟩⟩
    · exact ⟨e, he, Or.inl ⟨h2, h1⟩⟩⟩

theorem toSub_adj (I : Instance) (P : Finset (Fin I.n × Fin I.n))
    (hP : ∀ e ∈ P, I.compatGraph.Adj e.1 e.2) (a b : Fin I.n) :
    (toSub I P hP).Adj a b ↔ ∃ e ∈ P, (a = e.1 ∧ b = e.2) ∨ (a = e.2 ∧ b = e.1) := Iff.rfl

theorem toSub_verts (I : Instance) (P : Finset (Fin I.n × Fin I.n))
    (hP : ∀ e ∈ P, I.compatGraph.Adj e.1 e.2) (v : Fin I.n) :
    v ∈ (toSub I P hP).verts ↔ ∃ e ∈ P, v = e.1 ∨ v = e.2 := Iff.rfl

theorem toSub_matching (I : Instance) (P : Finset (Fin I.n × Fin I.n))
    (hP : ∀ e ∈ P, I.compatGraph.Adj e.1 e.2)
    (hdis : ∀ e ∈ P, ∀ e' ∈ P, e ≠ e' →
      e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2) :
    (toSub I P hP).IsMatching := by
  intro v hv
  rw [toSub_verts] at hv
  obtain ⟨e, he, hve⟩ := hv
  obtain ⟨hne, -⟩ := hP e he
  rcases hve with hve | hve
  · refine ⟨e.2, (toSub_adj I P hP _ _).mpr ⟨e, he, Or.inl ⟨hve, rfl⟩⟩, ?_⟩
    intro w hw
    obtain ⟨e', he', h⟩ := (toSub_adj I P hP _ _).mp hw
    by_cases hee : e = e'
    · rw [← hee] at h
      rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2
      · exact absurd (hve.symm.trans h1) hne
    · rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact absurd (hve.symm.trans h1) (hdis e he e' he' hee).1
      · exact absurd (hve.symm.trans h1) (hdis e he e' he' hee).2.1
  · refine ⟨e.1, (toSub_adj I P hP _ _).mpr ⟨e, he, Or.inr ⟨hve, rfl⟩⟩, ?_⟩
    intro w hw
    obtain ⟨e', he', h⟩ := (toSub_adj I P hP _ _).mp hw
    by_cases hee : e = e'
    · rw [← hee] at h
      rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact absurd (hve.symm.trans h1).symm hne
      · exact h2
    · rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact absurd (hve.symm.trans h1) (hdis e he e' he' hee).2.2.1
      · exact absurd (hve.symm.trans h1) (hdis e he e' he' hee).2.2.2

theorem toSub_card (I : Instance) (P : Finset (Fin I.n × Fin I.n))
    (hP : ∀ e ∈ P, I.compatGraph.Adj e.1 e.2)
    (hdis : ∀ e ∈ P, ∀ e' ∈ P, e ≠ e' →
      e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2) :
    P.card ≤ (toSub I P hP).edgeSet.ncard := by
  have hsub : (↑(P.image (fun e => s(e.1, e.2))) : Set (Sym2 (Fin I.n)))
      ⊆ (toSub I P hP).edgeSet := by
    intro x hx
    rw [Finset.coe_image] at hx
    obtain ⟨e, he, rfl⟩ := hx
    show s(e.1, e.2) ∈ (toSub I P hP).edgeSet
    rw [SimpleGraph.Subgraph.mem_edgeSet]
    exact (toSub_adj I P hP _ _).mpr ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  have hinj : Set.InjOn (fun e : Fin I.n × Fin I.n => s(e.1, e.2)) ↑P := by
    intro e he e' he' heq
    have heq' : s(e.1, e.2) = s(e'.1, e'.2) := heq
    rw [Sym2.eq_iff] at heq'
    by_contra hne
    rcases heq' with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact (hdis e he e' he' hne).1 h1
    · exact (hdis e he e' he' hne).2.1 h1
  calc P.card = (P.image (fun e => s(e.1, e.2))).card := (Finset.card_image_of_injOn hinj).symm
    _ = (↑(P.image (fun e => s(e.1, e.2))) : Set (Sym2 (Fin I.n))).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ (toSub I P hP).edgeSet.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

/-! ### Upper bound: a schedule from the matching `S` -/

/-- The partner of `v` in the matching (or `v` itself if unmatched). -/
noncomputable def partner (I : Instance) (S : I.compatGraph.Subgraph) (hS : S.IsMatching)
    (v : Fin I.n) : Fin I.n := by
  classical
  exact if h : v ∈ S.verts then (hS h).exists.choose else v

theorem partner_spec (I : Instance) (S : I.compatGraph.Subgraph) (hS : S.IsMatching)
    {v : Fin I.n} (h : v ∈ S.verts) : S.Adj v (partner I S hS v) := by
  unfold partner
  split_ifs
  exact (hS h).exists.choose_spec

theorem partner_not (I : Instance) (S : I.compatGraph.Subgraph) (hS : S.IsMatching)
    {v : Fin I.n} (h : v ∉ S.verts) : partner I S hS v = v := by
  unfold partner
  split_ifs
  rfl

theorem partner_eq (I : Instance) (S : I.compatGraph.Subgraph) (hS : S.IsMatching)
    {v w : Fin I.n} (h : S.Adj v w) : partner I S hS v = w :=
  (hS (S.edge_vert h)).unique (partner_spec I S hS (S.edge_vert h)) h

theorem partner_invol (I : Instance) (S : I.compatGraph.Subgraph) (hS : S.IsMatching)
    (v : Fin I.n) : partner I S hS (partner I S hS v) = v := by
  by_cases h : v ∈ S.verts
  · exact partner_eq I S hS (partner_spec I S hS h).symm
  · rw [partner_not I S hS h, partner_not I S hS h]

theorem partner_adj (I : Instance) (S : I.compatGraph.Subgraph) (hS : S.IsMatching)
    {v : Fin I.n} (h : partner I S hS v ≠ v) : S.Adj v (partner I S hS v) := by
  by_cases hv : v ∈ S.verts
  · exact partner_spec I S hS hv
  · exact absurd (partner_not I S hS hv) h

/-- Representatives: the smaller job of each matched pair, and every unmatched job. -/
noncomputable def Rset (I : Instance) (S : I.compatGraph.Subgraph) (hS : S.IsMatching) :
    Finset (Fin I.n) :=
  Finset.univ.filter (fun v => v ≤ partner I S hS v)

noncomputable def slotOf (I : Instance) (S : I.compatGraph.Subgraph) (hS : S.IsMatching)
    (x : Fin I.n) : ℕ :=
  ((Rset I S hS).filter (fun v => v < x)).card

noncomputable def rep (I : Instance) (S : I.compatGraph.Subgraph) (hS : S.IsMatching)
    (j : Fin I.n) : Fin I.n :=
  min j (partner I S hS j)

theorem mem_Rset (I : Instance) (S : I.compatGraph.Subgraph) (hS : S.IsMatching)
    (v : Fin I.n) : v ∈ Rset I S hS ↔ v ≤ partner I S hS v := by
  unfold Rset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem rep_mem (I : Instance) (S : I.compatGraph.Subgraph) (hS : S.IsMatching)
    (j : Fin I.n) : rep I S hS j ∈ Rset I S hS := by
  rw [mem_Rset]
  unfold rep
  rcases le_total j (partner I S hS j) with h | h
  · rw [min_eq_left h]
    exact h
  · rw [min_eq_right h, partner_invol]
    exact h

theorem slotOf_lt (I : Instance) (S : I.compatGraph.Subgraph) (hS : S.IsMatching)
    {a b : Fin I.n} (ha : a ∈ Rset I S hS) (hab : a < b) :
    slotOf I S hS a < slotOf I S hS b := by
  unfold slotOf
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨a, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨ha, hab⟩
    · rw [Finset.mem_filter]
      intro h
      exact lt_irrefl a h.2
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 hab⟩

theorem slot_lt_card (I : Instance) (S : I.compatGraph.Subgraph) (hS : S.IsMatching)
    (j : Fin I.n) : slotOf I S hS (rep I S hS j) < (Rset I S hS).card := by
  unfold slotOf
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  refine ⟨rep I S hS j, rep_mem I S hS j, ?_⟩
  rw [Finset.mem_filter]
  intro h
  exact lt_irrefl _ h.2

theorem rep_eq_of_slot (I : Instance) (S : I.compatGraph.Subgraph) (hS : S.IsMatching)
    {j k : Fin I.n}
    (h : slotOf I S hS (rep I S hS j) = slotOf I S hS (rep I S hS k)) :
    rep I S hS j = rep I S hS k := by
  rcases lt_trichotomy (rep I S hS j) (rep I S hS k) with hlt | heq | hgt
  · exact absurd h (ne_of_lt (slotOf_lt I S hS (rep_mem I S hS j) hlt))
  · exact heq
  · exact absurd h (ne_of_gt (slotOf_lt I S hS (rep_mem I S hS k) hgt))

theorem rep_cases (I : Instance) (S : I.compatGraph.Subgraph) (hS : S.IsMatching)
    (j k : Fin I.n) (h : rep I S hS j = rep I S hS k) : k = j ∨ k = partner I S hS j := by
  unfold rep at h
  rcases min_choice j (partner I S hS j) with h1 | h1 <;>
    rcases min_choice k (partner I S hS k) with h2 | h2 <;> rw [h1, h2] at h
  · left
    exact h.symm
  · right
    rw [h, partner_invol]
  · right
    exact h.symm
  · left
    have h3 := congrArg (partner I S hS) h
    rw [partner_invol, partner_invol] at h3
    exact h3.symm

/-- Matched pairs run in parallel in one unit slot; unmatched jobs run alone. -/
noncomputable def sched (I : Instance) (hm : I.m = 2) (S : I.compatGraph.Subgraph)
    (hS : S.IsMatching) : Schedule I where
  machine j := if partner I S hS j < j then (⟨1, by omega⟩ : Fin I.m) else ⟨0, by omega⟩
  start j := ((slotOf I S hS (rep I S hS j) : ℕ) : ℝ)

theorem sched_mach_val (I : Instance) (hm : I.m = 2) (S : I.compatGraph.Subgraph)
    (hS : S.IsMatching) (j : Fin I.n) :
    ((sched I hm S hS).machine j).val = if partner I S hS j < j then 1 else 0 := by
  show (if partner I S hS j < j then (⟨1, by omega⟩ : Fin I.m) else ⟨0, by omega⟩).val = _
  split_ifs <;> rfl

theorem sched_mach_ne (I : Instance) (hm : I.m = 2) (S : I.compatGraph.Subgraph)
    (hS : S.IsMatching) {j : Fin I.n} (hj : partner I S hS j ≠ j) :
    (sched I hm S hS).machine j ≠ (sched I hm S hS).machine (partner I S hS j) := by
  intro h
  have h' := congrArg Fin.val h
  rw [sched_mach_val, sched_mach_val, partner_invol] at h'
  rcases lt_or_gt_of_ne hj with hlt | hgt
  · rw [if_pos hlt, if_neg (not_lt.mpr hlt.le)] at h'
    exact absurd h' (by norm_num)
  · rw [if_neg (not_lt.mpr hgt.le), if_pos hgt] at h'
    exact absurd h' (by norm_num)

theorem sched_disj (I : Instance) (hm : I.m = 2) (hq : ∀ i, I.q i = 1)
    (S : I.compatGraph.Subgraph) (hS : S.IsMatching) :
    ∀ j k, j ≠ k → (sched I hm S hS).machine j = (sched I hm S hS).machine k →
      (sched I hm S hS).completion j ≤ (sched I hm S hS).start k ∨
        (sched I hm S hS).completion k ≤ (sched I hm S hS).start j := by
  intro j k hjk hmach
  rw [compl_eq I hq, compl_eq I hq]
  show (slotOf I S hS (rep I S hS j) : ℝ) + 1 ≤ slotOf I S hS (rep I S hS k) ∨
    (slotOf I S hS (rep I S hS k) : ℝ) + 1 ≤ slotOf I S hS (rep I S hS j)
  have hne : slotOf I S hS (rep I S hS j) ≠ slotOf I S hS (rep I S hS k) := by
    intro h
    rcases rep_cases I S hS j k (rep_eq_of_slot I S hS h) with h1 | h1
    · exact hjk h1.symm
    · have hpj : partner I S hS j ≠ j := by
        rw [← h1]
        exact Ne.symm hjk
      rw [h1] at hmach
      exact sched_mach_ne I hm S hS hpj hmach
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · left
    exact_mod_cast Nat.succ_le_of_lt h
  · right
    exact_mod_cast Nat.succ_le_of_lt h

theorem sched_feasible (I : Instance) (hm : I.m = 2) (hq : ∀ i, I.q i = 1)
    (hprec : I.NoPrecedence) (hfit : I.EveryJobFits)
    (S : I.compatGraph.Subgraph) (hS : S.IsMatching) : (sched I hm S hS).Feasible := by
  refine ⟨fun j => ?_, sched_disj I hm hq S hS, fun j k h => (transGen_false hprec h).elim, ?_⟩
  · show (0 : ℝ) ≤ ((slotOf I S hS (rep I S hS j) : ℕ) : ℝ)
    exact Nat.cast_nonneg _
  intro t h
  apply active_sum_le hm _ (sched_disj I hm hq S hS) (I.r h) (I.s h) t (fun a => hfit h a)
  intro a b ha hb hab
  rw [mem_active, compl_eq I hq] at ha hb
  have ha' : (slotOf I S hS (rep I S hS a) : ℝ) ≤ t ∧
      t < (slotOf I S hS (rep I S hS a) : ℝ) + 1 := ha
  have hb' : (slotOf I S hS (rep I S hS b) : ℝ) ≤ t ∧
      t < (slotOf I S hS (rep I S hS b) : ℝ) + 1 := hb
  have h1 : slotOf I S hS (rep I S hS a) < slotOf I S hS (rep I S hS b) + 1 := by
    have h3 : (slotOf I S hS (rep I S hS a) : ℝ) < (slotOf I S hS (rep I S hS b) : ℝ) + 1 := by
      linarith [ha'.1, hb'.2]
    exact_mod_cast h3
  have h2 : slotOf I S hS (rep I S hS b) < slotOf I S hS (rep I S hS a) + 1 := by
    have h3 : (slotOf I S hS (rep I S hS b) : ℝ) < (slotOf I S hS (rep I S hS a) : ℝ) + 1 := by
      linarith [hb'.1, ha'.2]
    exact_mod_cast h3
  have hs : slotOf I S hS (rep I S hS a) = slotOf I S hS (rep I S hS b) := by omega
  rcases rep_cases I S hS a b (rep_eq_of_slot I S hS hs) with h3 | h3
  · exfalso
    apply hab
    rw [h3]
  · have hpa : partner I S hS a ≠ a := by
      intro he
      apply hab
      rw [h3, he]
    have hadj := partner_adj I S hS hpa
    obtain ⟨_, hres⟩ := S.adj_sub hadj
    rw [h3]
    exact hres h

theorem Rset_card (I : Instance) (S : I.compatGraph.Subgraph) (hS : S.IsMatching) :
    (Rset I S hS).card + S.edgeSet.ncard ≤ I.n := by
  have hsum : (Rset I S hS).card
      + (Finset.univ.filter (fun v => ¬ v ≤ partner I S hS v)).card = I.n := by
    unfold Rset
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hsub : S.edgeSet ⊆ ↑((Finset.univ.filter (fun v => ¬ v ≤ partner I S hS v)).image
      (fun v => s(v, partner I S hS v))) := by
    intro x
    induction x using Sym2.ind with
    | h a b =>
      intro hx
      rw [SimpleGraph.Subgraph.mem_edgeSet] at hx
      have hpa := partner_eq I S hS hx
      have hpb := partner_eq I S hS hx.symm
      obtain ⟨hne, -⟩ := S.adj_sub hx
      rw [Finset.coe_image]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · refine ⟨b, ?_, ?_⟩
        · rw [Finset.mem_coe, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [hpb]
          exact not_le.mpr hlt
        · show s(b, partner I S hS b) = s(a, b)
          rw [hpb]
          exact Sym2.eq_swap
      · refine ⟨a, ?_, ?_⟩
        · rw [Finset.mem_coe, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [hpa]
          exact not_le.mpr hgt
        · show s(a, partner I S hS a) = s(a, b)
          rw [hpa]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at h1
  have h2 := Finset.card_image_le (s := Finset.univ.filter (fun v => ¬ v ≤ partner I S hS v))
    (f := fun v => s(v, partner I S hS v))
  omega

end Aux_P2Match

open ResourceScheduling.Poly in
theorem solution (I : Instance) (hm : I.m = 2) (hq : ∀ i, I.q i = 1)
    (hprec : I.NoPrecedence) (hfit : I.EveryJobFits)
    (S : I.compatGraph.Subgraph) (hS : S.IsMatching)
    (hmax : ∀ S' : I.compatGraph.Subgraph, S'.IsMatching → S'.edgeSet.ncard ≤ S.edgeSet.ncard) :
    (∃ σ : Schedule I, σ.Feasible ∧ σ.makespan = (I.n : ℝ) - S.edgeSet.ncard) ∧
      ∀ σ : Schedule I, σ.Feasible → (I.n : ℝ) - S.edgeSet.ncard ≤ σ.makespan := by
  have hlow : ∀ σ : Schedule I, σ.Feasible → (I.n : ℝ) - S.edgeSet.ncard ≤ σ.makespan := by
    intro σ hσ
    have hL0 := Aux_P2Match.makespan_nonneg σ hσ.1
    obtain ⟨P, hP, hPc⟩ := Aux_P2Match.lower I hm hq σ hσ I.n Finset.univ (by simp) 0
      σ.makespan (fun j _ => hσ.1 j)
      (fun j _ => by rw [← Aux_P2Match.compl_eq I hq]; exact Aux_P2Match.le_makespan σ j) hL0
    have hadj : ∀ e ∈ P, I.compatGraph.Adj e.1 e.2 := fun e he => (hP.1 e he).2.2
    have h1 := Aux_P2Match.toSub_card I P hadj hP.2
    have h2 := hmax _ (Aux_P2Match.toSub_matching I P hadj hP.2)
    rw [Finset.card_univ, Fintype.card_fin] at hPc
    have h3 : (P.card : ℝ) ≤ S.edgeSet.ncard := by exact_mod_cast h1.trans h2
    linarith
  refine ⟨⟨Aux_P2Match.sched I hm S hS,
    Aux_P2Match.sched_feasible I hm hq hprec hfit S hS, ?_⟩, hlow⟩
  have h2 := Aux_P2Match.Rset_card I S hS
  have h4 : ((Aux_P2Match.Rset I S hS).card : ℝ) + (S.edgeSet.ncard : ℝ) ≤ I.n := by
    exact_mod_cast h2
  apply le_antisymm ?_ (hlow _ (Aux_P2Match.sched_feasible I hm hq hprec hfit S hS))
  apply Aux_P2Match.makespan_le
  · intro j
    rw [Aux_P2Match.compl_eq I hq]
    have h1 := Aux_P2Match.slot_lt_card I S hS j
    have h3 : ((Aux_P2Match.slotOf I S hS (Aux_P2Match.rep I S hS j) : ℕ) : ℝ) + 1
        ≤ ((Aux_P2Match.Rset I S hS).card : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt h1
    show ((Aux_P2Match.slotOf I S hS (Aux_P2Match.rep I S hS j) : ℕ) : ℝ) + 1 ≤ _
    linarith
  · have h5 : (0 : ℝ) ≤ ((Aux_P2Match.Rset I S hS).card : ℝ) := Nat.cast_nonneg _
    linarith
