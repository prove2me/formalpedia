-- Prove2me | solution 1 for TraceAdopt.LPReform.proposition_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T23:54:34.012545+00:00
-- url     : https://prove2.me/submissions/65083801-57f0-4ad5-b5b3-73b1d47a8e22

import Definitions.Def_TraceAdopt_LPReform_BiLP10Graph

namespace TraceAdopt.LPReform

open SimpleGraph

/-- Sufficient condition for the path axiom (iii): bags containing a vertex are
walk-connected inside a tree. -/
theorem taTD_iii_of_walks {V T : Type} [DecidableEq V] {t : SimpleGraph T} (ht : t.IsAcyclic)
    (X : T → Finset V)
    (h : ∀ v a b, v ∈ X a → v ∈ X b → ∃ w : t.Walk a b, ∀ c ∈ w.support, v ∈ X c) :
    ∀ (s s' s'' : T) (p : t.Walk s s''), p.IsPath → s' ∈ p.support → X s ∩ X s'' ⊆ X s' := by
  classical
  intro s s' s'' p hp hs' v hv
  rw [Finset.mem_inter] at hv
  obtain ⟨w, hw⟩ := h v s s'' hv.1 hv.2
  have heq : (⟨w.bypass, w.bypass_isPath⟩ : t.Path s s'') = ⟨p, hp⟩ :=
    (ht.subsingleton_path s s'').elim _ _
  have hq : w.bypass = p := congrArg Subtype.val heq
  apply hw
  apply w.support_bypass_subset_support
  rw [hq]; exact hs'

theorem taTD_walks_of_iii {V T : Type} [DecidableEq V] {t : SimpleGraph T} (ht : t.Connected)
    (X : T → Finset V)
    (h : ∀ (s s' s'' : T) (p : t.Walk s s''), p.IsPath → s' ∈ p.support → X s ∩ X s'' ⊆ X s') :
    ∀ v a b, v ∈ X a → v ∈ X b → ∃ w : t.Walk a b, ∀ c ∈ w.support, v ∈ X c := by
  classical
  intro v a b ha hb
  obtain ⟨w⟩ := ht.preconnected a b
  refine ⟨w.bypass, fun c hc => ?_⟩
  exact h a c b w.bypass w.bypass_isPath hc (Finset.mem_inter.2 ⟨ha, hb⟩)

section Leaves
variable {T : Type} (t : SimpleGraph T) {ι : Type} (sj : ι → T)

/-- The tree with one leaf `inr j` attached to `inl (sj j)` for each `j`. -/
def leafTree : SimpleGraph (T ⊕ ι) :=
  (t ⊕g (⊥ : SimpleGraph (ι))) ⊔ fromEdgeSet (Set.range fun j => s(Sum.inl (sj j), Sum.inr j))

theorem leafTree_adj_inl_inl (a b : T) : (leafTree t sj).Adj (Sum.inl a) (Sum.inl b) ↔ t.Adj a b := by
  simp [leafTree]

theorem leafTree_adj_inl_inr (j : ι) : (leafTree t sj).Adj (Sum.inl (sj j)) (Sum.inr j) := by
  simp [leafTree]

theorem leafTree_adj_inr_inl (j : ι) : (leafTree t sj).Adj (Sum.inr j) (Sum.inl (sj j)) :=
  (leafTree_adj_inl_inr t sj j).symm

/-- The embedding of `t` into the leaf tree. -/
def leafHom : t →g leafTree t sj where
  toFun := Sum.inl
  map_rel' := fun h => (leafTree_adj_inl_inl t sj _ _).2 h

/-- Lifting a walk of `t` to the leaf tree. -/
def liftWalk : ∀ {a b : T}, t.Walk a b → (leafTree t sj).Walk (Sum.inl a) (Sum.inl b)
  | _, _, .nil => .nil
  | _, _, .cons h p => .cons ((leafTree_adj_inl_inl t sj _ _).2 h) (liftWalk p)

theorem liftWalk_support : ∀ {a b : T} (w : t.Walk a b) (c : T ⊕ ι),
    c ∈ (liftWalk t sj w).support → ∃ c0 ∈ w.support, c = Sum.inl c0
  | _, _, .nil, c, hc => by
    simp [liftWalk] at hc
    exact ⟨_, by simp, hc⟩
  | _, _, .cons h p, c, hc => by
    simp only [liftWalk, Walk.support_cons, List.mem_cons] at hc
    rcases hc with hc | hc
    · exact ⟨_, by simp, hc⟩
    · obtain ⟨c0, hc0, rfl⟩ := liftWalk_support p c hc
      exact ⟨c0, by simp [hc0], rfl⟩

theorem leafTree_connected (ht : t.Connected) : (leafTree t sj).Connected := by
  have hinl : ∀ a b : T, (leafTree t sj).Reachable (Sum.inl a) (Sum.inl b) := by
    intro a b
    obtain ⟨w⟩ := ht.preconnected a b
    exact ⟨w.map (leafHom t sj)⟩
  have hall : ∀ x : T ⊕ ι, ∃ a, (leafTree t sj).Reachable x (Sum.inl a) := by
    intro x
    cases x with
    | inl a => exact ⟨a, Reachable.refl _⟩
    | inr j => exact ⟨sj j, (leafTree_adj_inr_inl t sj j).reachable⟩
  have : Nonempty T := ht.nonempty
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, ha⟩ := hall x
  obtain ⟨b, hb⟩ := hall y
  exact ha.trans ((hinl a b).trans hb.symm)

theorem leafTree_isTree [Finite T] [Finite ι] (ht : t.IsTree) : (leafTree t sj).IsTree := by
  classical
  have hT := (isTree_iff_connected_and_card.1 ht).2
  rw [isTree_iff_connected_and_card]
  refine ⟨leafTree_connected t sj ht.connected, ?_⟩
  have hfinE : (t.edgeSet).Finite := Set.toFinite _
  have h1 : Nat.card ((t ⊕g (⊥ : SimpleGraph (ι))).edgeSet) = Nat.card t.edgeSet := by
    rw [Nat.card_congr (edgeSetSumEquiv), Nat.card_sum]
    simp
  have hL : (fromEdgeSet (Set.range fun j : ι => (s(Sum.inl (sj j), Sum.inr j) : Sym2 (T ⊕ ι)))).edgeSet
      = Set.range fun j : ι => (s(Sum.inl (sj j), Sum.inr j) : Sym2 (T ⊕ ι)) := by
    rw [edgeSet_fromEdgeSet]
    ext e
    simp only [Set.mem_diff]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      obtain ⟨j, rfl⟩ := h
      simp
  have hinj : Function.Injective fun j : ι => (s(Sum.inl (sj j), Sum.inr j) : Sym2 (T ⊕ ι)) := by
    intro j k hjk
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] at hjk
    rcases hjk with ⟨_, h⟩ | h
    · exact h
    · simp at h
  have hdisj : Disjoint (t ⊕g (⊥ : SimpleGraph (ι))).edgeSet
      (Set.range fun j : ι => (s(Sum.inl (sj j), Sum.inr j) : Sym2 (T ⊕ ι))) := by
    rw [Set.disjoint_left]
    rintro e he ⟨j, rfl⟩
    simp at he
  have hfin1 : ((t ⊕g (⊥ : SimpleGraph (ι))).edgeSet).Finite := Set.toFinite _
  have hfin2 : (Set.range fun j : ι => (s(Sum.inl (sj j), Sum.inr j) : Sym2 (T ⊕ ι))).Finite :=
    Set.finite_range _
  rw [Nat.card_coe_set_eq, leafTree, edgeSet_sup, hL, Set.ncard_union_eq hdisj hfin1 hfin2,
    Set.ncard_range_of_injective hinj, ← Nat.card_coe_set_eq, h1, Nat.card_sum, ← hT]
  simp
  ring

end Leaves

section P9
variable (I : Instance) {T : Type} [Fintype T] [DecidableEq T]
  (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T)

/-- Membership of a variable of (10) in the bag of node `z`. -/
def inBag (z : T) : Var10 I T → Prop
  | .s i => Sum.inl i ∈ X' z
  | .l p q => p ∈ X' z ∧ q ∈ X' z
  | .u i z' _ => z' = z ∧ Sum.inl i ∈ X' z
  | .ut i z' _ => Sum.inl i ∈ X' z' ∧ (z' = z ∨ (z' ≠ rt ∧ par z' = z))
  | .v j z' _ => z' = z ∧ Sum.inr j ∈ X' z
  | .vt j z' _ => Sum.inr j ∈ X' z' ∧ (z' = z ∨ (z' ≠ rt ∧ par z' = z))

/-- An injective encoding of the variables into a finite type. -/
def enc10 : Var10 I T → (Fin I.n) ⊕ ((Fin I.n ⊕ Fin I.m) × (Fin I.n ⊕ Fin I.m)) ⊕
    (Bool × Fin I.n × T × Fin (nu I + 1)) ⊕ (Bool × Fin I.m × T × Fin (nv I + 1))
  | .s i => Sum.inl i
  | .l p q => Sum.inr (Sum.inl (p, q))
  | .u i z τ => Sum.inr (Sum.inr (Sum.inl (true, i, z, τ)))
  | .ut i z τ => Sum.inr (Sum.inr (Sum.inl (false, i, z, τ)))
  | .v j z τ => Sum.inr (Sum.inr (Sum.inr (true, j, z, τ)))
  | .vt j z τ => Sum.inr (Sum.inr (Sum.inr (false, j, z, τ)))

theorem enc10_inj : Function.Injective (enc10 I (T := T)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [enc10]

instance : Finite (Var10 I T) := Finite.of_injective _ (enc10_inj I)

end P9

theorem ta_prop9 :
    ∃ C : ℕ, 0 < C ∧
      ∀ (I : Instance), I.Standing →
      ∀ {T : Type} [Fintype T] [DecidableEq T]
        (t : SimpleGraph T) (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T)
        (J : Fin I.n → T → Finset (Fin I.m)) (Ip : Fin I.m → T → Finset (Fin I.n))
        (ω' : ℕ),
        IsRootedBinaryTD I t X' rt par → IsPartitionData I X' J Ip →
        (∀ z, (X' z).card ≤ ω' + 1) →
        RobertsonSeymour1986.GM5.TreewidthLE (intersectionGraph10 I X' rt par J Ip)
          (C * (ω' + 1) ^ 2 + C * (ω' + 1) * (Nat.log 2 (varthetaMax I) + 1)) := by
  classical
  refine ⟨9, by norm_num, ?_⟩
  intro I _ T _ _ t X' rt par J Ip ω' hX hJ hω
  obtain ⟨⟨htree, hvert, hedge, hpath⟩, hrt, hadj, _, hbin⟩ := hX
  have hwalks := taTD_walks_of_iii htree.connected X' hpath
  haveI : Fintype (Var10 I T) := Fintype.ofFinite _
  -- every constraint support lies in one bag
  have hsupp : ∀ k, ∃ z, ∀ x ∈ supp10 I X' rt par J Ip k, inBag I X' rt par z x := by
    intro k
    cases k with
    | a i z =>
      refine ⟨z, fun x hx => ?_⟩
      simp only [supp10] at hx
      split_ifs at hx with hi
      · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hx
        rcases hx with ⟨j, hj, rfl⟩ | ⟨τ, rfl⟩
        · exact ⟨(hJ.1 i z j hj).2.2, hi⟩
        · exact ⟨rfl, hi⟩
      · simp at hx
    | b i z =>
      refine ⟨z, fun x hx => ?_⟩
      simp only [supp10] at hx
      split_ifs at hx with hi hr
      · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_biUnion, Finset.mem_filter, Finset.mem_singleton] at hx
        rcases hx with (⟨τ, rfl⟩ | ⟨z', ⟨hz', hiz'⟩, τ, rfl⟩) | rfl
        · exact ⟨rfl, hi⟩
        · simp only [children, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
          exact ⟨hiz', Or.inr hz'⟩
        · exact hi
      · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_biUnion, Finset.mem_filter] at hx
        rcases hx with (⟨τ, rfl⟩ | ⟨z', ⟨hz', hiz'⟩, τ, rfl⟩) | ⟨τ, rfl⟩
        · exact ⟨rfl, hi⟩
        · simp only [children, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
          exact ⟨hiz', Or.inr hz'⟩
        · exact ⟨hi, Or.inl rfl⟩
      · simp at hx
    | e j z =>
      refine ⟨z, fun x hx => ?_⟩
      simp only [supp10] at hx
      split_ifs at hx with hj
      · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hx
        rcases hx with ⟨i, hi, rfl⟩ | ⟨τ, rfl⟩
        · exact ⟨(hJ.2.2.2.1 j z i hi).2.1, hj⟩
        · exact ⟨rfl, hj⟩
      · simp at hx
    | f j z =>
      refine ⟨z, fun x hx => ?_⟩
      simp only [supp10] at hx
      split_ifs at hx with hj hr
      · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_biUnion, Finset.mem_filter, Finset.notMem_empty, or_false] at hx
        rcases hx with ⟨τ, rfl⟩ | ⟨z', ⟨hz', hjz'⟩, τ, rfl⟩
        · exact ⟨rfl, hj⟩
        · simp only [children, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
          exact ⟨hjz', Or.inr hz'⟩
      · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_biUnion, Finset.mem_filter] at hx
        rcases hx with (⟨τ, rfl⟩ | ⟨z', ⟨hz', hjz'⟩, τ, rfl⟩) | ⟨τ, rfl⟩
        · exact ⟨rfl, hj⟩
        · simp only [children, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
          exact ⟨hjz', Or.inr hz'⟩
        · exact ⟨hj, Or.inl rfl⟩
      · simp at hx
    | pair z p q =>
      refine ⟨z, fun x hx => ?_⟩
      simp only [supp10] at hx
      split_ifs at hx with h
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact ⟨h.1, h.2.1⟩
        · exact ⟨h.2.1, h.1⟩
      · simp at hx
    | triple z p q x0 =>
      refine ⟨z, fun x hx => ?_⟩
      simp only [supp10] at hx
      split_ifs at hx with h
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨h.1, h.2.1⟩
        · exact ⟨h.2.1, h.2.2.1⟩
        · exact ⟨h.2.2.1, h.1⟩
      · simp at hx
  -- the bags
  let iso : Var10 I T → Prop := fun x => ∀ z, ¬ inBag I X' rt par z x
  let B : T ⊕ Var10 I T → Finset (Var10 I T) := fun a =>
    match a with
    | Sum.inl z => Finset.univ.filter (inBag I X' rt par z)
    | Sum.inr x => if iso x then {x} else ∅
  have hBl : ∀ z x, x ∈ B (Sum.inl z) ↔ inBag I X' rt par z x := by
    intro z x; simp [B]
  have hBr : ∀ y x, x ∈ B (Sum.inr y) ↔ x = y ∧ iso y := by
    intro y x
    by_cases h : iso y
    · simp [B, h]
    · simp [B, h]
  let sj : Var10 I T → T := fun _ => rt
  refine ⟨T ⊕ Var10 I T, inferInstance, leafTree t sj, B,
    ⟨leafTree_isTree t sj htree, ?_, ?_, ?_⟩, ?_⟩
  · -- cover
    intro x
    by_cases h : iso x
    · exact ⟨Sum.inr x, (hBr x x).2 ⟨rfl, h⟩⟩
    · simp only [iso, not_forall, not_not] at h
      obtain ⟨z, hz⟩ := h
      exact ⟨Sum.inl z, (hBl z x).2 hz⟩
  · -- edges
    intro x y hxy
    obtain ⟨_, k, hxk, hyk⟩ := hxy
    obtain ⟨z, hz⟩ := hsupp k
    exact ⟨Sum.inl z, (hBl z x).2 (hz x hxk), (hBl z y).2 (hz y hyk)⟩
  · -- path axiom
    apply taTD_iii_of_walks (leafTree_isTree t sj htree).isAcyclic B
    intro x a b ha hb
    cases a with
    | inr y =>
      obtain ⟨rfl, hiso⟩ := (hBr y x).1 ha
      cases b with
      | inl zb => exact absurd ((hBl zb x).1 hb) (hiso zb)
      | inr y' =>
        obtain ⟨rfl, _⟩ := (hBr y' x).1 hb
        exact ⟨Walk.nil, fun c hc => by simp at hc; subst hc; exact ha⟩
    | inl za =>
      cases b with
      | inr y =>
        obtain ⟨rfl, hiso⟩ := (hBr y x).1 hb
        exact absurd ((hBl za x).1 ha) (hiso za)
      | inl zb =>
        have ha' := (hBl za x).1 ha
        have hb' := (hBl zb x).1 hb
        -- a walk in `t` inside the node set of `x`
        suffices H : ∃ w : t.Walk za zb, ∀ c ∈ w.support, inBag I X' rt par c x by
          obtain ⟨w, hw⟩ := H
          refine ⟨liftWalk t sj w, fun c hc => ?_⟩
          obtain ⟨c0, hc0, rfl⟩ := liftWalk_support t sj w c hc
          exact (hBl c0 x).2 (hw c0 hc0)
        cases x with
        | s i => exact hwalks _ za zb ha' hb'
        | l p q =>
          obtain ⟨w0⟩ := htree.connected.preconnected za zb
          refine ⟨w0.bypass, fun c hc => ?_⟩
          have hsub := hpath za c zb w0.bypass w0.bypass_isPath hc
          exact ⟨hsub (Finset.mem_inter.2 ⟨ha'.1, hb'.1⟩), hsub (Finset.mem_inter.2 ⟨ha'.2, hb'.2⟩)⟩
        | u i z τ =>
          obtain ⟨rfl, hi⟩ := ha'
          obtain ⟨rfl, _⟩ := hb'
          exact ⟨Walk.nil, fun c hc => by simp at hc; subst hc; exact ⟨rfl, hi⟩⟩
        | v j z τ =>
          obtain ⟨rfl, hi⟩ := ha'
          obtain ⟨rfl, _⟩ := hb'
          exact ⟨Walk.nil, fun c hc => by simp at hc; subst hc; exact ⟨rfl, hi⟩⟩
        | ut i z τ =>
          obtain ⟨hiz, hza⟩ := ha'
          obtain ⟨_, hzb⟩ := hb'
          have hzz : inBag I X' rt par z (Var10.ut i z τ) := ⟨hiz, Or.inl rfl⟩
          have hzp : z ≠ rt → inBag I X' rt par (par z) (Var10.ut i z τ) :=
            fun h => ⟨hiz, Or.inr ⟨h, rfl⟩⟩
          rcases hza with rfl | ⟨hzr, rfl⟩ <;> rcases hzb with rfl | ⟨hzr', rfl⟩
          · exact ⟨Walk.nil, fun c hc => by simp at hc; subst hc; exact hzz⟩
          · refine ⟨Walk.cons (hadj _ hzr') Walk.nil, fun c hc => ?_⟩
            simp at hc; rcases hc with rfl | rfl
            · exact hzz
            · exact hzp hzr'
          · refine ⟨Walk.cons (hadj _ hzr).symm Walk.nil, fun c hc => ?_⟩
            simp at hc; rcases hc with rfl | rfl
            · exact hzp hzr
            · exact hzz
          · exact ⟨Walk.nil, fun c hc => by simp at hc; subst hc; exact hzp hzr⟩
        | vt j z τ =>
          obtain ⟨hiz, hza⟩ := ha'
          obtain ⟨_, hzb⟩ := hb'
          have hzz : inBag I X' rt par z (Var10.vt j z τ) := ⟨hiz, Or.inl rfl⟩
          have hzp : z ≠ rt → inBag I X' rt par (par z) (Var10.vt j z τ) :=
            fun h => ⟨hiz, Or.inr ⟨h, rfl⟩⟩
          rcases hza with rfl | ⟨hzr, rfl⟩ <;> rcases hzb with rfl | ⟨hzr', rfl⟩
          · exact ⟨Walk.nil, fun c hc => by simp at hc; subst hc; exact hzz⟩
          · refine ⟨Walk.cons (hadj _ hzr') Walk.nil, fun c hc => ?_⟩
            simp at hc; rcases hc with rfl | rfl
            · exact hzz
            · exact hzp hzr'
          · refine ⟨Walk.cons (hadj _ hzr).symm Walk.nil, fun c hc => ?_⟩
            simp at hc; rcases hc with rfl | rfl
            · exact hzp hzr
            · exact hzz
          · exact ⟨Walk.nil, fun c hc => by simp at hc; subst hc; exact hzp hzr⟩
  · -- width
    have hlogu : nu I ≤ Nat.log 2 (varthetaMax I) := Nat.log_mono_right (le_max_left _ _)
    have hlogv : nv I ≤ Nat.log 2 (varthetaMax I) := by
      apply Nat.log_mono_right
      have h1 : Finset.univ.sup I.θ ≤ Finset.univ.sup (fun j => I.θ j - 1) + 1 := by
        apply Finset.sup_le
        intro j _
        have := Finset.le_sup (f := fun j => I.θ j - 1) (Finset.mem_univ j)
        omega
      have h2 : Finset.univ.sup (fun j => I.θ j - 1) ≤ varthetaMax I := le_max_right _ _
      omega
    set L := Nat.log 2 (varthetaMax I) with hL
    have cu : ∀ (A B : Finset (Var10 I T)) (a b : ℕ), A.card ≤ a → B.card ≤ b →
        (A ∪ B).card ≤ a + b := fun A B a b ha hb =>
      le_trans (Finset.card_union_le A B) (Nat.add_le_add ha hb)
    let F : T → Finset (Fin I.n) := fun z => Finset.univ.filter (fun i => Sum.inl i ∈ X' z)
    let G : T → Finset (Fin I.m) := fun z => Finset.univ.filter (fun j => Sum.inr j ∈ X' z)
    have hF : ∀ z, (F z).card ≤ ω' + 1 := by
      intro z
      refine le_trans ?_ (hω z)
      rw [← Finset.card_map ⟨Sum.inl, Sum.inl_injective⟩]
      apply Finset.card_le_card
      intro v hv
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hv
      obtain ⟨i, hi, rfl⟩ := hv
      simpa [F] using hi
    have hG : ∀ z, (G z).card ≤ ω' + 1 := by
      intro z
      refine le_trans ?_ (hω z)
      rw [← Finset.card_map ⟨Sum.inr, Sum.inr_injective⟩]
      apply Finset.card_le_card
      intro v hv
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hv
      obtain ⟨j, hj, rfl⟩ := hv
      simpa [G] using hj
    intro a
    cases a with
    | inr y =>
      simp only [B]
      split_ifs <;> simp
    | inl z =>
      let Ls := (X' z ×ˢ X' z).image (fun pq => Var10.l (T := T) pq.1 pq.2)
      let Ss := (F z).image (Var10.s (T := T))
      let Uu := (F z ×ˢ (Finset.univ : Finset (Fin (nu I + 1)))).image (fun p => Var10.u p.1 z p.2)
      let Ut := (F z ×ˢ (Finset.univ : Finset (Fin (nu I + 1)))).image (fun p => Var10.ut p.1 z p.2)
      let Utc := (children rt par z).biUnion (fun z' =>
        (F z' ×ˢ (Finset.univ : Finset (Fin (nu I + 1)))).image (fun p => Var10.ut p.1 z' p.2))
      let Vv := (G z ×ˢ (Finset.univ : Finset (Fin (nv I + 1)))).image (fun p => Var10.v p.1 z p.2)
      let Vt := (G z ×ˢ (Finset.univ : Finset (Fin (nv I + 1)))).image (fun p => Var10.vt p.1 z p.2)
      let Vtc := (children rt par z).biUnion (fun z' =>
        (G z' ×ˢ (Finset.univ : Finset (Fin (nv I + 1)))).image (fun p => Var10.vt p.1 z' p.2))
      have hsub : B (Sum.inl z) ⊆ Ls ∪ Ss ∪ Uu ∪ Ut ∪ Utc ∪ Vv ∪ Vt ∪ Vtc := by
        intro x hx
        rw [hBl] at hx
        simp only [Finset.mem_union]
        cases x with
        | s i =>
          simp only [inBag] at hx
          left; left; left; left; left; left; right
          exact Finset.mem_image.2 ⟨i, by simpa [F] using hx, rfl⟩
        | l p q =>
          simp only [inBag] at hx
          left; left; left; left; left; left; left
          exact Finset.mem_image.2 ⟨(p, q), Finset.mem_product.2 hx, rfl⟩
        | u i z' τ =>
          simp only [inBag] at hx
          obtain ⟨rfl, hi⟩ := hx
          left; left; left; left; left; right
          exact Finset.mem_image.2 ⟨(i, τ), by simpa [F] using hi, rfl⟩
        | ut i z' τ =>
          simp only [inBag] at hx
          obtain ⟨hi, rfl | ⟨hr, hp⟩⟩ := hx
          · left; left; left; left; right
            exact Finset.mem_image.2 ⟨(i, τ), by simpa [F] using hi, rfl⟩
          · left; left; left; right
            refine Finset.mem_biUnion.2 ⟨z', ?_, Finset.mem_image.2 ⟨(i, τ), by simpa [F] using hi, rfl⟩⟩
            simp [children, hr, hp]
        | v j z' τ =>
          simp only [inBag] at hx
          obtain ⟨rfl, hj⟩ := hx
          left; left; right
          exact Finset.mem_image.2 ⟨(j, τ), by simpa [G] using hj, rfl⟩
        | vt j z' τ =>
          simp only [inBag] at hx
          obtain ⟨hj, rfl | ⟨hr, hp⟩⟩ := hx
          · left; right
            exact Finset.mem_image.2 ⟨(j, τ), by simpa [G] using hj, rfl⟩
          · right
            refine Finset.mem_biUnion.2 ⟨z', ?_, Finset.mem_image.2 ⟨(j, τ), by simpa [G] using hj, rfl⟩⟩
            simp [children, hr, hp]
      have hch : (children rt par z).card ≤ 2 := hbin z
      have bU : ∀ z', ((F z' ×ˢ (Finset.univ : Finset (Fin (nu I + 1)))).image
          (fun p => Var10.ut (T := T) p.1 z' p.2)).card ≤ (ω' + 1) * (nu I + 1) := by
        intro z'
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
        exact Nat.mul_le_mul_right _ (hF z')
      have bV : ∀ z', ((G z' ×ˢ (Finset.univ : Finset (Fin (nv I + 1)))).image
          (fun p => Var10.vt (T := T) p.1 z' p.2)).card ≤ (ω' + 1) * (nv I + 1) := by
        intro z'
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
        exact Nat.mul_le_mul_right _ (hG z')
      have b1 : Ls.card ≤ (ω' + 1) * (ω' + 1) := by
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_product]
        exact Nat.mul_le_mul (hω z) (hω z)
      have b2 : Ss.card ≤ ω' + 1 := le_trans Finset.card_image_le (hF z)
      have b3 : Uu.card ≤ (ω' + 1) * (nu I + 1) := by
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
        exact Nat.mul_le_mul_right _ (hF z)
      have b4 : Ut.card ≤ (ω' + 1) * (nu I + 1) := bU z
      have b5 : Utc.card ≤ 2 * ((ω' + 1) * (nu I + 1)) := by
        refine le_trans Finset.card_biUnion_le ?_
        refine le_trans (Finset.sum_le_card_nsmul _ _ ((ω' + 1) * (nu I + 1)) (fun z' _ => bU z')) ?_
        rw [smul_eq_mul]
        exact Nat.mul_le_mul_right _ hch
      have b6 : Vv.card ≤ (ω' + 1) * (nv I + 1) := by
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
        exact Nat.mul_le_mul_right _ (hG z)
      have b7 : Vt.card ≤ (ω' + 1) * (nv I + 1) := by
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
        exact Nat.mul_le_mul_right _ (hG z)
      have b8 : Vtc.card ≤ 2 * ((ω' + 1) * (nv I + 1)) := by
        refine le_trans Finset.card_biUnion_le ?_
        refine le_trans (Finset.sum_le_card_nsmul _ _ ((ω' + 1) * (nv I + 1)) (fun z' _ => bV z')) ?_
        rw [smul_eq_mul]
        exact Nat.mul_le_mul_right _ hch
      have htot := cu _ _ _ _ (cu _ _ _ _ (cu _ _ _ _ (cu _ _ _ _ (cu _ _ _ _ (cu _ _ _ _
        (cu _ _ _ _ b1 b2) b3) b4) b5) b6) b7) b8
      refine le_trans (Finset.card_le_card hsub) (le_trans htot ?_)
      have hu : (ω' + 1) * (nu I + 1) ≤ (ω' + 1) * (L + 1) := Nat.mul_le_mul_left _ (by omega)
      have hv : (ω' + 1) * (nv I + 1) ≤ (ω' + 1) * (L + 1) := Nat.mul_le_mul_left _ (by omega)
      have ha : ω' + 1 ≤ (ω' + 1) * (ω' + 1) := Nat.le_mul_of_pos_left _ (by omega)
      have e1 : (ω' + 1) ^ 2 = (ω' + 1) * (ω' + 1) := by ring
      have e2 : 9 * (ω' + 1) * (L + 1) = 9 * ((ω' + 1) * (L + 1)) := by ring
      rw [e1, e2]
      omega

end TraceAdopt.LPReform

open TraceAdopt.LPReform in
theorem solution :
    ∃ C : ℕ, 0 < C ∧
      ∀ (I : Instance), I.Standing →
      ∀ {T : Type} [Fintype T] [DecidableEq T]
        (t : SimpleGraph T) (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T)
        (J : Fin I.n → T → Finset (Fin I.m)) (Ip : Fin I.m → T → Finset (Fin I.n))
        (ω' : ℕ),
        IsRootedBinaryTD I t X' rt par → IsPartitionData I X' J Ip →
        (∀ z, (X' z).card ≤ ω' + 1) →
        RobertsonSeymour1986.GM5.TreewidthLE (intersectionGraph10 I X' rt par J Ip)
          (C * (ω' + 1) ^ 2 + C * (ω' + 1) * (Nat.log 2 (varthetaMax I) + 1)) :=
  ta_prop9
