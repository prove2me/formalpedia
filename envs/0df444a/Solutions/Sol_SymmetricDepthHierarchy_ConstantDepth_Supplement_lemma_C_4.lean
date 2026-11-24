-- Prove2me | solution 1 for SymmetricDepthHierarchy.ConstantDepth.Supplement.lemma_C_4
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T17:39:49.203473+00:00
-- url     : https://prove2.me/submissions/c79b2389-6bb9-490e-806c-8835614e774f

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Paths

set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

section aux
variable {W : Type} [Fintype W] {G : SimpleGraph W} {T : Type}

def Anc (D : TreeDecomp G T) (s t : T) : Prop :=
  Relation.ReflTransGen (fun a b => b ≠ D.root ∧ D.parent b = a) s t

def UP (D : TreeDecomp G T) (t : T) : Finset W :=
  Finset.univ.filter (fun v => ∃ s, Anc D s t ∧ v ∈ D.bag s)

lemma anc_cases (D : TreeDecomp G T) (t s : T) (ht : t ≠ D.root) :
    Anc D s t ↔ s = t ∨ Anc D s (D.parent t) := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with h | ⟨b, hb, hr⟩
    · left; exact h.symm
    · right; rw [hr.2]; exact hb
  · rintro (rfl | h)
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail h ⟨ht, rfl⟩

lemma anc_root (D : TreeDecomp G T) (s : T) (h : Anc D s D.root) : s = D.root := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨b, _, hr⟩
  · exact h.symm
  · exact absurd rfl hr.1

lemma anc_level (D : TreeDecomp G T) (s t : T) (h : Anc D s t) : D.level s ≤ D.level t := by
  induction h with
  | refl => exact le_refl _
  | tail _ hr ih =>
    have := D.level_parent _ hr.1
    rw [hr.2] at this
    omega

lemma anc_refl (D : TreeDecomp G T) (t : T) : Anc D t t := Relation.ReflTransGen.refl

lemma anc_step (D : TreeDecomp G T) (t : T) (ht : t ≠ D.root) : Anc D (D.parent t) t :=
  Relation.ReflTransGen.single ⟨ht, rfl⟩

lemma anc_trans (D : TreeDecomp G T) {a b c : T} (h1 : Anc D a b) (h2 : Anc D b c) : Anc D a c :=
  Relation.ReflTransGen.trans h1 h2

lemma level_parent_lt (D : TreeDecomp G T) (t : T) (ht : t ≠ D.root) :
    D.level (D.parent t) < D.level t := by
  have := D.level_parent t ht; omega

lemma UP_root (D : TreeDecomp G T) : UP D D.root = D.bag D.root := by
  ext v
  simp only [UP, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨s, hs, hv⟩
    rw [anc_root D s hs] at hv; exact hv
  · intro hv; exact ⟨D.root, anc_refl D _, hv⟩

lemma UP_succ (D : TreeDecomp G T) (t : T) (ht : t ≠ D.root) :
    UP D t = UP D (D.parent t) ∪ D.bag t := by
  ext v
  simp only [UP, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨s, hs, hv⟩
    rcases (anc_cases D t s ht).1 hs with rfl | h
    · right; exact hv
    · left; exact ⟨s, h, hv⟩
  · rintro (⟨s, hs, hv⟩ | hv)
    · exact ⟨s, (anc_cases D t s ht).2 (Or.inr hs), hv⟩
    · exact ⟨t, anc_refl D _, hv⟩

lemma card_UP_le (D : TreeDecomp G T) (K : ℕ) (hb : ∀ t, (D.bag t).card ≤ K)
    (hr : D.bag D.root = ∅) : ∀ n t, D.level t = n → (UP D t).card ≤ n * K := by
  intro n
  induction n with
  | zero =>
    intro t ht
    have : t = D.root := by
      by_contra hne
      have := D.level_parent t hne; omega
    subst this
    rw [UP_root, hr]; simp
  | succ n ih =>
    intro t ht
    have hne : t ≠ D.root := by
      rintro rfl; rw [D.level_root] at ht; omega
    have hp : D.level (D.parent t) = n := by
      have := D.level_parent t hne; omega
    rw [UP_succ D t hne]
    calc _ ≤ (UP D (D.parent t)).card + (D.bag t).card := Finset.card_union_le _ _
      _ ≤ n * K + K := Nat.add_le_add (ih _ hp) (hb t)
      _ = (n + 1) * K := by ring

/-! Part 2 -/

lemma exists_top (D : TreeDecomp G T) [Fintype T] (v : W) (t0 : T) (h0 : v ∈ D.bag t0) :
    ∃ u0, v ∈ D.bag u0 ∧ ∀ u, v ∈ D.bag u → D.level u0 ≤ D.level u := by
  obtain ⟨u0, hu0, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun u => v ∈ D.bag u))
    D.level ⟨t0, by simpa using h0⟩
  refine ⟨u0, by simpa using hu0, fun u hu => hmin u (by simpa using hu)⟩

lemma top_prop (D : TreeDecomp G T) (v : W) (u0 : T) (h0 : v ∈ D.bag u0)
    (hmin : ∀ u, v ∈ D.bag u → D.level u0 ≤ D.level u) :
    ∀ u, v ∈ D.bag u → Anc D u0 u ∧ ∀ s, Anc D u0 s → Anc D s u → v ∈ D.bag s := by
  have hconn := (D.connected v).preconnected
  intro u hu
  suffices H : ∀ y : {t // v ∈ D.bag t}, Relation.ReflTransGen
      (fun a b => (SimpleGraph.induce {t | v ∈ D.bag t} (RootedTree.graph D.toRootedTree)).Adj a b)
      ⟨u0, h0⟩ y → Anc D u0 y.1 ∧ ∀ s, Anc D u0 s → Anc D s y.1 → v ∈ D.bag s by
    have hR := hconn ⟨u0, h0⟩ ⟨u, hu⟩
    rw [SimpleGraph.reachable_iff_reflTransGen] at hR
    exact H _ hR
  intro y hR
  induction hR with
  | refl =>
    refine ⟨anc_refl D _, fun s h1 h2 => ?_⟩
    by_cases hr : u0 = D.root
    · subst hr; rw [anc_root D s h2] at *; exact h0
    · rcases (anc_cases D u0 s hr).1 h2 with rfl | h
      · exact h0
      · have := anc_level D _ _ h
        have := anc_level D _ _ h1
        have := level_parent_lt D u0 hr
        omega
  | @tail b c _ hadj ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hadj' : (b.1 ≠ D.root ∧ D.parent b.1 = c.1) ∨ (c.1 ≠ D.root ∧ D.parent c.1 = b.1) := by
      have := hadj
      simp only [SimpleGraph.comap_adj, SimpleGraph.induce, RootedTree.graph,
        SimpleGraph.fromRel_adj] at this
      exact this.2
    rcases hadj' with ⟨hb, hp⟩ | ⟨hc, hp⟩
    · have hbne : b.1 ≠ u0 := by
        rintro h
        have := hmin c.1 c.2
        have := level_parent_lt D b.1 hb
        rw [hp] at this
        rw [h] at this
        omega
      have hanc : Anc D u0 c.1 := by
        rcases (anc_cases D b.1 u0 hb).1 ih1 with h | h
        · exact absurd h.symm hbne
        · rw [← hp]; exact h
      refine ⟨hanc, fun s h1 h2 => ih2 s h1 ?_⟩
      have h3 : Anc D (D.parent b.1) b.1 := anc_step D b.1 hb
      rw [hp] at h3
      exact anc_trans D h2 h3
    · refine ⟨Relation.ReflTransGen.tail ih1 ⟨hc, hp⟩, fun s h1 h2 => ?_⟩
      rcases (anc_cases D c.1 s hc).1 h2 with rfl | h
      · exact c.2
      · rw [hp] at h; exact ih2 s h1 h

lemma lemmaB (D : TreeDecomp G T) [Fintype T] (t s : T) (ht : t ≠ D.root) (v : W)
    (hvt : v ∈ D.bag t) (hvs : v ∈ D.bag s) (hs : Anc D s (D.parent t)) : v ∈ D.bag (D.parent t) := by
  obtain ⟨u0, h0, hmin⟩ := exists_top D v t hvt
  have hs' := (top_prop D v u0 h0 hmin s hvs).1
  have := (top_prop D v u0 h0 hmin t hvt).2 (D.parent t) (anc_trans D hs' hs) (anc_step D t ht)
  exact this

def pb (D : TreeDecomp G T) (t : T) : Finset W := if t = D.root then ∅ else D.bag (D.parent t)

def Ess (D : TreeDecomp G T) (t : T) : Prop := ¬ D.bag t ⊆ pb D t

def up (D : TreeDecomp G T) (t : T) : Option {t : T // Ess D t} :=
  if h : Ess D t then some ⟨t, h⟩ else if ht : t = D.root then none else up D (D.parent t)
termination_by D.level t
decreasing_by
  have := D.level_parent t ht; omega

lemma up_anc (D : TreeDecomp G T) : ∀ n t, D.level t = n → ∀ a, up D t = some a → Anc D a.1 t := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t htn a ha
    rw [up] at ha
    by_cases h : Ess D t
    · rw [dif_pos h] at ha
      cases ha; exact anc_refl D _
    · rw [dif_neg h] at ha
      by_cases hr : t = D.root
      · rw [dif_pos hr] at ha; cases ha
      · rw [dif_neg hr] at ha
        have := ih _ (by have := level_parent_lt D t hr; omega) (D.parent t) rfl a ha
        exact anc_trans D this (anc_step D t hr)

lemma up_bag (D : TreeDecomp G T) : ∀ n t, D.level t = n → ∀ X : Finset W, X.Nonempty →
    X ⊆ D.bag t → ∃ a, up D t = some a ∧ X ⊆ D.bag a.1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t htn X hX hXt
    by_cases h : Ess D t
    · exact ⟨⟨t, h⟩, by rw [up, dif_pos h], hXt⟩
    · have h' : D.bag t ⊆ pb D t := by simpa [Ess] using h
      have hr : t ≠ D.root := by
        rintro rfl
        simp [pb] at h'
        obtain ⟨x, hx⟩ := hX
        have := hXt hx
        rw [h'] at this
        simp at this
      have hXp : X ⊆ D.bag (D.parent t) := by
        intro x hx
        have := h' (hXt hx)
        simpa [pb, hr] using this
      obtain ⟨a, ha, hXa⟩ := ih _ (by have := level_parent_lt D t hr; omega) (D.parent t) rfl X hX hXp
      refine ⟨a, ?_, hXa⟩
      rw [up.eq_1 D t, dif_neg h, dif_neg hr]; exact ha

def lv (D : TreeDecomp G T) (t : T) : ℕ :=
  (if Ess D t then 1 else 0) + (if h : t = D.root then 0 else lv D (D.parent t))
termination_by D.level t
decreasing_by have := D.level_parent t h; omega

def lvo (D : TreeDecomp G T) : Option {t : T // Ess D t} → ℕ
  | none => 0
  | some a => lv D a.1

lemma lv_up (D : TreeDecomp G T) : ∀ n t, D.level t = n → lvo D (up D t) = lv D t := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t htn
    by_cases h : Ess D t
    · rw [up.eq_1 D t, dif_pos h]; rfl
    · by_cases hr : t = D.root
      · subst hr
        rw [up.eq_1 D _, dif_neg h, dif_pos rfl, lv.eq_1 D _]
        simp [lvo, h]
      · rw [up.eq_1 D t, dif_neg h, dif_neg hr, lv.eq_1 D t]
        rw [ih _ (by have := level_parent_lt D t hr; omega) (D.parent t) rfl]
        simp [h, hr]

lemma lv_le (D : TreeDecomp G T) [Fintype T] : ∀ n t, D.level t = n → lv D t ≤ (UP D t).card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t htn
    rw [lv.eq_1 D t]
    by_cases hr : t = D.root
    · subst hr
      rw [UP_root]
      by_cases h : Ess D D.root
      · have : (D.bag D.root).Nonempty := by
          by_contra hne
          rw [Finset.not_nonempty_iff_eq_empty] at hne
          apply h; rw [hne]; exact Finset.empty_subset _
        simp [h]; exact this
      · simp [h]
    · rw [dif_neg hr]
      have ih' := ih _ (by have := level_parent_lt D t hr; omega) (D.parent t) rfl
      rw [UP_succ D t hr]
      by_cases h : Ess D t
      · simp only [if_pos h]
        have h' : ¬ D.bag t ⊆ D.bag (D.parent t) := by simpa [Ess, pb, hr] using h
        rw [Finset.not_subset] at h'
        obtain ⟨v, hv, hvn⟩ := h'
        have hvU : v ∉ UP D (D.parent t) := by
          intro hm
          simp only [UP, Finset.mem_filter, Finset.mem_univ, true_and] at hm
          obtain ⟨s, hs, hvs⟩ := hm
          exact hvn (lemmaB D t s hr v hv hvs hs)
        have : insert v (UP D (D.parent t)) ⊆ UP D (D.parent t) ∪ D.bag t := by
          intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact Finset.mem_union_right _ hv
          · exact Finset.mem_union_left _ hx
        have h2 := Finset.card_le_card this
        rw [Finset.card_insert_of_notMem hvU] at h2
        omega
      · simp only [if_neg h]
        have := Finset.card_le_card (Finset.subset_union_left (s₁ := UP D (D.parent t)) (s₂ := D.bag t))
        omega

def RT' (D : TreeDecomp G T) : RootedTree (Option {t : T // Ess D t}) where
  root := none
  parent := fun x => match x with
    | none => none
    | some a => if a.1 = D.root then none else up D (D.parent a.1)
  level := lvo D
  level_root := rfl
  level_parent := by
    intro x hx
    cases x with
    | none => exact absurd rfl hx
    | some a =>
      by_cases hr : a.1 = D.root
      · simp only [hr, if_true]
        show lv D a.1 = 0 + 1
        have h2 : Ess D D.root := hr ▸ a.2
        rw [lv.eq_1 D a.1]
        simp [a.2, hr, h2]
      · simp only [hr, if_false]
        rw [lv_up D _ _ rfl]
        show lv D a.1 = _
        rw [lv.eq_1 D a.1]
        simp [a.2, hr]
        omega

def bag' (D : TreeDecomp G T) : Option {t : T // Ess D t} → Finset W
  | none => ∅
  | some a => D.bag a.1

lemma ess_top (D : TreeDecomp G T) (v : W) (u0 : T) (h0 : v ∈ D.bag u0)
    (hmin : ∀ u, v ∈ D.bag u → D.level u0 ≤ D.level u) : Ess D u0 := by
  intro hsub
  have := hsub h0
  by_cases hr : u0 = D.root
  · simp [pb, hr] at this
  · simp only [pb, hr, if_false] at this
    have h1 := hmin _ this
    have h2 := level_parent_lt D u0 hr
    omega

lemma RT'_conn (D : TreeDecomp G T) [Fintype T] (v : W) (hv : ∃ t, v ∈ D.bag t) :
    ((RT' D).graph.induce {x | v ∈ bag' D x}).Connected := by
  obtain ⟨t0, ht0⟩ := hv
  obtain ⟨u0, h0, hmin⟩ := exists_top D v t0 ht0
  have hess := ess_top D v u0 h0 hmin
  let x0 : {x : Option {t : T // Ess D t} | v ∈ bag' D x} := ⟨some ⟨u0, hess⟩, h0⟩
  have key : ∀ n (a : {t : T // Ess D t}) (ha : v ∈ D.bag a.1), D.level a.1 = n →
      ((RT' D).graph.induce {x | v ∈ bag' D x}).Reachable ⟨some a, ha⟩ x0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a ha han
      by_cases hu : a.1 = u0
      · have : (⟨some a, ha⟩ : {x : Option {t : T // Ess D t} | v ∈ bag' D x}) = x0 :=
          Subtype.ext (congrArg some (Subtype.ext hu))
        rw [this]
      · obtain ⟨hanc, hint⟩ := top_prop D v u0 h0 hmin a.1 ha
        have hr : a.1 ≠ D.root := by
          intro hr
          rw [hr] at hanc
          exact hu (by rw [hr]; exact (anc_root D _ hanc).symm)
        have hanc' := ((anc_cases D a.1 u0 hr).1 hanc).resolve_left (Ne.symm hu)
        have hp : v ∈ D.bag (D.parent a.1) := hint _ hanc' (anc_step D a.1 hr)
        obtain ⟨b, hb, hXb⟩ := up_bag D _ _ rfl {v} (Finset.singleton_nonempty v)
          (by simpa using hp)
        have hbv : v ∈ D.bag b.1 := hXb (Finset.mem_singleton_self v)
        have hba := up_anc D _ _ rfl b hb
        have hl1 := anc_level D _ _ hba
        have hl2 := level_parent_lt D a.1 hr
        have hne : b.1 ≠ a.1 := by
          intro h; rw [h] at hl1; omega
        have hadj : ((RT' D).graph.induce {x | v ∈ bag' D x}).Adj ⟨some a, ha⟩ ⟨some b, hbv⟩ := by
          simp only [SimpleGraph.comap_adj, SimpleGraph.induce, RootedTree.graph,
            SimpleGraph.fromRel_adj]
          refine ⟨?_, Or.inl ⟨by simp [RT'], ?_⟩⟩
          · intro h
            exact hne (congrArg Subtype.val (Option.some.inj h)).symm
          · simp [RT', hr, hb]
        exact hadj.reachable.trans (ih _ (by omega) b hbv rfl)
  have hx : ∀ x : {x : Option {t : T // Ess D t} | v ∈ bag' D x}, 
      ((RT' D).graph.induce {x | v ∈ bag' D x}).Reachable x x0 := by
    rintro ⟨x, hx⟩
    cases x with
    | none => exact absurd hx (by simp [bag'])
    | some a => exact key _ a hx rfl
  rw [SimpleGraph.connected_iff]
  exact ⟨fun x y => (hx x).trans (hx y).symm, ⟨x0⟩⟩

def mkD (D : TreeDecomp G T) [Fintype T] : TreeDecomp G (Option {t : T // Ess D t}) where
  toRootedTree := RT' D
  bag := bag' D
  cover_vertex := by
    intro v
    obtain ⟨t0, ht0⟩ := D.cover_vertex v
    obtain ⟨u0, h0, hmin⟩ := exists_top D v t0 ht0
    exact ⟨some ⟨u0, ess_top D v u0 h0 hmin⟩, h0⟩
  cover_edge := by
    intro u v huv
    obtain ⟨t, hu, hv⟩ := D.cover_edge u v huv
    obtain ⟨b, _, hX⟩ := up_bag D _ t rfl {u, v} (by simp) (by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hu
      · rw [Finset.mem_singleton.1 hx]; exact hv)
    exact ⟨some b, hX (by simp), hX (by simp)⟩
  connected := fun v => RT'_conn D v (D.cover_vertex v)

end aux


theorem lemma_C_4_aux (K Δ q : ℕ) (hK : 1 ≤ K) (hΔ : 1 ≤ Δ) (hq : 1 ≤ q)
    (F : FinGraph) :
    (FWLe F.G Δ (K-1) → inT F.G K (Δ*K)) ∧
    (inT F.G K q → FWLe F.G q (K-1)) := by
  constructor
  · rintro ⟨T, hT, D, hl, hr, hb⟩
    have e : ∀ t, (Finset.univ.filter (fun v => ∃ s,
        Relation.ReflTransGen (fun a b => b ≠ D.root ∧ D.parent b = a) s t ∧ v ∈ D.bag s)) = UP D t :=
      fun t => by unfold UP Anc; congr
    refine ⟨T, hT, D, fun t => by have := hb t; omega, fun t => ?_⟩
    have h1 := card_UP_le D K (fun t => by have := hb t; omega) hr _ t rfl
    have h2 := hl t
    rw [e t]
    exact le_trans h1 (Nat.mul_le_mul_right K h2)
  · rintro ⟨T, hT, D, hb, hq'⟩
    have e : ∀ t, (Finset.univ.filter (fun v => ∃ s,
        Relation.ReflTransGen (fun a b => b ≠ D.root ∧ D.parent b = a) s t ∧ v ∈ D.bag s)) = UP D t :=
      fun t => by unfold UP Anc; congr
    refine ⟨Option {t : T // Ess D t}, inferInstance, mkD D, ?_, rfl, ?_⟩
    · intro x
      cases x with
      | none => exact Nat.zero_le _
      | some a =>
        have := hq' a.1
        rw [e] at this
        exact le_trans (lv_le D _ a.1 rfl) this
    · intro x
      cases x with
      | none => simp [mkD, bag']
      | some a =>
        have := hb a.1
        show (D.bag a.1).card ≤ K - 1 + 1
        omega

end SymmetricDepthHierarchy.ConstantDepth.Supplement

open SymmetricDepthHierarchy.ConstantDepth SymmetricDepthHierarchy.ConstantDepth.Supplement in
theorem solution (K Δ q : ℕ) (hK : 1 ≤ K) (hΔ : 1 ≤ Δ) (hq : 1 ≤ q)
    (F : FinGraph) :
    (FWLe F.G Δ (K-1) → inT F.G K (Δ*K)) ∧
    (inT F.G K q → FWLe F.G q (K-1)) := lemma_C_4_aux K Δ q hK hΔ hq F
