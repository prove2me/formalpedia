-- Prove2me | solution 1 for RuralPostman.NPC.claim_directed
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:24:15.238868+00:00
-- url     : https://prove2.me/submissions/55587bbc-bfbd-49ba-9efb-2fbecb777331

import Mathlib
import Definitions.Def_RuralPostman_NPC_Reductions

open RuralPostman.NPC

namespace RPAux

theorem finRotate_val {n : ℕ} (i : Fin n) : (finRotate n i).val = (i.val + 1) % n := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    rw [coe_finRotate]
    split_ifs with h
    · subst h; simp
    · have : i.val + 1 < n + 1 := by
        have := Fin.val_lt_last h; omega
      rw [Nat.mod_eq_of_lt this]

theorem countP_eq_sum {α : Type*} (p : α → Bool) : ∀ l : List α,
    l.countP p = ∑ i : Fin l.length, if p (l.get i) = true then 1 else 0
  | [] => by simp
  | a :: l => by
    rw [List.countP_cons, countP_eq_sum p l]
    show _ = ∑ i : Fin (l.length + 1), _
    rw [Fin.sum_univ_succ, add_comm]
    congr 1

theorem countP_ofFn {α : Type*} (p : α → Bool) : ∀ {N : ℕ} (g : Fin N → α),
    (List.ofFn g).countP p = ∑ j, if p (g j) = true then 1 else 0
  | 0, g => by simp
  | N+1, g => by
    rw [List.ofFn_succ, List.countP_cons, countP_ofFn p, Fin.sum_univ_succ]
    simp [add_comm]

theorem closure (I : RPInstance) (τ : List I.Traversal)
    (hc : ∀ i : Fin τ.length, I.trDst (τ.get i) = I.trSrc (τ.get (finRotate τ.length i)))
    (Q : Fin I.n → Prop) (hQ : ∀ t ∈ τ, Q (I.trSrc t) → Q (I.trDst t))
    (t0 : I.Traversal) (ht0 : t0 ∈ τ) (h0 : Q (I.trSrc t0)) : ∀ t ∈ τ, Q (I.trSrc t) := by
  obtain ⟨j, rfl⟩ := List.mem_iff_get.1 ht0
  have hL : 0 < τ.length := by have := j.isLt; omega
  have key : ∀ m : ℕ, Q (I.trSrc (τ.get ⟨(j.val + m) % τ.length, Nat.mod_lt _ hL⟩)) := by
    intro m
    induction m with
    | zero => simpa [Nat.mod_eq_of_lt j.isLt] using h0
    | succ m ih =>
      have h1 := hc ⟨(j.val + m) % τ.length, Nat.mod_lt _ hL⟩
      have e : finRotate τ.length ⟨(j.val + m) % τ.length, Nat.mod_lt _ hL⟩ =
          ⟨(j.val + (m+1)) % τ.length, Nat.mod_lt _ hL⟩ := by
        ext; rw [finRotate_val]; simp only; rw [Nat.mod_add_mod]; ring_nf
      rw [e] at h1; rw [← h1]
      exact hQ _ (List.get_mem _ _) ih
  intro t ht
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 ht
  have := key (i.val + τ.length - j.val)
  have e : (j.val + (i.val + τ.length - j.val)) % τ.length = i.val := by
    have : j.val + (i.val + τ.length - j.val) = i.val + τ.length := by have := j.isLt; omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
  have e2 : (⟨(j.val + (i.val + τ.length - j.val)) % τ.length, Nat.mod_lt _ hL⟩ : Fin τ.length)
      = i := Fin.ext e
  rwa [e2] at this

theorem ham_of_next {v : ℕ} (adj : Fin v → Fin v → Bool) (next : Fin v → Fin v)
    (hinj : Function.Injective next) (hadj : ∀ x, adj x (next x) = true) (x0 : Fin v)
    (horb : ∀ x, ∃ m, next^[m] x0 = x) : SchedComplexity.NoWait.HasHamiltonCircuit adj := by
  have hper := hinj.mem_periodicPts x0
  have hp0 : 0 < Function.minimalPeriod next x0 :=
    Function.minimalPeriod_pos_of_mem_periodicPts hper
  have hpv : Function.minimalPeriod next x0 ≤ v := by
    have : Function.Injective
        (fun m : Fin (Function.minimalPeriod next x0) => next^[m.val] x0) := by
      intro a b h
      exact Fin.ext (Function.iterate_injOn_Iio_minimalPeriod a.isLt b.isLt h)
    simpa using Fintype.card_le_of_injective _ this
  have hvp : v ≤ Function.minimalPeriod next x0 := by
    have : Function.Surjective
        (fun m : Fin (Function.minimalPeriod next x0) => next^[m.val] x0) := by
      intro x
      obtain ⟨m, rfl⟩ := horb x
      exact ⟨⟨m % _, Nat.mod_lt _ hp0⟩, Function.iterate_mod_minimalPeriod_eq⟩
    simpa using Fintype.card_le_of_surjective _ this
  have hpe : Function.minimalPeriod next x0 = v := le_antisymm hpv hvp
  have hσinj : Function.Injective (fun i : Fin v => next^[i.val] x0) := by
    intro a b h
    have ha : a.val ∈ Set.Iio (Function.minimalPeriod next x0) := by
      simp only [Set.mem_Iio]; omega
    have hb : b.val ∈ Set.Iio (Function.minimalPeriod next x0) := by
      simp only [Set.mem_Iio]; omega
    exact Fin.ext (Function.iterate_injOn_Iio_minimalPeriod ha hb h)
  refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hσinj), fun i => ?_⟩
  simp only [Equiv.ofBijective_apply]
  have h2 : next^[(i.val + 1) % Function.minimalPeriod next x0] x0 = next^[i.val + 1] x0 :=
    Function.iterate_mod_minimalPeriod_eq
  rw [hpe] at h2
  rw [finRotate_val, h2, Function.iterate_succ_apply']
  exact hadj _

theorem ca_ne_na {v : ℕ} (a b : Fin v) : Fin.castAdd v a ≠ Fin.natAdd v b := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem na_ne_ca {v : ℕ} (a b : Fin v) : Fin.natAdd v a ≠ Fin.castAdd v b :=
  fun h => ca_ne_na b a h.symm

end RPAux

namespace RPAux

/-- the block tour: position `3q + r` holds `![R q, B q, E q] r`. -/
def blk {α : Type*} {v : ℕ} (R B E : Fin v → α) (j : Fin (v * 3)) : α :=
  if j.val % 3 = 0 then R ⟨j.val / 3, by have := j.isLt; omega⟩
  else if j.val % 3 = 1 then B ⟨j.val / 3, by have := j.isLt; omega⟩
  else E ⟨j.val / 3, by have := j.isLt; omega⟩

theorem blk_fpfe {α : Type*} {v : ℕ} (R B E : Fin v → α) (i : Fin v) (r : Fin 3) :
    blk R B E (finProdFinEquiv (i, r)) = ![R i, B i, E i] r := by
  have hv : (finProdFinEquiv (i, r) : Fin (v * 3)).val = r.val + 3 * i.val := by
    simp [finProdFinEquiv]
  have hq : (⟨(finProdFinEquiv (i, r) : Fin (v * 3)).val / 3,
      by have := (finProdFinEquiv (i, r) : Fin (v * 3)).isLt; omega⟩ : Fin v) = i := by
    ext; simp only [hv]; have := r.isLt; omega
  unfold blk
  fin_cases r
  · rw [if_pos (by simp only [hv]; omega)]
    simp only [hq]; rfl
  · rw [if_neg (by simp only [hv]; omega), if_pos (by simp only [hv]; omega)]
    simp only [hq]; rfl
  · rw [if_neg (by simp only [hv]; omega), if_neg (by simp only [hv]; omega)]
    simp only [hq]; rfl

theorem sum_blk {α : Type*} {v : ℕ} (R B E : Fin v → α) (F : α → ℕ) :
    ∑ j : Fin (v * 3), F (blk R B E j) = ∑ i : Fin v, (F (R i) + F (B i) + F (E i)) := by
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fin.sum_univ_three, blk_fpfe, blk_fpfe, blk_fpfe]
  rfl

theorem countP_blk {α : Type*} {v : ℕ} (R B E : Fin v → α) (p : α → Bool) :
    (List.ofFn (blk R B E)).countP p = ∑ i : Fin v,
      ((if p (R i) = true then 1 else 0) + (if p (B i) = true then 1 else 0) +
        (if p (E i) = true then 1 else 0)) := by
  rw [countP_ofFn]
  exact sum_blk R B E (fun t => if p t = true then 1 else 0)

theorem cyc_blk (I : RPInstance) {v : ℕ} (R B E : Fin v → I.Traversal)
    (h1 : ∀ i, I.trDst (R i) = I.trSrc (B i)) (h2 : ∀ i, I.trDst (B i) = I.trSrc (E i))
    (h3 : ∀ i, I.trDst (E i) = I.trSrc (R (finRotate v i))) :
    ∀ i : Fin (List.ofFn (blk R B E)).length,
      I.trDst ((List.ofFn (blk R B E)).get i) =
        I.trSrc ((List.ofFn (blk R B E)).get (finRotate _ i)) := by
  have H1 : ∀ a b : Fin v, a.val = b.val → I.trDst (R a) = I.trSrc (B b) := by
    intro a b h; rw [Fin.ext h]; exact h1 b
  have H2 : ∀ a b : Fin v, a.val = b.val → I.trDst (B a) = I.trSrc (E b) := by
    intro a b h; rw [Fin.ext h]; exact h2 b
  have H3 : ∀ a b : Fin v, (a.val + 1 < v ∧ b.val = a.val + 1) ∨ (a.val + 1 = v ∧ b.val = 0) →
      I.trDst (E a) = I.trSrc (R b) := by
    intro a b h
    have : b = finRotate v a := by
      ext; rw [finRotate_val]
      rcases h with ⟨h, h'⟩ | ⟨h, h'⟩
      · rw [h', Nat.mod_eq_of_lt h]
      · rw [h', h, Nat.mod_self]
    rw [this]; exact h3 a
  have key : ∀ j : Fin (v * 3), I.trDst (blk R B E j) = I.trSrc (blk R B E (finRotate _ j)) := by
    intro j
    have hj := j.isLt
    have hrot : (j.val + 1 < v * 3 ∧ (finRotate (v * 3) j).val = j.val + 1) ∨
        (j.val + 1 = v * 3 ∧ (finRotate (v * 3) j).val = 0) := by
      rw [finRotate_val]
      by_cases h : j.val + 1 < v * 3
      · left; exact ⟨h, Nat.mod_eq_of_lt h⟩
      · right
        have h' : j.val + 1 = v * 3 := by omega
        exact ⟨h', by rw [h', Nat.mod_self]⟩
    unfold blk
    split_ifs with c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 <;>
      first
      | omega
      | (apply H1; simp only; omega)
      | (apply H2; simp only; omega)
      | (apply H3; simp only; omega)
  intro i
  simp only [List.get_ofFn]
  have e : Fin.cast (List.length_ofFn (f := blk R B E)) (finRotate _ i) =
      finRotate (v * 3) (Fin.cast (List.length_ofFn (f := blk R B E)) i) := by
    ext; simp only [Fin.coe_cast, finRotate_val, List.length_ofFn]
  rw [e]
  exact key _

end RPAux

namespace RPAux

def drpF {v : ℕ} : List (Fin (v + v) × Fin (v + v) × ℕ × Bool) :=
  (List.finRange v).flatMap (fun s =>
      [(Fin.castAdd v s, Fin.natAdd v s, 0, true), (Fin.natAdd v s, Fin.castAdd v s, 0, false)])

def drpG {v : ℕ} (adj : Fin v → Fin v → Bool) : List (Fin (v + v) × Fin (v + v) × ℕ × Bool) :=
  (List.finRange v).flatMap (fun s =>
      ((List.finRange v).filter (fun t => adj s t)).map
        (fun t => (Fin.castAdd v s, Fin.castAdd v t, 1, false)))

theorem drp_len_eq {v : ℕ} (adj : Fin v → Fin v → Bool) :
    (drpOfGraph adj).arcs.length = (drpF ++ drpG adj).length := rfl

theorem drp_get_eq {v : ℕ} (adj : Fin v → Fin v → Bool) (e : Fin (drpOfGraph adj).arcs.length) :
    (drpOfGraph adj).arcs.get e = (drpF ++ drpG adj)[e.val]'(by rw [← drp_len_eq]; exact e.isLt) :=
  rfl

theorem drp_mem {v : ℕ} (adj : Fin v → Fin v → Bool) (a : Fin (v + v) × Fin (v + v) × ℕ × Bool) :
    a ∈ (drpOfGraph adj).arcs ↔ a ∈ drpF ++ drpG adj := Iff.rfl

theorem drp_mem_cases {v : ℕ} (adj : Fin v → Fin v → Bool) (a : Fin (v + v) × Fin (v + v) × ℕ × Bool)
    (h : a ∈ drpF ++ drpG adj) :
    (∃ s : Fin v, a = (Fin.castAdd v s, Fin.natAdd v s, 0, true)) ∨
    (∃ s : Fin v, a = (Fin.natAdd v s, Fin.castAdd v s, 0, false)) ∨
    (∃ s t : Fin v, adj s t = true ∧ a = (Fin.castAdd v s, Fin.castAdd v t, 1, false)) := by
  simp only [drpF, drpG, List.mem_append, List.mem_map, List.mem_finRange, true_and,
    List.mem_flatMap, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with ⟨s, hs | hs⟩ | ⟨s, t, hadj, hs⟩
  · exact Or.inl ⟨s, hs⟩
  · exact Or.inr (Or.inl ⟨s, hs⟩)
  · exact Or.inr (Or.inr ⟨s, t, hadj, hs.symm⟩)

theorem drp_arc {v : ℕ} (adj : Fin v → Fin v → Bool) (e : Fin (drpOfGraph adj).arcs.length) :
    (∃ s : Fin v, (drpOfGraph adj).arcs.get e = (Fin.castAdd v s, Fin.natAdd v s, 0, true)) ∨
    (∃ s : Fin v, (drpOfGraph adj).arcs.get e = (Fin.natAdd v s, Fin.castAdd v s, 0, false)) ∨
    (∃ s t : Fin v, adj s t = true ∧
      (drpOfGraph adj).arcs.get e = (Fin.castAdd v s, Fin.castAdd v t, 1, false)) :=
  drp_mem_cases adj _ ((drp_mem adj _).1 (List.get_mem (drpOfGraph adj).arcs e))

theorem drp_req_mem {v : ℕ} (adj : Fin v → Fin v → Bool) (s : Fin v) :
    ∃ e : Fin (drpOfGraph adj).arcs.length,
      (drpOfGraph adj).arcs.get e = (Fin.castAdd v s, Fin.natAdd v s, 0, true) := by
  refine List.mem_iff_get.1 ((drp_mem adj (Fin.castAdd v s, Fin.natAdd v s, 0, true)).2 ?_)
  simp only [drpF, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons]
  exact Or.inl ⟨s, Or.inl rfl⟩

theorem drp_back_mem {v : ℕ} (adj : Fin v → Fin v → Bool) (s : Fin v) :
    ∃ e : Fin (drpOfGraph adj).arcs.length,
      (drpOfGraph adj).arcs.get e = (Fin.natAdd v s, Fin.castAdd v s, 0, false) := by
  refine List.mem_iff_get.1 ((drp_mem adj (Fin.natAdd v s, Fin.castAdd v s, 0, false)).2 ?_)
  simp only [drpF, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons]
  exact Or.inl ⟨s, Or.inr (Or.inl rfl)⟩

theorem drp_edge_mem {v : ℕ} (adj : Fin v → Fin v → Bool) (s t : Fin v) (h : adj s t = true) :
    ∃ e : Fin (drpOfGraph adj).arcs.length,
      (drpOfGraph adj).arcs.get e = (Fin.castAdd v s, Fin.castAdd v t, 1, false) := by
  refine List.mem_iff_get.1 ((drp_mem adj (Fin.castAdd v s, Fin.castAdd v t, 1, false)).2 ?_)
  simp only [drpG, List.mem_append, List.mem_map, List.mem_finRange, true_and,
    List.mem_flatMap, List.mem_filter]
  right
  exact ⟨s, t, h, rfl⟩

theorem drpF_nodup {v : ℕ} : (drpF (v := v)).Nodup := by
  unfold drpF
  rw [List.nodup_flatMap]
  refine ⟨fun s _ => ?_, ?_⟩
  · simp
  · refine List.Pairwise.imp_of_mem ?_ (List.nodup_finRange v)
    intro a b _ _ hab
    intro x hx1 hx2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx1 hx2
    rcases hx1 with rfl | rfl <;> rcases hx2 with h | h <;>
      simp only [Prod.mk.injEq] at h <;>
      first
      | exact hab (Fin.castAdd_inj.1 h.1)
      | exact hab ((Fin.natAdd_inj v).1 h.1)
      | exact absurd h.2.2.2 (by decide)

theorem drpG_flag {v : ℕ} (adj : Fin v → Fin v → Bool) :
    ∀ x ∈ drpG adj, x.2.2.2 = false := by
  intro x hx
  simp only [drpG, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨s, -, t, -, rfl⟩ := hx
  rfl

theorem drp_req_unique {v : ℕ} (adj : Fin v → Fin v → Bool)
    (e e' : Fin (drpOfGraph adj).arcs.length)
    (he : (drpOfGraph adj).IsRequired e)
    (h : (drpOfGraph adj).arcs.get e = (drpOfGraph adj).arcs.get e') : e = e' := by
  have hlt : ∀ f : Fin (drpOfGraph adj).arcs.length, (drpOfGraph adj).IsRequired f →
      f.val < (drpF (v := v)).length := by
    intro f hf
    by_contra hge
    push_neg at hge
    unfold RPInstance.IsRequired at hf
    rw [drp_get_eq, List.getElem_append_right hge] at hf
    rw [drpG_flag adj _ (List.getElem_mem _)] at hf
    exact Bool.noConfusion hf
  have he' : (drpOfGraph adj).IsRequired e' := by
    unfold RPInstance.IsRequired at he ⊢; rw [← h]; exact he
  have h1 := hlt e he
  have h2 := hlt e' he'
  rw [drp_get_eq, drp_get_eq, List.getElem_append_left h1, List.getElem_append_left h2] at h
  exact Fin.ext ((List.Nodup.getElem_inj_iff drpF_nodup).1 h)

theorem drp_tr {v : ℕ} (adj : Fin v → Fin v → Bool) (t : (drpOfGraph adj).Traversal)
    (ht : t.2 = true) :
    (∃ s : Fin v, (drpOfGraph adj).IsRequired t.1 ∧
      ((drpOfGraph adj).arcs.get t.1).2.2.1 = 0 ∧
      ((drpOfGraph adj).trSrc t).val = s.val ∧ ((drpOfGraph adj).trDst t).val = v + s.val) ∨
    (∃ s : Fin v, ((drpOfGraph adj).arcs.get t.1).2.2.1 = 0 ∧
      ((drpOfGraph adj).trSrc t).val = v + s.val ∧ ((drpOfGraph adj).trDst t).val = s.val) ∨
    (∃ a b : Fin v, ((drpOfGraph adj).arcs.get t.1).2.2.1 = 1 ∧ adj a b = true ∧
      ((drpOfGraph adj).trSrc t).val = a.val ∧ ((drpOfGraph adj).trDst t).val = b.val) := by
  obtain ⟨e, d⟩ := t
  simp only at ht
  subst ht
  rcases drp_arc adj e with ⟨s, hs⟩ | ⟨s, hs⟩ | ⟨a, b, hadj, hs⟩
  · left
    refine ⟨s, by simp only [RPInstance.IsRequired, hs], by simp only [hs], ?_, ?_⟩
    · simp only [RPInstance.trSrc, hs]; simp
    · simp only [RPInstance.trDst, hs]; simp; omega
  · right; left
    refine ⟨s, by simp only [hs], ?_, ?_⟩
    · simp only [RPInstance.trSrc, hs]; simp; omega
    · simp only [RPInstance.trDst, hs]; simp
  · right; right
    refine ⟨a, b, by simp only [hs], hadj, ?_, ?_⟩
    · simp only [RPInstance.trSrc, hs]; simp
    · simp only [RPInstance.trDst, hs]; simp

theorem drp_weight {v : ℕ} (adj : Fin v → Fin v → Bool) (τ : List (drpOfGraph adj).Traversal) :
    (drpOfGraph adj).tourWeight τ =
      τ.countP (fun t => ((drpOfGraph adj).arcs.get t.1).2.2.1 = 1) := by
  unfold RPInstance.tourWeight
  induction τ with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons]
    rw [ih, add_comm]
    congr 1
    rcases drp_arc adj a.1 with ⟨s, hs⟩ | ⟨s, hs⟩ | ⟨s, u, hadj, hs⟩
    · simp only [hs]; simp
    · simp only [hs]; simp
    · simp only [hs]; simp

theorem drp_reqmem {v : ℕ} (adj : Fin v → Fin v → Bool) (τ : List (drpOfGraph adj).Traversal)
    (hτ : (drpOfGraph adj).IsTour true τ) (s : Fin v) :
    ∃ t ∈ τ, ((drpOfGraph adj).trSrc t).val = s.val := by
  obtain ⟨e, he⟩ := drp_req_mem adj s
  obtain ⟨b, hb⟩ := hτ.2.2 e (by simp only [RPInstance.IsRequired, he])
  have hb' : b = true := hτ.1 rfl _ hb
  subst hb'
  refine ⟨(e, true), hb, ?_⟩
  simp only [RPInstance.trSrc, he]; simp

theorem drp_bij {v : ℕ} (adj : Fin v → Fin v → Bool) (hv : 2 ≤ v)
    (τ : List (drpOfGraph adj).Traversal) (hτ : (drpOfGraph adj).IsTour true τ)
    (hw : (drpOfGraph adj).tourWeight τ ≤ v) :
    Set.InjOn (fun i => ((drpOfGraph adj).trSrc (τ.get i)).val)
      (Finset.univ.filter (fun i : Fin τ.length =>
        ((drpOfGraph adj).arcs.get (τ.get i).1).2.2.1 = 1)) ∧
    Set.InjOn (fun i => ((drpOfGraph adj).trDst (τ.get i)).val)
      (Finset.univ.filter (fun i : Fin τ.length =>
        ((drpOfGraph adj).arcs.get (τ.get i).1).2.2.1 = 1)) ∧
    (∀ s : Fin v, ∃ i : Fin τ.length, ((drpOfGraph adj).arcs.get (τ.get i).1).2.2.1 = 1 ∧
      ((drpOfGraph adj).trSrc (τ.get i)).val = s.val) := by
  have hc := hτ.2.1
  have hdir : ∀ t ∈ τ, t.2 = true := hτ.1 rfl
  have other : ∀ s : Fin v, ∃ s' : Fin v, s'.val ≠ s.val := by
    intro s
    by_cases h0 : s.val = 0
    · exact ⟨⟨1, by omega⟩, by simp; omega⟩
    · exact ⟨⟨0, by omega⟩, by simp; omega⟩
  have hsrc : ∀ s : Fin v, ∃ i : Fin τ.length, ((drpOfGraph adj).arcs.get (τ.get i).1).2.2.1 = 1 ∧
      ((drpOfGraph adj).trSrc (τ.get i)).val = s.val := by
    intro s
    by_contra hno
    push_neg at hno
    obtain ⟨t0, ht0, h0⟩ := drp_reqmem adj τ hτ s
    have hall := closure (drpOfGraph adj) τ hc
      (fun x => x.val = s.val ∨ x.val = v + s.val) ?_ t0 ht0 (Or.inl h0)
    · obtain ⟨s', hs'⟩ := other s
      obtain ⟨t1, ht1, h1⟩ := drp_reqmem adj τ hτ s'
      have := hall t1 ht1
      have := s.isLt; have := s'.isLt
      omega
    · intro t ht hq
      have := s.isLt
      rcases drp_tr adj t (hdir t ht) with ⟨s', -, -, h1, h2⟩ | ⟨s', -, h1, h2⟩ |
          ⟨a, b, hw1, -, h1, h2⟩
      · have := s'.isLt; omega
      · have := s'.isLt; omega
      · exfalso
        have := a.isLt
        obtain ⟨i, rfl⟩ := List.mem_iff_get.1 ht
        exact hno i hw1 (by omega)
  have hdst : ∀ s : Fin v, ∃ i : Fin τ.length, ((drpOfGraph adj).arcs.get (τ.get i).1).2.2.1 = 1 ∧
      ((drpOfGraph adj).trDst (τ.get i)).val = s.val := by
    intro s
    by_contra hno
    push_neg at hno
    obtain ⟨s', hs'⟩ := other s
    obtain ⟨t0, ht0, h0⟩ := drp_reqmem adj τ hτ s'
    have h0' : ¬ (((drpOfGraph adj).trSrc t0).val = s.val ∨
        ((drpOfGraph adj).trSrc t0).val = v + s.val) := by
      have := s.isLt; have := s'.isLt
      omega
    have hall := closure (drpOfGraph adj) τ hc
      (fun x => ¬ (x.val = s.val ∨ x.val = v + s.val)) ?_ t0 ht0 h0'
    · obtain ⟨t1, ht1, h1⟩ := drp_reqmem adj τ hτ s
      have := hall t1 ht1
      omega
    · intro t ht hq hq2
      apply hq
      have := s.isLt
      rcases drp_tr adj t (hdir t ht) with ⟨s', -, -, h1, h2⟩ | ⟨s', -, h1, h2⟩ |
          ⟨a, b, hw1, -, h1, h2⟩
      · have := s'.isLt; omega
      · have := s'.isLt; omega
      · exfalso
        have := b.isLt
        obtain ⟨i, rfl⟩ := List.mem_iff_get.1 ht
        exact hno i hw1 (by omega)
  set P := Finset.univ.filter (fun i : Fin τ.length =>
    ((drpOfGraph adj).arcs.get (τ.get i).1).2.2.1 = 1) with hP
  have hPcard : P.card ≤ v := by
    rw [drp_weight, countP_eq_sum, ← Finset.card_filter] at hw
    simpa [hP] using hw
  have himg : ∀ f : Fin τ.length → ℕ,
      (∀ s : Fin v, ∃ i, i ∈ P ∧ f i = s.val) → v ≤ (P.image f).card := by
    intro f hf
    have hsub : Finset.range v ⊆ P.image f := by
      intro x hx
      rw [Finset.mem_range] at hx
      obtain ⟨i, hi, hfi⟩ := hf ⟨x, hx⟩
      exact Finset.mem_image.2 ⟨i, hi, hfi⟩
    have := Finset.card_le_card hsub
    simpa using this
  have h1 := himg (fun i => ((drpOfGraph adj).trSrc (τ.get i)).val)
    (fun s => by obtain ⟨i, hi, h⟩ := hsrc s; exact ⟨i, by simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi, h⟩)
  have h2 := himg (fun i => ((drpOfGraph adj).trDst (τ.get i)).val)
    (fun s => by obtain ⟨i, hi, h⟩ := hdst s; exact ⟨i, by simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi, h⟩)
  have h1' := Finset.card_image_le (s := P) (f := fun i => ((drpOfGraph adj).trSrc (τ.get i)).val)
  have h2' := Finset.card_image_le (s := P) (f := fun i => ((drpOfGraph adj).trDst (τ.get i)).val)
  exact ⟨Finset.card_image_iff.mp (by omega), Finset.card_image_iff.mp (by omega), hsrc⟩

theorem drp_back {v : ℕ} (adj : Fin v → Fin v → Bool)
    (hv : 2 ≤ v) (hG : (drpOfGraph adj).RPYes true) :
    SchedComplexity.NoWait.HasHamiltonCircuit adj := by
  obtain ⟨τ, hτ, hw⟩ := hG
  obtain ⟨hinjS, hinjD, hsrc⟩ := drp_bij adj hv τ hτ hw
  have hc := hτ.2.1
  have hdir : ∀ t ∈ τ, t.2 = true := hτ.1 rfl
  have memP : ∀ k : Fin τ.length, ((drpOfGraph adj).arcs.get (τ.get k).1).2.2.1 = 1 →
      k ∈ (↑(Finset.univ.filter (fun i : Fin τ.length =>
        ((drpOfGraph adj).arcs.get (τ.get i).1).2.2.1 = 1)) : Set (Fin τ.length)) := by
    intro k hk
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact hk
  have hnext : ∀ a : Fin v, ∃ b : Fin v, ∃ i : Fin τ.length,
      ((drpOfGraph adj).arcs.get (τ.get i).1).2.2.1 = 1 ∧
      ((drpOfGraph adj).trSrc (τ.get i)).val = a.val ∧
      ((drpOfGraph adj).trDst (τ.get i)).val = b.val ∧ adj a b = true := by
    intro a
    obtain ⟨i, hi, h1⟩ := hsrc a
    rcases drp_tr adj (τ.get i) (hdir _ (List.get_mem _ _)) with ⟨s', -, hw0, -⟩ |
        ⟨s', hw0, -⟩ | ⟨x, y, -, hxy, h2, h3⟩
    · rw [hw0] at hi; exact absurd hi (by decide)
    · rw [hw0] at hi; exact absurd hi (by decide)
    · have hxa : x = a := Fin.ext (by omega)
      subst hxa
      exact ⟨y, i, hi, h1, h3, hxy⟩
  choose next idx hidxP hidxS hidxD hadj using hnext
  have hinj : Function.Injective next := by
    intro a a' h
    have := hinjD (memP _ (hidxP a)) (memP _ (hidxP a')) (by beta_reduce; rw [hidxD, hidxD, h])
    apply Fin.ext
    rw [← hidxS a, ← hidxS a', this]
  refine ham_of_next adj next hinj hadj ⟨0, by omega⟩ ?_
  intro z
  obtain ⟨t0, ht0, h0⟩ := drp_reqmem adj τ hτ ⟨0, by omega⟩
  have hall := closure (drpOfGraph adj) τ hc
    (fun y => ∃ x : Fin v, (∃ m, next^[m] ⟨0, by omega⟩ = x) ∧
      (y.val = x.val ∨ y.val = v + x.val)) ?_ t0 ht0 ⟨_, ⟨0, rfl⟩, Or.inl h0⟩
  · obtain ⟨t1, ht1, h1⟩ := drp_reqmem adj τ hτ z
    obtain ⟨x, ⟨m, hm⟩, hx⟩ := hall t1 ht1
    refine ⟨m, ?_⟩
    rw [hm]
    have := x.isLt; have := z.isLt
    exact Fin.ext (by omega)
  · intro t ht hq
    obtain ⟨x, ⟨m, hm⟩, hx⟩ := hq
    have := x.isLt
    rcases drp_tr adj t (hdir t ht) with ⟨s', -, -, h1, h2⟩ | ⟨s', -, h1, h2⟩ |
        ⟨c, d, hw1, -, h1, h2⟩
    · have := s'.isLt; exact ⟨x, ⟨m, hm⟩, by omega⟩
    · have := s'.isLt; exact ⟨x, ⟨m, hm⟩, by omega⟩
    · have := c.isLt
      obtain ⟨k, rfl⟩ := List.mem_iff_get.1 ht
      have hk : k = idx x := hinjS (memP k hw1) (memP _ (hidxP x)) (by
        beta_reduce; rw [hidxS]; omega)
      refine ⟨next x, ⟨m + 1, by rw [Function.iterate_succ_apply', hm]⟩, Or.inl ?_⟩
      rw [hk, hidxD]

end RPAux

namespace RPAux

theorem drp_fwd {v : ℕ} (adj : Fin v → Fin v → Bool) (hv : 2 ≤ v)
    (hH : SchedComplexity.NoWait.HasHamiltonCircuit adj) : (drpOfGraph adj).RPYes true := by
  obtain ⟨σ, hσ⟩ := hH
  choose rq hrq using drp_req_mem adj
  choose bk hbk using drp_back_mem adj
  choose ed hed using fun i => drp_edge_mem adj (σ i) (σ (finRotate v i)) (hσ i)
  have hRS : ∀ s : Fin v, ((drpOfGraph adj).trSrc (rq s, true)).val = s.val := by
    intro s; simp only [RPInstance.trSrc, hrq]; simp
  have hRD : ∀ s : Fin v, ((drpOfGraph adj).trDst (rq s, true)).val = v + s.val := by
    intro s; simp only [RPInstance.trDst, hrq]; simp; omega
  have hBS : ∀ s : Fin v, ((drpOfGraph adj).trSrc (bk s, true)).val = v + s.val := by
    intro s; simp only [RPInstance.trSrc, hbk]; simp; omega
  have hBD : ∀ s : Fin v, ((drpOfGraph adj).trDst (bk s, true)).val = s.val := by
    intro s; simp only [RPInstance.trDst, hbk]; simp
  have hES : ∀ i : Fin v, ((drpOfGraph adj).trSrc (ed i, true)).val = (σ i).val := by
    intro i; simp only [RPInstance.trSrc, hed]; simp
  have hED : ∀ i : Fin v, ((drpOfGraph adj).trDst (ed i, true)).val =
      (σ (finRotate v i)).val := by
    intro i; simp only [RPInstance.trDst, hed]; simp
  have hRw : ∀ s : Fin v, ((drpOfGraph adj).arcs.get (rq s)).2.2.1 = 0 := by
    intro s; simp only [hrq]
  have hBw : ∀ s : Fin v, ((drpOfGraph adj).arcs.get (bk s)).2.2.1 = 0 := by
    intro s; simp only [hbk]
  have hEw : ∀ i : Fin v, ((drpOfGraph adj).arcs.get (ed i)).2.2.1 = 1 := by
    intro i; simp only [hed]
  refine ⟨List.ofFn (blk (fun i => (rq (σ i), true)) (fun i => (bk (σ i), true))
    (fun i => (ed i, true))), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro _ t ht
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 ht
    unfold blk
    split_ifs <;> rfl
  · apply cyc_blk
    · intro i; exact Fin.ext (by rw [hRD, hBS])
    · intro i; exact Fin.ext (by rw [hBD, hES])
    · intro i; exact Fin.ext (by rw [hED, hRS])
  · intro e he
    rcases drp_arc adj e with ⟨s, hs⟩ | ⟨s, hs⟩ | ⟨a, b, -, hs⟩
    · have : e = rq s := drp_req_unique adj e (rq s) he (by rw [hs, hrq])
      subst this
      refine ⟨true, List.mem_ofFn.2 ⟨finProdFinEquiv (σ.symm s, 0), ?_⟩⟩
      rw [blk_fpfe]
      simp
    · exfalso
      unfold RPInstance.IsRequired at he
      rw [hs] at he
      exact Bool.noConfusion he
    · exfalso
      unfold RPInstance.IsRequired at he
      rw [hs] at he
      exact Bool.noConfusion he
  · unfold RPInstance.tourWeight
    rw [List.map_ofFn, List.sum_ofFn]
    have := sum_blk (fun i => (rq (σ i), true)) (fun i => (bk (σ i), true)) (fun i => (ed i, true))
      (fun t => ((drpOfGraph adj).arcs.get t.1).2.2.1)
    simp only [Function.comp] at this ⊢
    rw [this]
    simp only [hRw, hBw, hEw]
    simp
    rfl

theorem drp_claim {v : ℕ} (adj : Fin v → Fin v → Bool) (hv : v ≠ 1) :
    SchedComplexity.NoWait.HasHamiltonCircuit adj ↔ (drpOfGraph adj).RPYes true := by
  rcases Nat.lt_or_ge v 2 with h | h
  · obtain rfl : v = 0 := by omega
    have hlen : (drpOfGraph adj).arcs.length = 0 := by
      rw [drp_len_eq]; simp [drpF, drpG]
    constructor
    · intro _
      refine ⟨[], ⟨fun _ t ht => by simp at ht, fun i => i.elim0, fun e _ => ?_⟩, ?_⟩
      · exact absurd e.isLt (by omega)
      · simp [RPInstance.tourWeight]
    · intro _
      exact ⟨Equiv.refl _, fun i => i.elim0⟩
  · exact ⟨drp_fwd adj h, drp_back adj h⟩

end RPAux

open RuralPostman.NPC

theorem solution {v : ℕ} (adj : Fin v → Fin v → Bool) (hv : v ≠ 1) :
    SchedComplexity.NoWait.HasHamiltonCircuit adj ↔ (drpOfGraph adj).RPYes true :=
  RPAux.drp_claim adj hv
