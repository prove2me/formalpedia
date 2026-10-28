-- Prove2me | solution 1 for RuralPostman.NPC.claim_undirected_forward
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:19:21.391553+00:00
-- url     : https://prove2.me/submissions/aacff347-5bd5-4eae-abec-982798b96cfe

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

set_option linter.unusedSimpArgs false

namespace RPAux

theorem urp_mem {v : ℕ} (adj : Fin v → Fin v → Bool) (a : Fin (v + v) × Fin (v + v) × ℕ × Bool) :
    a ∈ (urpOfGraph adj).arcs ↔ a ∈ (List.finRange v).map (fun s => (Fin.castAdd v s, Fin.natAdd v s, 0, true)) ++
    (List.finRange v).flatMap (fun s =>
      ((List.finRange v).filter (fun t => decide (s < t) && adj s t)).map
        (fun t => (Fin.castAdd v s, Fin.castAdd v t, 1, false))) := Iff.rfl

theorem urp_mem_cases {v : ℕ} (adj : Fin v → Fin v → Bool) (a : Fin (v + v) × Fin (v + v) × ℕ × Bool)
    (h : a ∈ (List.finRange v).map (fun s => (Fin.castAdd v s, Fin.natAdd v s, 0, true)) ++
    (List.finRange v).flatMap (fun s =>
      ((List.finRange v).filter (fun t => decide (s < t) && adj s t)).map
        (fun t => (Fin.castAdd v s, Fin.castAdd v t, 1, false)))) :
    (∃ s : Fin v, a = (Fin.castAdd v s, Fin.natAdd v s, 0, true)) ∨
    (∃ s t : Fin v, s < t ∧ adj s t = true ∧ a = (Fin.castAdd v s, Fin.castAdd v t, 1, false)) := by
  simp only [List.mem_append, List.mem_map, List.mem_finRange, true_and,
    List.mem_flatMap, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨s, hs⟩ | ⟨s, t, ⟨hst, hadj⟩, hs⟩
  · exact Or.inl ⟨s, hs.symm⟩
  · exact Or.inr ⟨s, t, hst, hadj, hs.symm⟩

theorem urp_arc {v : ℕ} (adj : Fin v → Fin v → Bool) (e : Fin (urpOfGraph adj).arcs.length) :
    (∃ s : Fin v, (urpOfGraph adj).arcs.get e = (Fin.castAdd v s, Fin.natAdd v s, 0, true)) ∨
    (∃ s t : Fin v, s < t ∧ adj s t = true ∧
      (urpOfGraph adj).arcs.get e = (Fin.castAdd v s, Fin.castAdd v t, 1, false)) :=
  urp_mem_cases adj _ ((urp_mem adj _).1 (List.get_mem (urpOfGraph adj).arcs e))

theorem urp_req_mem {v : ℕ} (adj : Fin v → Fin v → Bool) (s : Fin v) :
    ∃ e : Fin (urpOfGraph adj).arcs.length,
      (urpOfGraph adj).arcs.get e = (Fin.castAdd v s, Fin.natAdd v s, 0, true) := by
  refine List.mem_iff_get.1 ((urp_mem adj (Fin.castAdd v s, Fin.natAdd v s, 0, true)).2 ?_)
  simp only [List.mem_append, List.mem_map, List.mem_finRange, true_and]
  exact Or.inl ⟨s, rfl⟩

theorem urp_edge_mem {v : ℕ} (adj : Fin v → Fin v → Bool) (s t : Fin v) (hst : s < t)
    (h : adj s t = true) :
    ∃ e : Fin (urpOfGraph adj).arcs.length,
      (urpOfGraph adj).arcs.get e = (Fin.castAdd v s, Fin.castAdd v t, 1, false) := by
  refine List.mem_iff_get.1 ((urp_mem adj (Fin.castAdd v s, Fin.castAdd v t, 1, false)).2 ?_)
  simp only [List.mem_append, List.mem_map, List.mem_finRange, true_and,
    List.mem_flatMap, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  right
  exact ⟨s, t, ⟨hst, h⟩, rfl⟩

theorem urp_tr {v : ℕ} (adj : Fin v → Fin v → Bool) (t : (urpOfGraph adj).Traversal) :
    (∃ s : Fin v, (urpOfGraph adj).IsRequired t.1 ∧
      ((((urpOfGraph adj).trSrc t).val = s.val ∧ ((urpOfGraph adj).trDst t).val = v + s.val) ∨
       (((urpOfGraph adj).trSrc t).val = v + s.val ∧ ((urpOfGraph adj).trDst t).val = s.val))) ∨
    (∃ a b : Fin v, ¬ (urpOfGraph adj).IsRequired t.1 ∧ a ≠ b ∧
      (adj a b = true ∨ adj b a = true) ∧
      ((urpOfGraph adj).trSrc t).val = a.val ∧ ((urpOfGraph adj).trDst t).val = b.val) := by
  obtain ⟨e, d⟩ := t
  rcases urp_arc adj e with ⟨s, hs⟩ | ⟨s, u, hlt, hadj, hs⟩
  · left
    refine ⟨s, by simp only [RPInstance.IsRequired, hs], ?_⟩
    cases d <;> simp only [RPInstance.trSrc, RPInstance.trDst, hs] <;> simp <;> omega
  · right
    cases d
    · refine ⟨u, s, by simp only [RPInstance.IsRequired, hs]; simp, (ne_of_lt hlt).symm,
        Or.inr hadj, ?_, ?_⟩
      · simp only [RPInstance.trSrc, hs]; simp
      · simp only [RPInstance.trDst, hs]; simp
    · refine ⟨s, u, by simp only [RPInstance.IsRequired, hs]; simp, ne_of_lt hlt,
        Or.inl hadj, ?_, ?_⟩
      · simp only [RPInstance.trSrc, hs]; simp
      · simp only [RPInstance.trDst, hs]; simp

theorem urp_weight {v : ℕ} (adj : Fin v → Fin v → Bool) (τ : List (urpOfGraph adj).Traversal) :
    (urpOfGraph adj).tourWeight τ = τ.countP (fun t => ¬ (urpOfGraph adj).IsRequired t.1) := by
  unfold RPInstance.tourWeight
  induction τ with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons]
    rw [ih, add_comm]
    congr 1
    rcases urp_arc adj a.1 with ⟨s, hs⟩ | ⟨s, u, hlt, hadj, hs⟩
    · simp only [RPInstance.IsRequired, hs]; simp
    · simp only [RPInstance.IsRequired, hs]; simp

theorem urp_bij {v : ℕ} (adj : Fin v → Fin v → Bool) (hv : 2 ≤ v)
    (τ : List (urpOfGraph adj).Traversal) (hτ : (urpOfGraph adj).IsTour false τ)
    (hw : (urpOfGraph adj).tourWeight τ ≤ v) :
    (Finset.univ.filter (fun i : Fin τ.length => ¬ (urpOfGraph adj).IsRequired (τ.get i).1)).card = v ∧
    Set.InjOn (fun i => ((urpOfGraph adj).trSrc (τ.get i)).val)
      (Finset.univ.filter (fun i : Fin τ.length => ¬ (urpOfGraph adj).IsRequired (τ.get i).1)) ∧
    Set.InjOn (fun i => ((urpOfGraph adj).trDst (τ.get i)).val)
      (Finset.univ.filter (fun i : Fin τ.length => ¬ (urpOfGraph adj).IsRequired (τ.get i).1)) ∧
    (∀ s : Fin v, ∃ i : Fin τ.length, ¬ (urpOfGraph adj).IsRequired (τ.get i).1 ∧
      ((urpOfGraph adj).trSrc (τ.get i)).val = s.val) ∧
    (∀ s : Fin v, ∃ i : Fin τ.length, ¬ (urpOfGraph adj).IsRequired (τ.get i).1 ∧
      ((urpOfGraph adj).trDst (τ.get i)).val = s.val) := by
  obtain ⟨-, hc, hreq⟩ := hτ
  have hreqmem : ∀ s : Fin v, ∃ t ∈ τ, ((urpOfGraph adj).trSrc t).val = s.val ∨
      ((urpOfGraph adj).trSrc t).val = v + s.val := by
    intro s
    obtain ⟨e, he⟩ := urp_req_mem adj s
    obtain ⟨b, hb⟩ := hreq e (by simp only [RPInstance.IsRequired, he])
    refine ⟨(e, b), hb, ?_⟩
    cases b <;> simp only [RPInstance.trSrc, he] <;> simp <;> omega
  have other : ∀ s : Fin v, ∃ s' : Fin v, s'.val ≠ s.val := by
    intro s
    by_cases h0 : s.val = 0
    · exact ⟨⟨1, by omega⟩, by simp; omega⟩
    · exact ⟨⟨0, by omega⟩, by simp; omega⟩
  have hsrc : ∀ s : Fin v, ∃ i : Fin τ.length, ¬ (urpOfGraph adj).IsRequired (τ.get i).1 ∧
      ((urpOfGraph adj).trSrc (τ.get i)).val = s.val := by
    intro s
    by_contra hno
    push_neg at hno
    obtain ⟨t0, ht0, h0⟩ := hreqmem s
    have hall := closure (urpOfGraph adj) τ hc
      (fun x => x.val = s.val ∨ x.val = v + s.val) ?_ t0 ht0 h0
    · obtain ⟨s', hs'⟩ := other s
      obtain ⟨t1, ht1, h1⟩ := hreqmem s'
      have := hall t1 ht1
      have := s.isLt; have := s'.isLt
      omega
    · intro t ht hq
      have := s.isLt
      rcases urp_tr adj t with ⟨s', -, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨a, b, hnr, -, -, h1, h2⟩
      · have := s'.isLt; omega
      · have := s'.isLt; omega
      · exfalso
        have := a.isLt
        obtain ⟨i, rfl⟩ := List.mem_iff_get.1 ht
        exact hno i hnr (by omega)
  have hdst : ∀ s : Fin v, ∃ i : Fin τ.length, ¬ (urpOfGraph adj).IsRequired (τ.get i).1 ∧
      ((urpOfGraph adj).trDst (τ.get i)).val = s.val := by
    intro s
    by_contra hno
    push_neg at hno
    obtain ⟨s', hs'⟩ := other s
    obtain ⟨t0, ht0, h0⟩ := hreqmem s'
    have h0' : ¬ (((urpOfGraph adj).trSrc t0).val = s.val ∨
        ((urpOfGraph adj).trSrc t0).val = v + s.val) := by
      have := s.isLt; have := s'.isLt
      omega
    have hall := closure (urpOfGraph adj) τ hc
      (fun x => ¬ (x.val = s.val ∨ x.val = v + s.val)) ?_ t0 ht0 h0'
    · obtain ⟨t1, ht1, h1⟩ := hreqmem s
      have := hall t1 ht1
      omega
    · intro t ht hq hq2
      apply hq
      have := s.isLt
      rcases urp_tr adj t with ⟨s', -, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨a, b, hnr, -, -, h1, h2⟩
      · have := s'.isLt; omega
      · have := s'.isLt; omega
      · exfalso
        have := b.isLt
        obtain ⟨i, rfl⟩ := List.mem_iff_get.1 ht
        exact hno i hnr (by omega)
  set P := Finset.univ.filter (fun i : Fin τ.length => ¬ (urpOfGraph adj).IsRequired (τ.get i).1)
    with hP
  have hPcard : P.card ≤ v := by
    rw [urp_weight, countP_eq_sum, ← Finset.card_filter] at hw
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
  have h1 := himg (fun i => ((urpOfGraph adj).trSrc (τ.get i)).val)
    (fun s => by obtain ⟨i, hi, h⟩ := hsrc s; exact ⟨i, by simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi, h⟩)
  have h2 := himg (fun i => ((urpOfGraph adj).trDst (τ.get i)).val)
    (fun s => by obtain ⟨i, hi, h⟩ := hdst s; exact ⟨i, by simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi, h⟩)
  have h1' := Finset.card_image_le (s := P) (f := fun i => ((urpOfGraph adj).trSrc (τ.get i)).val)
  have h2' := Finset.card_image_le (s := P) (f := fun i => ((urpOfGraph adj).trDst (τ.get i)).val)
  refine ⟨by omega, Finset.card_image_iff.mp (by omega), Finset.card_image_iff.mp (by omega),
    hsrc, hdst⟩

end RPAux

namespace RPAux

theorem urp_reqmem {v : ℕ} (adj : Fin v → Fin v → Bool) (τ : List (urpOfGraph adj).Traversal)
    (hτ : (urpOfGraph adj).IsTour false τ) (s : Fin v) :
    ∃ t ∈ τ, ((urpOfGraph adj).trSrc t).val = s.val ∨
      ((urpOfGraph adj).trSrc t).val = v + s.val := by
  obtain ⟨e, he⟩ := urp_req_mem adj s
  obtain ⟨b, hb⟩ := hτ.2.2 e (by simp only [RPInstance.IsRequired, he])
  refine ⟨(e, b), hb, ?_⟩
  cases b <;> simp only [RPInstance.trSrc, he] <;> simp <;> omega

theorem urp_count {v : ℕ} (adj : Fin v → Fin v → Bool)
    (hv : 3 ≤ v) (τ : List (urpOfGraph adj).Traversal) (hτ : (urpOfGraph adj).IsTour false τ)
    (hw : (urpOfGraph adj).tourWeight τ ≤ (urpOfGraph adj).k) :
    τ.countP (fun t => ¬ (urpOfGraph adj).IsRequired t.1) = v ∧
      ∀ e, ¬ (urpOfGraph adj).IsRequired e → τ.countP (fun t => t.1 = e) ≤ 1 := by
  have hw' : (urpOfGraph adj).tourWeight τ ≤ v := hw
  obtain ⟨hcard, hinjS, hinjD, hsrc, hdst⟩ := urp_bij adj (by omega) τ hτ hw'
  have hc := hτ.2.1
  have memP : ∀ k : Fin τ.length, ¬ (urpOfGraph adj).IsRequired (τ.get k).1 →
      k ∈ (↑(Finset.univ.filter (fun i : Fin τ.length =>
        ¬ (urpOfGraph adj).IsRequired (τ.get i).1)) : Set (Fin τ.length)) := by
    intro k hk
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact hk
  refine ⟨?_, ?_⟩
  · rw [countP_eq_sum, ← Finset.card_filter]; simpa using hcard
  · intro e he
    by_contra hlt
    push_neg at hlt
    rw [countP_eq_sum, ← Finset.card_filter] at hlt
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 hlt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hi hj
    rcases urp_arc adj e with ⟨s, hs⟩ | ⟨a, b, hab, hadj, hs⟩
    · exact he (by simp only [RPInstance.IsRequired, hs])
    have hS : ∀ d : Bool, ((urpOfGraph adj).trSrc (e, d)).val = if d then a.val else b.val := by
      intro d; cases d <;> simp only [RPInstance.trSrc, hs] <;> simp
    have hD : ∀ d : Bool, ((urpOfGraph adj).trDst (e, d)).val = if d then b.val else a.val := by
      intro d; cases d <;> simp only [RPInstance.trDst, hs] <;> simp
    have ti : τ.get i = (e, (τ.get i).2) := Prod.ext hi rfl
    have tj : τ.get j = (e, (τ.get j).2) := Prod.ext hj rfl
    generalize (τ.get i).2 = di at ti
    generalize (τ.get j).2 = dj at tj
    have hiP := memP i (by rw [hi]; exact he)
    have hjP := memP j (by rw [hj]; exact he)
    have hab' : a.val < b.val := hab
    by_cases hd : di = dj
    · apply hij
      apply hinjS hiP hjP
      beta_reduce
      rw [ti, tj, hd]
    have key : (((urpOfGraph adj).trSrc (τ.get i)).val = a.val ∧
        ((urpOfGraph adj).trDst (τ.get i)).val = b.val ∧
        ((urpOfGraph adj).trSrc (τ.get j)).val = b.val ∧
        ((urpOfGraph adj).trDst (τ.get j)).val = a.val) ∨
        (((urpOfGraph adj).trSrc (τ.get i)).val = b.val ∧
        ((urpOfGraph adj).trDst (τ.get i)).val = a.val ∧
        ((urpOfGraph adj).trSrc (τ.get j)).val = a.val ∧
        ((urpOfGraph adj).trDst (τ.get j)).val = b.val) := by
      rw [ti, tj, hS, hS, hD, hD]
      cases di <;> cases dj <;> simp at hd ⊢
    have hall := closure (urpOfGraph adj) τ hc
      (fun x => x.val = a.val ∨ x.val = v + a.val ∨ x.val = b.val ∨ x.val = v + b.val) ?_
      (τ.get i) (List.get_mem _ _) (by
        rcases key with ⟨k1, -⟩ | ⟨k1, -⟩
        · exact Or.inl k1
        · exact Or.inr (Or.inr (Or.inl k1)))
    · obtain ⟨c, -, hc'⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := {a, b}) (t := Finset.univ) (by
          have := Finset.card_le_two (a := a) (b := b)
          simp only [Finset.card_univ, Fintype.card_fin]; omega)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc'
      have hca : c.val ≠ a.val := fun h => hc'.1 (Fin.ext h)
      have hcb : c.val ≠ b.val := fun h => hc'.2 (Fin.ext h)
      obtain ⟨t1, ht1, h1⟩ := urp_reqmem adj τ hτ c
      have := hall t1 ht1
      have := a.isLt; have := b.isLt; have := c.isLt
      omega
    · intro t ht hq
      have := a.isLt; have := b.isLt
      rcases urp_tr adj t with ⟨s', -, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨x, y, hnr, -, -, h1, h2⟩
      · have := s'.isLt; omega
      · have := s'.isLt; omega
      · have := x.isLt; have := y.isLt
        obtain ⟨k, rfl⟩ := List.mem_iff_get.1 ht
        have hkP := memP k hnr
        have hk : k = i ∨ k = j := by
          rcases key with ⟨k1, k2, k3, k4⟩ | ⟨k1, k2, k3, k4⟩
          · by_cases hxa : x.val = a.val
            · left; exact hinjS hkP hiP (by try simp only; omega)
            · right; exact hinjS hkP hjP (by try simp only; omega)
          · by_cases hxa : x.val = a.val
            · right; exact hinjS hkP hjP (by try simp only; omega)
            · left; exact hinjS hkP hiP (by try simp only; omega)
        rcases hk with rfl | rfl <;> omega

theorem urp_back {v : ℕ} (adj : Fin v → Fin v → Bool) (hs : IsSymm adj)
    (hv : 3 ≤ v) (hG : (urpOfGraph adj).RPYes false) :
    SchedComplexity.NoWait.HasHamiltonCircuit adj := by
  obtain ⟨τ, hτ, hw⟩ := hG
  obtain ⟨hcard, hinjS, hinjD, hsrc, hdst⟩ := urp_bij adj (by omega) τ hτ hw
  have hc := hτ.2.1
  have memP : ∀ k : Fin τ.length, ¬ (urpOfGraph adj).IsRequired (τ.get k).1 →
      k ∈ (↑(Finset.univ.filter (fun i : Fin τ.length =>
        ¬ (urpOfGraph adj).IsRequired (τ.get i).1)) : Set (Fin τ.length)) := by
    intro k hk
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact hk
  have hnext : ∀ a : Fin v, ∃ b : Fin v, ∃ i : Fin τ.length,
      ¬ (urpOfGraph adj).IsRequired (τ.get i).1 ∧
      ((urpOfGraph adj).trSrc (τ.get i)).val = a.val ∧
      ((urpOfGraph adj).trDst (τ.get i)).val = b.val ∧ adj a b = true := by
    intro a
    obtain ⟨i, hi, h1⟩ := hsrc a
    rcases urp_tr adj (τ.get i) with ⟨s', hr, -⟩ | ⟨x, y, -, -, hxy, h2, h3⟩
    · exact absurd hr hi
    · have hxa : x = a := Fin.ext (by omega)
      subst hxa
      refine ⟨y, i, hi, h1, h3, ?_⟩
      rcases hxy with h | h
      · exact h
      · rw [hs]; exact h
  choose next idx hidxP hidxS hidxD hadj using hnext
  have hinj : Function.Injective next := by
    intro a a' h
    have := hinjD (memP _ (hidxP a)) (memP _ (hidxP a')) (by beta_reduce; rw [hidxD, hidxD, h])
    apply Fin.ext
    rw [← hidxS a, ← hidxS a', this]
  refine ham_of_next adj next hinj hadj ⟨0, by omega⟩ ?_
  intro z
  obtain ⟨t0, ht0, h0⟩ := urp_reqmem adj τ hτ ⟨0, by omega⟩
  have hall := closure (urpOfGraph adj) τ hc
    (fun y => ∃ x : Fin v, (∃ m, next^[m] ⟨0, by omega⟩ = x) ∧
      (y.val = x.val ∨ y.val = v + x.val)) ?_ t0 ht0 ⟨_, ⟨0, rfl⟩, h0⟩
  · obtain ⟨t1, ht1, h1⟩ := urp_reqmem adj τ hτ z
    obtain ⟨x, ⟨m, hm⟩, hx⟩ := hall t1 ht1
    refine ⟨m, ?_⟩
    rw [hm]
    have := x.isLt; have := z.isLt
    exact Fin.ext (by omega)
  · intro t ht hq
    obtain ⟨x, ⟨m, hm⟩, hx⟩ := hq
    have := x.isLt
    rcases urp_tr adj t with ⟨s', -, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨c, d, hnr, -, -, h1, h2⟩
    · have := s'.isLt; exact ⟨x, ⟨m, hm⟩, by omega⟩
    · have := s'.isLt; exact ⟨x, ⟨m, hm⟩, by omega⟩
    · have := c.isLt
      obtain ⟨k, rfl⟩ := List.mem_iff_get.1 ht
      have hk : k = idx x := hinjS (memP k hnr) (memP _ (hidxP x)) (by
        beta_reduce; rw [hidxS]; omega)
      refine ⟨next x, ⟨m + 1, by rw [Function.iterate_succ_apply', hm]⟩, Or.inl ?_⟩
      rw [hk, hidxD]

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

def urpL {v : ℕ} (adj : Fin v → Fin v → Bool) : List (Fin (v + v) × Fin (v + v) × ℕ × Bool) :=
  (List.finRange v).map (fun s => (Fin.castAdd v s, Fin.natAdd v s, 0, true)) ++
    (List.finRange v).flatMap (fun s =>
      ((List.finRange v).filter (fun t => decide (s < t) && adj s t)).map
        (fun t => (Fin.castAdd v s, Fin.castAdd v t, 1, false)))

theorem urp_len_eq {v : ℕ} (adj : Fin v → Fin v → Bool) :
    (urpOfGraph adj).arcs.length = (urpL adj).length := rfl

theorem urp_len {v : ℕ} (adj : Fin v → Fin v → Bool) : v ≤ (urpOfGraph adj).arcs.length := by
  rw [urp_len_eq]; simp [urpL]

theorem urp_get_eq {v : ℕ} (adj : Fin v → Fin v → Bool) (e : Fin (urpOfGraph adj).arcs.length) :
    (urpOfGraph adj).arcs.get e = (urpL adj)[e.val]'(by rw [← urp_len_eq]; exact e.isLt) := rfl

theorem urpL_lt {v : ℕ} (adj : Fin v → Fin v → Bool) (n : ℕ) (h : n < (urpL adj).length)
    (hn : n < v) : (urpL adj)[n] = (Fin.castAdd v ⟨n, hn⟩, Fin.natAdd v ⟨n, hn⟩, 0, true) := by
  simp only [urpL]
  rw [List.getElem_append_left (by simpa using hn)]
  simp

theorem urpL_ge {v : ℕ} (adj : Fin v → Fin v → Bool) (n : ℕ) (h : n < (urpL adj).length)
    (hn : v ≤ n) : ((urpL adj)[n]).2.2.2 = false := by
  have hB : ∀ x ∈ (List.finRange v).flatMap (fun s =>
      ((List.finRange v).filter (fun t => decide (s < t) && adj s t)).map
        (fun t => (Fin.castAdd v s, Fin.castAdd v t, 1, false))), x.2.2.2 = false := by
    intro x hx
    simp only [List.mem_flatMap, List.mem_map] at hx
    obtain ⟨s, -, t, -, rfl⟩ := hx
    rfl
  simp only [urpL]
  rw [List.getElem_append_right (by simpa using hn)]
  apply hB
  exact List.getElem_mem _

def reqE {v : ℕ} (adj : Fin v → Fin v → Bool) (s : Fin v) : Fin (urpOfGraph adj).arcs.length :=
  ⟨s.val, lt_of_lt_of_le s.isLt (urp_len adj)⟩

theorem reqE_get {v : ℕ} (adj : Fin v → Fin v → Bool) (s : Fin v) :
    (urpOfGraph adj).arcs.get (reqE adj s) = (Fin.castAdd v s, Fin.natAdd v s, 0, true) := by
  rw [urp_get_eq]
  exact urpL_lt adj s.val _ s.isLt

theorem reqE_inj {v : ℕ} (adj : Fin v → Fin v → Bool) (a b : Fin v) :
    reqE adj a = reqE adj b ↔ a = b := by
  constructor
  · intro h
    have h2 := congrArg Fin.val h
    exact Fin.ext h2
  · rintro rfl; rfl

theorem req_eq {v : ℕ} (adj : Fin v → Fin v → Bool) (e : Fin (urpOfGraph adj).arcs.length)
    (he : (urpOfGraph adj).IsRequired e) : ∃ s : Fin v, e = reqE adj s := by
  by_cases hlt : e.val < v
  · exact ⟨⟨e.val, hlt⟩, rfl⟩
  · exfalso
    have h1 := urpL_ge adj e.val (by rw [← urp_len_eq]; exact e.isLt) (by omega)
    unfold RPInstance.IsRequired at he
    rw [urp_get_eq] at he
    rw [he] at h1
    exact Bool.noConfusion h1

end RPAux

namespace RPAux

theorem rot_ne {v : ℕ} (hv : 2 ≤ v) (i : Fin v) : finRotate v i ≠ i := by
  intro h
  have h2 := congrArg Fin.val h
  rw [finRotate_val] at h2
  by_cases hi : i.val + 1 < v
  · rw [Nat.mod_eq_of_lt hi] at h2; omega
  · have : i.val + 1 = v := by have := i.isLt; omega
    rw [this, Nat.mod_self] at h2; omega

theorem rot_rot_ne {v : ℕ} (hv : 3 ≤ v) (i : Fin v) : finRotate v (finRotate v i) ≠ i := by
  intro h
  have h2 := congrArg Fin.val h
  rw [finRotate_val, finRotate_val] at h2
  have := i.isLt
  by_cases hi : i.val + 1 < v
  · rw [Nat.mod_eq_of_lt hi] at h2
    by_cases hi2 : i.val + 1 + 1 < v
    · rw [Nat.mod_eq_of_lt hi2] at h2; omega
    · have : i.val + 1 + 1 = v := by omega
      rw [this, Nat.mod_self] at h2; omega
  · have : i.val + 1 = v := by omega
    rw [this, Nat.mod_self, Nat.mod_eq_of_lt (by omega : 0 + 1 < v)] at h2; omega

theorem urp_fwd {v : ℕ} (adj : Fin v → Fin v → Bool) (hs : IsSymm adj)
    (hv : 3 ≤ v) (hH : SchedComplexity.NoWait.HasHamiltonCircuit adj) :
    ∃ τ : List (urpOfGraph adj).Traversal, (urpOfGraph adj).IsTour false τ ∧
      (∀ e, (urpOfGraph adj).IsRequired e → τ.countP (fun t => t.1 = e) = 2) ∧
      τ.countP (fun t => ¬ (urpOfGraph adj).IsRequired t.1) = v ∧
      (∀ e, ¬ (urpOfGraph adj).IsRequired e → τ.countP (fun t => t.1 = e) ≤ 1) ∧
      (urpOfGraph adj).tourWeight τ = v := by
  obtain ⟨σ, hσ⟩ := hH
  have hedge : ∀ a b : Fin v, a ≠ b → adj a b = true → ∃ t : (urpOfGraph adj).Traversal,
      ¬ (urpOfGraph adj).IsRequired t.1 ∧ ((urpOfGraph adj).arcs.get t.1).2.2.1 = 1 ∧
      ((urpOfGraph adj).trSrc t).val = a.val ∧ ((urpOfGraph adj).trDst t).val = b.val := by
    intro a b hab h
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · obtain ⟨e, he⟩ := urp_edge_mem adj a b hlt h
      refine ⟨(e, true), ?_, ?_, ?_, ?_⟩
      · simp only [RPInstance.IsRequired, he]; simp
      · simp only [he]
      · simp only [RPInstance.trSrc, he]; simp
      · simp only [RPInstance.trDst, he]; simp
    · obtain ⟨e, he⟩ := urp_edge_mem adj b a hlt (by rw [hs]; exact h)
      refine ⟨(e, false), ?_, ?_, ?_, ?_⟩
      · simp only [RPInstance.IsRequired, he]; simp
      · simp only [he]
      · simp only [RPInstance.trSrc, he]; simp
      · simp only [RPInstance.trDst, he]; simp
  have hne : ∀ i : Fin v, σ i ≠ σ (finRotate v i) := by
    intro i h
    exact rot_ne (by omega) i (σ.injective h).symm
  choose E hEnr hEw hES hED using fun i => hedge (σ i) (σ (finRotate v i)) (hne i) (hσ i)
  have hRreq : ∀ s : Fin v, (urpOfGraph adj).IsRequired (reqE adj s) := by
    intro s; simp only [RPInstance.IsRequired, reqE_get]
  have hRS : ∀ s : Fin v, ((urpOfGraph adj).trSrc (reqE adj s, true)).val = s.val := by
    intro s; simp only [RPInstance.trSrc, reqE_get]; simp
  have hRD : ∀ s : Fin v, ((urpOfGraph adj).trDst (reqE adj s, true)).val = v + s.val := by
    intro s; simp only [RPInstance.trDst, reqE_get]; simp; omega
  have hBS : ∀ s : Fin v, ((urpOfGraph adj).trSrc (reqE adj s, false)).val = v + s.val := by
    intro s; simp only [RPInstance.trSrc, reqE_get]; simp; omega
  have hBD : ∀ s : Fin v, ((urpOfGraph adj).trDst (reqE adj s, false)).val = s.val := by
    intro s; simp only [RPInstance.trDst, reqE_get]; simp
  have hRw : ∀ s : Fin v, ((urpOfGraph adj).arcs.get (reqE adj s)).2.2.1 = 0 := by
    intro s; simp only [reqE_get]
  have hEne : ∀ i e, (urpOfGraph adj).IsRequired e → (E i).1 ≠ e := by
    intro i e he h; exact hEnr i (by rw [h]; exact he)
  refine ⟨List.ofFn (blk (fun i => (reqE adj (σ i), true)) (fun i => (reqE adj (σ i), false)) E),
    ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun h => absurd h (by simp), ?_, ?_⟩
    · apply cyc_blk
      · intro i; exact Fin.ext (by rw [hRD, hBS])
      · intro i; exact Fin.ext (by rw [hBD, hES])
      · intro i; exact Fin.ext (by rw [hED, hRS])
    · intro e he
      obtain ⟨s, rfl⟩ := req_eq adj e he
      refine ⟨true, List.mem_ofFn.2 ⟨finProdFinEquiv (σ.symm s, 0), ?_⟩⟩
      rw [blk_fpfe]
      simp
  · intro e he
    obtain ⟨s, rfl⟩ := req_eq adj e he
    rw [countP_blk]
    have : ∀ i : Fin v, ((if decide ((reqE adj (σ i), true).1 = reqE adj s) = true then 1 else 0) +
        (if decide ((reqE adj (σ i), false).1 = reqE adj s) = true then 1 else 0) +
        (if decide ((E i).1 = reqE adj s) = true then 1 else 0)) =
        if σ.symm s = i then 2 else 0 := by
      intro i
      have h3 := hEne i _ (hRreq s)
      by_cases h : σ.symm s = i
      · subst h; simp [h3]
      · have : σ i ≠ s := fun h' => h (by rw [← h']; simp)
        simp [h3, reqE_inj, this, h]
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_ite_eq]
    simp
  · rw [countP_blk]
    have : ∀ i : Fin v, ((if decide (¬ (urpOfGraph adj).IsRequired (reqE adj (σ i), true).1) = true then 1 else 0) +
        (if decide (¬ (urpOfGraph adj).IsRequired (reqE adj (σ i), false).1) = true then 1 else 0) +
        (if decide (¬ (urpOfGraph adj).IsRequired (E i).1) = true then 1 else 0)) = 1 := by
      intro i
      simp [hRreq, hEnr]
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    simp
  · intro e he
    rw [countP_blk]
    have : ∀ i : Fin v, ((if decide ((reqE adj (σ i), true).1 = e) = true then 1 else 0) +
        (if decide ((reqE adj (σ i), false).1 = e) = true then 1 else 0) +
        (if decide ((E i).1 = e) = true then 1 else 0)) =
        if (E i).1 = e then 1 else 0 := by
      intro i
      have : reqE adj (σ i) ≠ e := fun h => he (h ▸ hRreq _)
      simp [this]
    rw [Finset.sum_congr rfl (fun i _ => this i), ← Finset.card_filter]
    apply Finset.card_le_one.2
    intro i hi j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    rcases urp_arc adj e with ⟨s, hs'⟩ | ⟨a, b, hab, -, hs'⟩
    · exact absurd (by simp only [RPInstance.IsRequired, hs']) he
    have hS : ∀ d : Bool, ((urpOfGraph adj).trSrc (e, d)).val = if d then a.val else b.val := by
      intro d; cases d <;> simp only [RPInstance.trSrc, hs'] <;> simp
    have hD : ∀ d : Bool, ((urpOfGraph adj).trDst (e, d)).val = if d then b.val else a.val := by
      intro d; cases d <;> simp only [RPInstance.trDst, hs'] <;> simp
    have ti : E i = (e, (E i).2) := Prod.ext hi rfl
    have tj : E j = (e, (E j).2) := Prod.ext hj rfl
    have si := hES i; have di := hED i; have sj := hES j; have dj := hED j
    rw [ti, hS] at si; rw [ti, hD] at di; rw [tj, hS] at sj; rw [tj, hD] at dj
    have inj : ∀ x y : Fin v, (σ x).val = (σ y).val → x = y := fun x y h => σ.injective (Fin.ext h)
    generalize (E i).2 = c1 at si di
    generalize (E j).2 = c2 at sj dj
    cases c1 <;> cases c2 <;> simp only [if_true, if_false, Bool.false_eq_true] at si di sj dj
    · exact inj _ _ (by omega)
    · exfalso
      have h1 := inj i (finRotate v j) (by omega)
      have h2 := inj (finRotate v i) j (by omega)
      rw [h1] at h2
      exact rot_rot_ne hv j h2
    · exfalso
      have h1 := inj i (finRotate v j) (by omega)
      have h2 := inj (finRotate v i) j (by omega)
      rw [h1] at h2
      exact rot_rot_ne hv j h2
    · exact inj _ _ (by omega)
  · unfold RPInstance.tourWeight
    rw [List.map_ofFn, List.sum_ofFn]
    have := sum_blk (fun i => (reqE adj (σ i), true)) (fun i => (reqE adj (σ i), false)) E
      (fun t => ((urpOfGraph adj).arcs.get t.1).2.2.1)
    simp only [Function.comp] at this ⊢
    rw [this]
    simp only [hRw, hEw]
    simp

end RPAux

open RuralPostman.NPC

theorem solution {v : ℕ} (adj : Fin v → Fin v → Bool) (hs : IsSymm adj)
    (hv : 3 ≤ v) (hH : SchedComplexity.NoWait.HasHamiltonCircuit adj) :
    ∃ τ : List (urpOfGraph adj).Traversal, (urpOfGraph adj).IsTour false τ ∧
      (∀ e, (urpOfGraph adj).IsRequired e → τ.countP (fun t => t.1 = e) = 2) ∧
      τ.countP (fun t => ¬ (urpOfGraph adj).IsRequired t.1) = v ∧
      (∀ e, ¬ (urpOfGraph adj).IsRequired e → τ.countP (fun t => t.1 = e) ≤ 1) ∧
      (urpOfGraph adj).tourWeight τ = v :=
  RPAux.urp_fwd adj hs hv hH
