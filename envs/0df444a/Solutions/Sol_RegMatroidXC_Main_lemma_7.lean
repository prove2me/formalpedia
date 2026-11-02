-- Prove2me | solution 1 for RegMatroidXC.Main.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T11:21:35.722322+00:00
-- url     : https://prove2.me/submissions/fb9e657f-8ecc-49c3-814f-bd51e929f41b

import Mathlib

namespace RMXCAux7

open SimpleGraph

open Classical in
theorem lemma7_aux {V : Type} [Fintype V] (T : SimpleGraph V) (hT : T.IsTree) (w : V → ℝ) :
    ∃ v₀ : V, ∀ c : (T.induce ({v₀}ᶜ : Set V)).ConnectedComponent,
      (∑ v : ({v₀}ᶜ : Set V),
          if (T.induce ({v₀}ᶜ : Set V)).connectedComponentMk v = c then w v else 0)
        ≤ (∑ v, w v) / 2 := by
  classical
  set W := ∑ v, w v with hW
  -- reachability avoiding a vertex
  let R : V → V → V → Prop := fun v x y => ∃ p : T.Walk x y, v ∉ p.support
  have Rsymm : ∀ v x y, R v x y → R v y x := by
    rintro v x y ⟨p, hp⟩; exact ⟨p.reverse, by simpa using hp⟩
  have Rtrans : ∀ v x y z, R v x y → R v y z → R v x z := by
    rintro v x y z ⟨p, hp⟩ ⟨q, hq⟩
    refine ⟨p.append q, ?_⟩
    rw [Walk.mem_support_append_iff]; tauto
  have Rrefl : ∀ v x, x ≠ v → R v x x := by
    intro v x hx; exact ⟨Walk.nil, by simpa using hx.symm⟩
  have hreach : ∀ v (x y : ({v}ᶜ : Set V)),
      (T.induce ({v}ᶜ : Set V)).Reachable x y ↔ R v x y := by
    intro v x y
    constructor
    · rintro ⟨p⟩
      have key : ∀ (a b : ({v}ᶜ : Set V)) (p : (T.induce ({v}ᶜ : Set V)).Walk a b), R v a b := by
        intro a b p
        induction p with
        | @nil a => exact Rrefl _ _ (Set.mem_compl_singleton_iff.1 a.2)
        | @cons a c b h q ih =>
          refine Rtrans _ _ _ _ ?_ ih
          refine ⟨Walk.cons (by simpa using h) Walk.nil, ?_⟩
          simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
            or_false, not_or]
          exact ⟨fun hh => a.2 (by simp [hh]), fun hh => c.2 (by simp [hh])⟩
      exact key x y p
    · rintro ⟨p, hp⟩
      have key : ∀ (a b : V) (p : T.Walk a b) (ha : a ≠ v) (hb : b ≠ v), v ∉ p.support →
          (T.induce ({v}ᶜ : Set V)).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
        intro a b p
        induction p with
        | nil => intro ha hb _; rfl
        | @cons a c b h q ih =>
          intro ha hb hv
          rw [Walk.support_cons, List.mem_cons, not_or] at hv
          have hc : c ≠ v := by
            intro hcv; apply hv.2; rw [← hcv]; exact Walk.start_mem_support q
          refine Reachable.trans ?_ (ih hc hb hv.2)
          apply Adj.reachable
          simpa using h
      exact key x y p x.2 y.2 hp
  -- distinct neighbours of `v` are separated by `v`
  have hsep : ∀ v u1 u2, T.Adj v u1 → T.Adj v u2 → u1 ≠ u2 → ¬ R v u1 u2 := by
    rintro v u1 u2 h1 h2 hne ⟨r, hr⟩
    let r' := r.toPath
    have hr' : v ∉ (r' : T.Walk u1 u2).support := fun hh => hr (r.support_toPath_subset hh)
    let q : T.Walk u1 u2 := Walk.cons h1.symm (Walk.cons h2 Walk.nil)
    have hq : q.IsPath := by
      apply Walk.IsPath.mk'
      simp only [q, Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or]
      exact ⟨⟨h1.ne.symm, hne⟩, h2.ne, not_false⟩
    have := hT.IsAcyclic.path_unique r' ⟨q, hq⟩
    apply hr'
    rw [this]
    simp [q]
  -- translating component weights
  have hwt : ∀ v (x0 : ({v}ᶜ : Set V)),
      (∑ x : ({v}ᶜ : Set V), if (T.induce ({v}ᶜ : Set V)).connectedComponentMk x =
          (T.induce ({v}ᶜ : Set V)).connectedComponentMk x0 then w x else 0)
        = ∑ y ∈ Finset.univ.filter (fun y => y ≠ v ∧ R v x0 y), w y := by
    intro v x0
    have h1 : ∀ x : ({v}ᶜ : Set V), ((T.induce ({v}ᶜ : Set V)).connectedComponentMk x =
          (T.induce ({v}ᶜ : Set V)).connectedComponentMk x0) ↔ R v x0 x := by
      intro x
      rw [ConnectedComponent.eq, hreach]
      exact ⟨Rsymm _ _ _, Rsymm _ _ _⟩
    simp_rw [h1]
    rw [← Finset.sum_subtype (Finset.univ.filter (fun y => y ∈ ({v}ᶜ : Set V)))
      (fun y => by simp) (fun y => if R v x0 y then w y else 0)]
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases hy1 : y = v <;> by_cases hy2 : R v x0 y <;> simp [hy1, hy2]
  -- main argument
  by_contra hcon
  push Not at hcon
  have hc : ∀ v, ∃ x0 : V, x0 ≠ v ∧
      W / 2 < ∑ y ∈ Finset.univ.filter (fun y => y ≠ v ∧ R v x0 y), w y := by
    intro v
    obtain ⟨c, hc⟩ := hcon v
    induction c using ConnectedComponent.ind with
    | h x0 =>
      refine ⟨x0, x0.2, ?_⟩
      rw [← hwt v x0]; exact hc
  choose x0 hx0 hheavy using hc
  let S : V → Finset V := fun v => Finset.univ.filter (fun y => y ≠ v ∧ R v (x0 v) y)
  have : Nonempty V := hT.isConnected.nonempty
  obtain ⟨v, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun v => (S v).card)
    Finset.univ_nonempty
  have hmemS : ∀ y, y ∈ S v ↔ y ≠ v ∧ R v (x0 v) y := by intro y; simp [S]
  -- first step of a path
  have hstep : ∀ (a b : V) (p : T.Walk a b), p.IsPath → a ≠ b →
      ∃ (u : V) (_ : T.Adj a u) (q : T.Walk u b), a ∉ q.support ∧ q.support ⊆ p.support := by
    intro a b p hp hab
    cases p with
    | nil => exact absurd rfl hab
    | cons h q =>
      rw [Walk.cons_isPath_iff] at hp
      refine ⟨_, h, q, hp.2, ?_⟩
      intro z hz; rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hz
  have hpath : ∀ a b, a ≠ b → ∃ (u : V) (_ : T.Adj a u) (q : T.Walk u b), a ∉ q.support := by
    intro a b hab
    obtain ⟨p⟩ := hT.isConnected.preconnected a b
    obtain ⟨u, h, q, hq, -⟩ := hstep a b p.toPath p.toPath.2 hab
    exact ⟨u, h, q, hq⟩
  -- a neighbour of `v` in the heavy component
  obtain ⟨u, hvu, huS⟩ : ∃ u, T.Adj v u ∧ u ∈ S v := by
    obtain ⟨u, h, q, hq⟩ := hpath v (x0 v) (hx0 v).symm
    exact ⟨u, h, (hmemS u).2 ⟨h.ne.symm, Rsymm _ _ _ ⟨q, hq⟩⟩⟩
  have hRu : R v u (x0 v) := Rsymm _ _ _ ((hmemS u).1 huS).2
  have huv : u ≠ v := hvu.ne.symm
  -- characterisation of the component of `v` in `T - u`
  have hF2 : ∀ y, y ≠ u → (y ∉ S v ↔ R u v y) := by
    intro y hyu
    constructor
    · intro hyS
      by_cases hyv : y = v
      · subst hyv; exact Rrefl _ _ huv.symm
      obtain ⟨u', h, q, hq⟩ := hpath v y (Ne.symm hyv)
      have hRq : R v u' y := ⟨q, hq⟩
      by_cases hu' : u' = u
      · subst hu'
        exact absurd ((hmemS y).2 ⟨hyv, Rtrans _ _ _ _ (Rsymm _ _ _ hRu) hRq⟩) hyS
      · by_cases huq : u ∈ q.support
        · exact absurd ⟨q.takeUntil u huq,
            fun hh => hq (q.support_takeUntil_subset_support huq hh)⟩ (hsep v u' u h hvu hu')
        · refine ⟨Walk.cons h q, ?_⟩
          rw [Walk.support_cons, List.mem_cons, not_or]
          exact ⟨huv, huq⟩
    · rintro ⟨q, hq⟩ hyS
      have hyv : y ≠ v := ((hmemS y).1 hyS).1
      have hRyu : R v y u := Rtrans _ _ _ _ (Rsymm _ _ _ ((hmemS y).1 hyS).2) (Rsymm _ _ _ hRu)
      obtain ⟨u'', h, r, hr, hsub⟩ := hstep v y q.toPath q.toPath.2 (Ne.symm hyv)
      have hu'' : u'' ≠ u := by
        intro hh; apply hq; rw [← hh]
        exact q.support_toPath_subset_support (hsub (Walk.start_mem_support r))
      exact hsep v u'' u h hvu hu'' (Rtrans _ _ _ _ ⟨r, hr⟩ hRyu)
  -- the chosen heavy component at `u`
  have hlt : (S u).card < (S v).card := by
    have hnot : ¬ R u (x0 u) v := by
      intro hR
      -- then S u = complement of S v
      have hSu : S u = Finset.univ \ S v := by
        ext y
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        constructor
        · intro hy
          have hy' : y ≠ u ∧ R u (x0 u) y := by simpa [S] using hy
          exact (hF2 y hy'.1).2 (Rtrans _ _ _ _ (Rsymm _ _ _ hR) hy'.2)
        · intro hy
          have hyu : y ≠ u := by rintro rfl; exact hy huS
          have := (hF2 y hyu).1 hy
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hyu, Rtrans _ _ _ _ hR this⟩
      have h1 := hheavy u
      have h2 := hheavy v
      change W / 2 < ∑ y ∈ S u, w y at h1
      change W / 2 < ∑ y ∈ S v, w y at h2
      rw [hSu, Finset.sum_sdiff_eq_sub (Finset.subset_univ _)] at h1
      linarith
    apply Finset.card_lt_card
    refine ⟨fun y hy => ?_, fun hsub => ?_⟩
    · have hy' : y ≠ u ∧ R u (x0 u) y := by simpa [S] using hy
      by_contra hyS
      exact hnot (Rtrans _ _ _ _ hy'.2 (Rsymm _ _ _ ((hF2 y hy'.1).1 hyS)))
    · have := hsub huS
      simp [S] at this
  exact absurd (hmin u (Finset.mem_univ _)) (not_le.2 hlt)

end RMXCAux7

open Classical in
theorem solution {V : Type} [Fintype V] (T : SimpleGraph V) (hT : T.IsTree) (w : V → ℝ) :
    ∃ v₀ : V, ∀ c : (T.induce ({v₀}ᶜ : Set V)).ConnectedComponent,
      (∑ v : ({v₀}ᶜ : Set V),
          if (T.induce ({v₀}ᶜ : Set V)).connectedComponentMk v = c then w v else 0)
        ≤ (∑ v, w v) / 2 := by
  obtain ⟨v₀, h⟩ := RMXCAux7.lemma7_aux T hT w
  refine ⟨v₀, fun c => ?_⟩
  convert h c
