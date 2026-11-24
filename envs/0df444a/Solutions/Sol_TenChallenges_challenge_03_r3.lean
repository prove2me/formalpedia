-- Prove2me | solution 1 for TenChallenges.challenge_03_r3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:29:33.082324+00:00
-- url     : https://prove2.me/submissions/5a1aae30-f0d7-44a7-a7b7-feb5514c8a95
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_TenChallenges_Challenge_03
import Theorems.Thm_LefebvreVariations_ch3_small_separator
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
open TenChallenges

/-! ## Closed walks -/

/-- A closed walk of length `L` for the relation `R`. -/
private def CW {V : Type} (R : V → V → Prop) (L : ℕ) : Prop :=
  ∃ f : ℕ → V, f L = f 0 ∧ ∀ i < L, R (f i) (f (i + 1))

private lemma cw_sub {V : Type} {R : V → V → Prop} {L : ℕ} {f : ℕ → V}
    (hf : ∀ i < L, R (f i) (f (i + 1))) {a b : ℕ} (hab : a ≤ b) (hbL : b ≤ L)
    (he : f a = f b) : CW R (b - a) := by
  refine ⟨fun k => f (a + k), ?_, ?_⟩
  · simp only [Nat.add_zero]
    rw [Nat.add_sub_cancel' hab]
    exact he.symm
  · intro i hi
    have := hf (a + i) (by omega)
    simpa [Nat.add_assoc] using this


private lemma cw_min {V : Type} {R : V → V → Prop} {L : ℕ} (hL : 1 ≤ L) (h : CW R L) :
    ∃ M, 1 ≤ M ∧ M ≤ L ∧ CW R M ∧ ∀ M', 1 ≤ M' → M' < M → ¬ CW R M' := by
  classical
  have hex : ∃ M, 1 ≤ M ∧ CW R M := ⟨L, hL, h⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, Nat.find_min' hex ⟨hL, h⟩,
    (Nat.find_spec hex).2, ?_⟩
  intro M' h1 h2 hc
  exact Nat.find_min hex h2 ⟨h1, hc⟩


/-- From a closed walk to a cycle. -/
private lemma cw_cycle {V : Type} (G : Digraph V) (hloop : ∀ v, ¬ G.Adj v v) {L : ℕ}
    (hL : 1 ≤ L) (h : CW G.Adj L) : ∃ ℓ, 2 ≤ ℓ ∧ ℓ ≤ L ∧ G.HasCycleOfLength ℓ := by
  obtain ⟨M, hM1, hML, ⟨f, hf0, hf⟩, hmin⟩ := cw_min hL h
  have hinj : ∀ a b, a < b → b < M → f a ≠ f b := by
    intro a b hab hbM he
    exact hmin (b - a) (by omega) (by omega) (cw_sub hf hab.le hbM.le he)
  have hM2 : 2 ≤ M := by
    by_contra hc
    have : M = 1 := by omega
    subst this
    have := hf 0 (by omega)
    rw [hf0] at this
    exact hloop _ this
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  refine ⟨k + 1, hM2, hML, fun i => f i, ?_, ?_⟩
  · intro i j hij
    simp only at hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact hinj _ _ hlt j.isLt hij
    · exact hinj _ _ hlt i.isLt hij.symm
  · intro i
    simp only
    rw [finRotate_apply, Fin.val_add_one]
    split_ifs with hi
    · have := hf i i.isLt
      have hi' : (i : ℕ) = k := by rw [hi]; simp
      rw [hi', hf0] at this
      rwa [hi']
    · exact hf i i.isLt

/-! ## Out-balls -/

open Classical

/-- The out-boundary of `S`: vertices outside `S` with an in-neighbour in `S`. -/
private noncomputable def bd {V : Type} [Fintype V] (G : Digraph V) (S : Finset V) : Finset V :=
  Finset.univ.filter (fun w => w ∉ S ∧ ∃ s ∈ S, G.Adj s w)

/-- The out-ball of radius `j` around `v`. -/
private noncomputable def ball {V : Type} [Fintype V] (G : Digraph V) (v : V) : ℕ → Finset V
  | 0 => {v}
  | j + 1 => ball G v j ∪ bd G (ball G v j)

private lemma mem_bd {V : Type} [Fintype V] (G : Digraph V) (S : Finset V) (w : V) :
    w ∈ bd G S ↔ w ∉ S ∧ ∃ s ∈ S, G.Adj s w := by
  classical
  unfold bd
  simp

private lemma v_mem_ball {V : Type} [Fintype V] (G : Digraph V) (v : V) (j : ℕ) :
    v ∈ ball G v j := by
  induction j with
  | zero => simp [ball]
  | succ j ih => exact Finset.mem_union_left _ ih

private lemma card_ball_succ {V : Type} [Fintype V] (G : Digraph V) (v : V) (j : ℕ) :
    (ball G v (j + 1)).card = (ball G v j).card + (bd G (ball G v j)).card := by
  classical
  show (ball G v j ∪ bd G (ball G v j)).card = _
  apply Finset.card_union_of_disjoint
  rw [Finset.disjoint_left]
  intro a ha hb
  exact ((mem_bd G _ a).mp hb).1 ha

/-- Every vertex of the ball of radius `j` is the end of a walk of length `≤ j` from `v`. -/
private lemma reach {V : Type} [Fintype V] (G : Digraph V) (v : V) (j : ℕ) (w : V)
    (hw : w ∈ ball G v j) :
    ∃ f : ℕ → V, ∃ m ≤ j, f 0 = v ∧ f m = w ∧ ∀ i < m, G.Adj (f i) (f (i + 1)) := by
  classical
  induction j generalizing w with
  | zero =>
    have : w = v := by simpa [ball] using hw
    subst this
    exact ⟨fun _ => w, 0, le_rfl, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ j ih =>
    rcases Finset.mem_union.mp hw with h | h
    · obtain ⟨f, m, hm, h0, hmw, hf⟩ := ih w h
      exact ⟨f, m, by omega, h0, hmw, hf⟩
    · obtain ⟨_, s, hs, hsw⟩ := (mem_bd G _ w).mp h
      obtain ⟨f, m, hm, h0, hms, hf⟩ := ih s hs
      refine ⟨fun i => if i ≤ m then f i else w, m + 1, by omega, by simp [h0], by simp, ?_⟩
      intro i hi
      by_cases him : i < m
      · simp only [show i ≤ m by omega, show i + 1 ≤ m by omega, if_true]
        exact hf i him
      · have : i = m := by omega
        subst this
        simp only [le_refl, if_true, show ¬ (i + 1 ≤ i) by omega, if_false]
        rw [hms]
        exact hsw

/-- The ball argument: if every out-ball that misses a vertex has an out-boundary of size at
least three, a vertex of in-degree at least three lies on a short cycle. -/
private lemma ball_case {V : Type} [Fintype V] (G : Digraph V) (hloop : ∀ v, ¬ G.Adj v v)
    (v : V) (hin : 3 ≤ (Finset.univ.filter (fun w => G.Adj w v)).card)
    (hconn : ∀ S : Finset V, S.Nonempty → S ∪ bd G S ≠ Finset.univ → 3 ≤ (bd G S).card) :
    ∃ ℓ, 2 ≤ ℓ ∧ ℓ * 3 < Fintype.card V + 3 ∧ G.HasCycleOfLength ℓ := by
  classical
  by_contra hno
  push Not at hno
  set I := Finset.univ.filter (fun w => G.Adj w v) with hI
  have key : ∀ j, Disjoint (ball G v j) I ∧ 1 + 3 * j ≤ (ball G v j).card := by
    intro j
    induction j with
    | zero =>
      refine ⟨?_, by simp [ball]⟩
      rw [Finset.disjoint_left]
      intro a ha haI
      have hav : a = v := by simpa [ball] using ha
      subst hav
      exact hloop a (by simpa [hI] using haI)
    | succ j ih =>
      obtain ⟨hd, hc⟩ := ih
      have hcard : (ball G v j).card + I.card ≤ Fintype.card V := by
        rw [← Finset.card_union_of_disjoint hd]
        exact Finset.card_le_univ _
      have hd' : Disjoint (ball G v (j + 1)) I := by
        rw [Finset.disjoint_left]
        intro w hw hwI
        have hwv : G.Adj w v := by simpa [hI] using hwI
        obtain ⟨f, m, hm, h0, hmw, hf⟩ := reach G v (j + 1) w hw
        have hcw : CW G.Adj (m + 1) := by
          refine ⟨fun i => if i ≤ m then f i else v, by simp [h0], ?_⟩
          intro i hi
          by_cases him : i < m
          · simp only [show i ≤ m by omega, show i + 1 ≤ m by omega, if_true]
            exact hf i him
          · have : i = m := by omega
            subst this
            simp only [le_refl, if_true, show ¬ (i + 1 ≤ i) by omega, if_false]
            rw [hmw]
            exact hwv
        obtain ⟨ℓ, h2, hle, hcyc⟩ := cw_cycle G hloop (by omega) hcw
        exact hno ℓ h2 (by omega) hcyc
      refine ⟨hd', ?_⟩
      have hne : ball G v j ∪ bd G (ball G v j) ≠ Finset.univ := by
        intro h
        obtain ⟨w, hw⟩ : I.Nonempty := Finset.card_pos.mp (by omega)
        have : w ∈ ball G v (j + 1) := by
          show w ∈ ball G v j ∪ bd G (ball G v j)
          rw [h]
          exact Finset.mem_univ _
        exact Finset.disjoint_left.mp hd' this hw
      have h3 := hconn _ ⟨v, v_mem_ball G v j⟩ hne
      have := card_ball_succ G v j
      omega
  have h1 := (key (Fintype.card V)).2
  have h2 := Finset.card_le_univ (ball G v (Fintype.card V))
  omega

/-- Some vertex has in-degree at least three. -/
private lemma exists_indeg {V : Type} [Fintype V] [Nonempty V] (G : Digraph V)
    (hdeg : ∀ v, 3 ≤ G.outDegree v) :
    ∃ v, 3 ≤ (Finset.univ.filter (fun w => G.Adj w v)).card := by
  classical
  have hout : ∀ v, 3 ≤ (Finset.univ.filter (fun w => G.Adj v w)).card := by
    intro v
    have := hdeg v
    unfold Digraph.outDegree at this
    have e : {w | G.Adj v w} = ↑(Finset.univ.filter (fun w => G.Adj v w)) := by ext; simp
    rwa [e, Set.ncard_coe_finset] at this
  have hsum := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (Finset.univ : Finset V)) (t := (Finset.univ : Finset V)) (r := G.Adj)
  have hle : ∑ _v ∈ (Finset.univ : Finset V), 3 ≤
      ∑ v ∈ (Finset.univ : Finset V), (Finset.univ.filter (fun w => G.Adj w v)).card := by
    calc ∑ _v ∈ (Finset.univ : Finset V), 3
        ≤ ∑ v ∈ (Finset.univ : Finset V), (Finset.univ.filter (fun w => G.Adj v w)).card :=
          Finset.sum_le_sum (fun v _ => hout v)
      _ = _ := by
          unfold Finset.bipartiteAbove Finset.bipartiteBelow at hsum
          exact hsum
  obtain ⟨v, _, hv⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hle
  exact ⟨v, hv⟩

/-! ## Induction on the number of vertices -/

/-- The statement for digraphs with exactly `m` vertices. -/
private def P3 (m : ℕ) : Prop :=
  ∀ {W : Type} [Fintype W] [Nonempty W] (H : Digraph W), Fintype.card W = m →
    (∀ v, ¬ H.Adj v v) → (∀ v, 3 ≤ H.outDegree v) →
      ∃ ℓ, 2 ≤ ℓ ∧ ℓ * 3 < m + 3 ∧ H.HasCycleOfLength ℓ

/-- A nonempty set with no arc leaving it carries a smaller digraph of minimum out-degree
three. -/
private lemma closed_case {V : Type} [Fintype V] (G : Digraph V) (n : ℕ)
    (IH : ∀ m < n, P3 m) (hn : Fintype.card V = n) (hloop : ∀ v, ¬ G.Adj v v)
    (hdeg : ∀ v, 3 ≤ G.outDegree v) (S : Finset V) (hS : S.Nonempty)
    (hcl : ∀ a ∈ S, ∀ w, G.Adj a w → w ∈ S) (hne : S ≠ Finset.univ) :
    ∃ ℓ, 2 ≤ ℓ ∧ ℓ * 3 < Fintype.card V + 3 ∧ G.HasCycleOfLength ℓ := by
  let W := {x // x ∈ S}
  have : Nonempty W := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  let H : Digraph W := ⟨fun a b => G.Adj a.1 b.1⟩
  have hcardW : Fintype.card W = S.card := Fintype.card_coe S
  have hlt : S.card < n := by
    rw [← hn]
    exact Finset.card_lt_univ_of_notMem (Classical.choose_spec
      (show ∃ x, x ∉ S by
        by_contra h
        push Not at h
        exact hne (Finset.eq_univ_iff_forall.mpr h)))
  have hdegH : ∀ a : W, 3 ≤ H.outDegree a := by
    intro a
    have e : Subtype.val '' {b : W | H.Adj a b} = {w | G.Adj a.1 w} := by
      ext w
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact hb
      · intro hw
        exact ⟨⟨w, hcl a.1 a.2 w hw⟩, hw, rfl⟩
    have := hdeg a.1
    unfold Digraph.outDegree at this ⊢
    rw [← e, Set.ncard_image_of_injective _ Subtype.val_injective] at this
    exact this
  obtain ⟨ℓ, h2, hlen, f, hf, hadj⟩ := IH S.card hlt H hcardW (fun a => hloop a.1) hdegH
  refine ⟨ℓ, h2, by omega, fun i => (f i).1, ?_, fun i => hadj i⟩
  intro i j hij
  exact hf (Subtype.val_injective hij)

/-! ## The case of a small out-separator (child lemma) -/

/-- A nonempty set `S` whose out-boundary has one or two vertices and leaves some vertex
outside `S` and its boundary: this is `LefebvreVariations.ch3_small_separator`, once `bd G S`
is written out. -/
private lemma separator_case {V : Type} [Fintype V] (G : Digraph V)
    (hloop : ∀ v, ¬ G.Adj v v) (hdeg : ∀ v, 3 ≤ G.outDegree v) (S : Finset V)
    (hS : S.Nonempty) (hcov : S ∪ bd G S ≠ Finset.univ) (hpos : 1 ≤ (bd G S).card)
    (hsmall : (bd G S).card ≤ 2) :
    ∃ ℓ, 2 ≤ ℓ ∧ ℓ * 3 < Fintype.card V + 3 ∧ G.HasCycleOfLength ℓ := by
  have hbd : bd G S = Finset.univ.filter (fun y => y ∉ S ∧ ∃ x ∈ S, G.Adj x y) := by
    ext y
    simp [mem_bd]
  rw [hbd] at hcov hpos hsmall
  exact LefebvreVariations.ch3_small_separator G hloop hdeg S hS hpos hsmall hcov

private lemma main (n : ℕ) : P3 n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro V _ _ G hn hloop hdeg
    rw [← hn]
    by_cases hconn : ∀ S : Finset V, S.Nonempty → S ∪ bd G S ≠ Finset.univ →
        3 ≤ (bd G S).card
    · obtain ⟨v, hv⟩ := exists_indeg G hdeg
      exact ball_case G hloop v hv hconn
    · push Not at hconn
      obtain ⟨S, hS, hcov, hsmall⟩ := hconn
      by_cases h0 : (bd G S).card = 0
      · have hbd : bd G S = ∅ := Finset.card_eq_zero.mp h0
        refine closed_case G n IH hn hloop hdeg S hS ?_ ?_
        · intro a ha w hw
          by_contra hwS
          have : w ∈ bd G S := (mem_bd G S w).mpr ⟨hwS, a, ha, hw⟩
          rw [hbd] at this
          simp at this
        · intro h
          apply hcov
          rw [hbd, h]
          simp
      · exact separator_case G hloop hdeg S hS hcov (by omega) (by omega)

theorem solution : TenChallenges.statement_03 3 := by
  intro _ V _ _ G hloop hdeg
  exact main _ G rfl hloop hdeg
