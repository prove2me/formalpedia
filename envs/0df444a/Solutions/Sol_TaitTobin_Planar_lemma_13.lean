-- Prove2me | solution 1 for TaitTobin.Planar.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T13:21:48.815596+00:00
-- url     : https://prove2.me/submissions/bea03427-51f6-4178-af09-a1d117cbde39

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting
import Theorems.Thm_TaitTobin_Planar_lemma_9
import Theorems.Thm_TaitTobin_Planar_lemma_10
import Theorems.Thm_TaitTobin_Planar_eq_7
import Theorems.Thm_TaitTobin_Planar_LS_counts

set_option autoImplicit false

open Matrix in
theorem wk9_transpose {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    Aᵀ = A := by
  rw [← conjTranspose_eq_transpose_of_trivial]; exact hA

open Matrix in
theorem wk9_parseval {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (x y : n → ℝ) :
    x ⬝ᵥ y = ∑ j, (WithLp.ofLp (hA.eigenvectorBasis j) ⬝ᵥ x) *
      (WithLp.ofLp (hA.eigenvectorBasis j) ⬝ᵥ y) := by
  have := hA.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at this
  rw [dotProduct_comm x y, ← this]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [dotProduct_comm y]

open Matrix in
theorem wk9_eigdot {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (j : n) (x : n → ℝ) :
    WithLp.ofLp (hA.eigenvectorBasis j) ⬝ᵥ (A *ᵥ x) =
      hA.eigenvalues j * (WithLp.ofLp (hA.eigenvectorBasis j) ⬝ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, wk9_transpose hA, dotProduct_comm,
    hA.mulVec_eigenvectorBasis, dotProduct_smul, smul_eq_mul, dotProduct_comm]

open Matrix in
theorem wk9_le {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (h : 0 < Fintype.card n) (x : n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ hA.eigenvalues₀ ⟨0, h⟩ * (x ⬝ᵥ x) := by
  rw [wk9_parseval hA x (A *ᵥ x), wk9_parseval hA x x, Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [wk9_eigdot]
  have hj : hA.eigenvalues j ≤ hA.eigenvalues₀ ⟨0, h⟩ := by
    unfold Matrix.IsHermitian.eigenvalues
    exact hA.eigenvalues₀_antitone (by rw [Fin.le_def]; exact Nat.zero_le _)
  nlinarith [mul_le_mul_of_nonneg_right hj
    (mul_self_nonneg (WithLp.ofLp (hA.eigenvectorBasis j) ⬝ᵥ x))]


open Matrix in
theorem wk9_quad {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) :
    x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) = ∑ i, ∑ j, (if G.Adj i j then x i * x j else 0) := by
  simp only [dotProduct, mulVec, SimpleGraph.adjMatrix_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  split_ifs <;> ring

open Matrix in
theorem wk9_row {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) (i : V) :
    (G.adjMatrix ℝ *ᵥ x) i = ∑ j, (if G.Adj i j then x j else 0) := by
  simp only [mulVec, dotProduct, SimpleGraph.adjMatrix_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> ring


section TTSpec

open WangKangXue.SpectralTuran Matrix

-- Quadratic form bound.
open Classical in
theorem tt_Q_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hV : 0 < Fintype.card V) (x : V → ℝ) :
    (∑ i, ∑ j, (if G.Adj i j then x i * x j else 0)) ≤ specRad G * ∑ i, x i * x i := by
  have h := wk9_le (G.isHermitian_adjMatrix ℝ) hV x
  rw [wk9_quad] at h
  unfold specRad
  rw [dif_pos hV]
  simpa [dotProduct] using h

-- A nonnegative eigenvector for the spectral radius, in row form.

-- Gain from extra edges.
open Classical in
theorem tt_gain {V : Type*} [Fintype V] (G' G'' : SimpleGraph V) (hle : G' ≤ G'')
    (y : V → ℝ) (hy : ∀ i, 0 ≤ y i) (a b : V) (hab : G''.Adj a b) (hab' : ¬ G'.Adj a b) :
    (∑ i, ∑ j, (if G'.Adj i j then y i * y j else 0)) + 2 * (y a * y b) ≤
      ∑ i, ∑ j, (if G''.Adj i j then y i * y j else 0) := by
  set D : V → V → ℝ := fun i j =>
    (if G''.Adj i j then y i * y j else 0) - (if G'.Adj i j then y i * y j else 0) with hD
  have hD0 : ∀ i j, 0 ≤ D i j := by
    intro i j
    simp only [hD]
    by_cases h1 : G'.Adj i j
    · rw [if_pos (hle h1), if_pos h1]; simp
    · rw [if_neg h1]
      split_ifs
      · simpa using mul_nonneg (hy i) (hy j)
      · simp
  have hne : a ≠ b := G''.ne_of_adj hab
  have hrow : ∀ i, D i (if i = a then b else a) ≤ ∑ j, D i j := fun i =>
    Finset.single_le_sum (fun j _ => hD0 i j) (Finset.mem_univ _)
  have h2 : D a b + D b a ≤ ∑ i, D i (if i = a then b else a) := by
    have := Finset.add_le_sum (f := fun i => D i (if i = a then b else a)) (fun i _ => hD0 _ _)
      (Finset.mem_univ a) (Finset.mem_univ b) hne
    simpa [hne.symm] using this
  have h3 : ∑ i, D i (if i = a then b else a) ≤ ∑ i, ∑ j, D i j :=
    Finset.sum_le_sum (fun i _ => hrow i)
  have hDa : D a b = y a * y b := by
    simp only [hD]; rw [if_pos hab, if_neg hab']; ring
  have hDb : D b a = y a * y b := by
    simp only [hD]
    rw [if_pos hab.symm, if_neg (fun h => hab' h.symm)]; ring
  rw [hDa, hDb] at h2
  have hsplit : ∑ i, ∑ j, D i j = (∑ i, ∑ j, (if G''.Adj i j then y i * y j else 0)) -
      ∑ i, ∑ j, (if G'.Adj i j then y i * y j else 0) := by
    simp only [hD, Finset.sum_sub_distrib]
  linarith

end TTSpec

section TTShort

open RobertsonSeymour1986.GM5

theorem tt_drawing_bounded {W : Type} [Finite W] {H : SimpleGraph W} (D : PlaneDrawing H) :
    ∃ R : ℝ, (∀ a, ‖D.vertex a‖ ≤ R) ∧
      ∀ (a b : W) (h : H.Adj a b) (t : unitInterval), ‖D.arc h t‖ ≤ R := by
  have hK : IsCompact (Set.range D.vertex ∪
      ⋃ (a : W) (b : W) (h : H.Adj a b), Set.range (D.arc h)) := by
    refine (Set.finite_range D.vertex).isCompact.union ?_
    refine isCompact_iUnion (fun a => isCompact_iUnion (fun b => isCompact_iUnion (fun h => ?_)))
    exact isCompact_range (D.arc h).continuous
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨R, fun a => ?_, fun a b h t => ?_⟩
  · have := hR (Set.mem_union_left _ (Set.mem_range_self a))
    simpa using this
  · have := hR (Set.mem_union_right _ (Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨b,
      Set.mem_iUnion.2 ⟨h, Set.mem_range_self t⟩⟩⟩))
    simpa using this

/-- Delete every edge at `u` and add the edge `xw`. -/
def ttShort {V : Type} (G : SimpleGraph V) (u x w : V) : SimpleGraph V where
  Adj a b := (G.Adj a b ∧ a ≠ u ∧ b ≠ u) ∨ (x ≠ w ∧ ((a = x ∧ b = w) ∨ (a = w ∧ b = x)))
  symm := ⟨fun a b h => by
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2 | h2⟩
    · exact Or.inl ⟨h1.symm, h3, h2⟩
    · exact Or.inr ⟨h1, Or.inr ⟨h2.2, h2.1⟩⟩
    · exact Or.inr ⟨h1, Or.inl ⟨h2.2, h2.1⟩⟩⟩
  loopless := ⟨fun a h => by
    rcases h with ⟨h1, _, _⟩ | ⟨h1, h2 | h2⟩
    · exact G.loopless.irrefl a h1
    · exact h1 (h2.1.symm.trans h2.2)
    · exact h1 (h2.2.symm.trans h2.1)⟩

theorem tt_gamma {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G) {x u w : V}
    (hxu : G.Adj x u) (huw : G.Adj u w) (hxw : x ≠ w) :
    Function.Injective ((D.arc hxu).trans (D.arc huw)) ∧
    ∀ t : unitInterval,
      (∃ s, ((D.arc hxu).trans (D.arc huw)) t = D.arc hxu s ∧ (s = 0 → t = 0)) ∨
      (∃ s, ((D.arc hxu).trans (D.arc huw)) t = D.arc huw s ∧ (s = 1 → t = 1)) := by
  have hxu' : x ≠ u := G.ne_of_adj hxu
  have huw' : u ≠ w := G.ne_of_adj huw
  refine ⟨?_, ?_⟩
  · intro t t' h
    rw [Path.trans_apply, Path.trans_apply] at h
    by_cases h1 : (t : ℝ) ≤ 1 / 2 <;> by_cases h2 : (t' : ℝ) ≤ 1 / 2
    · rw [dif_pos h1, dif_pos h2] at h
      have := D.arc_injective hxu h
      apply Subtype.ext
      have := congrArg Subtype.val this
      simp only at this
      linarith
    · rw [dif_pos h1, dif_neg h2] at h
      exfalso
      rcases D.arcs_meet_only_at_endpoints hxu huw _ _ h with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact hxu' e1
      · exact hxw e1
      · have hb : (t' : ℝ) > 1 / 2 := not_le.1 h2
        rcases e2 with e2 | e2
        · have := congrArg Subtype.val e2
          simp only [Set.Icc.coe_zero] at this
          linarith
        · rcases e1 with e1 | e1
          · rw [e1, Path.source] at h
            rw [e2, Path.target] at h
            exact hxw (D.vertex_injective h)
          · rw [e1, Path.target] at h
            rw [e2, Path.target] at h
            exact huw' (D.vertex_injective h)
    · rw [dif_neg h1, dif_pos h2] at h
      exfalso
      rcases D.arcs_meet_only_at_endpoints huw hxu _ _ h with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact huw' e2.symm
      · exact hxw e2.symm
      · have hb : (t : ℝ) > 1 / 2 := not_le.1 h1
        rcases e1 with e1 | e1
        · have := congrArg Subtype.val e1
          simp only [Set.Icc.coe_zero] at this
          linarith
        · rcases e2 with e2 | e2
          · rw [e2, Path.source] at h
            rw [e1, Path.target] at h
            exact hxw (D.vertex_injective h).symm
          · rw [e2, Path.target] at h
            rw [e1, Path.target] at h
            exact huw' (D.vertex_injective h).symm
    · rw [dif_neg h1, dif_neg h2] at h
      have := D.arc_injective huw h
      apply Subtype.ext
      have := congrArg Subtype.val this
      simp only at this
      linarith
  · intro t
    rw [Path.trans_apply]
    by_cases h1 : (t : ℝ) ≤ 1 / 2
    · rw [dif_pos h1]
      left
      refine ⟨_, rfl, fun hs => ?_⟩
      have := congrArg Subtype.val hs
      simp only [Set.Icc.coe_zero] at this
      apply Subtype.ext
      simp only [Set.Icc.coe_zero]
      linarith
    · rw [dif_neg h1]
      right
      refine ⟨_, rfl, fun hs => ?_⟩
      have := congrArg Subtype.val hs
      simp only [Set.Icc.coe_one] at this
      apply Subtype.ext
      simp only [Set.Icc.coe_one]
      linarith

open Classical in
theorem tt_short_planar {V : Type} [Finite V] (G : SimpleGraph V) (hG : IsPlanar G) (u x w : V)
    (hxu : G.Adj x u) (huw : G.Adj u w) (hxw : x ≠ w) (hnxw : ¬ G.Adj x w) :
    IsPlanar (ttShort G u x w) := by
  obtain ⟨D⟩ := hG
  obtain ⟨R, hRv, hRa⟩ := tt_drawing_bounded D
  obtain ⟨hginj, hg2⟩ := tt_gamma D hxu huw hxw
  have hxu' : x ≠ u := G.ne_of_adj hxu
  have huw' : u ≠ w := G.ne_of_adj huw
  have hwu' : w ≠ u := huw'.symm
  obtain ⟨γ, hγ⟩ : ∃ γ : Path (D.vertex x) (D.vertex w), γ = (D.arc hxu).trans (D.arc huw) :=
    ⟨_, rfl⟩
  rw [← hγ] at hginj hg2
  have hfar : R < ‖((R + 1, (0:ℝ)) : ℝ × ℝ)‖ := by
    have h1 := norm_fst_le ((R + 1, (0:ℝ)) : ℝ × ℝ)
    have h2 : R + 1 ≤ ‖R + 1‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
    simp only at h1
    linarith
  obtain ⟨pt, hpt, hptu⟩ : ∃ pt : V → ℝ × ℝ, (∀ a, a ≠ u → pt a = D.vertex a) ∧
      pt u = ((R + 1, (0:ℝ)) : ℝ × ℝ) :=
    ⟨fun a => if a = u then ((R + 1, (0:ℝ)) : ℝ × ℝ) else D.vertex a,
      fun a ha => if_neg ha, if_pos rfl⟩
  -- facts about γ
  have hγb : ∀ t, ‖γ t‖ ≤ R := by
    intro t
    rcases hg2 t with ⟨s, hs, _⟩ | ⟨s, hs, _⟩
    · rw [hs]; exact hRa _ _ _ _
    · rw [hs]; exact hRa _ _ _ _
  have hγav : ∀ t z, γ t = D.vertex z → z = x ∨ z = u ∨ z = w := by
    intro t z hz
    rcases hg2 t with ⟨s, hs, _⟩ | ⟨s, hs, _⟩
    · rw [hs] at hz
      rcases D.arc_avoids_vertices hxu s z hz with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [hs] at hz
      rcases D.arc_avoids_vertices huw s z hz with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  have hmeet : ∀ (a b : V) (ho : G.Adj a b ∧ a ≠ u ∧ b ≠ u) (s t : unitInterval),
      D.arc ho.1 s = γ t → (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1) := by
    intro a b ho s t h
    have hvu : ∀ s' : unitInterval, (s = 0 ∨ s = 1) → D.arc ho.1 s = D.vertex u → False := by
      intro s' hs h'
      rcases hs with hs | hs
      · rw [hs, Path.source] at h'
        exact ho.2.1 (D.vertex_injective h')
      · rw [hs, Path.target] at h'
        exact ho.2.2 (D.vertex_injective h')
    rcases hg2 t with ⟨s', hs', hs'0⟩ | ⟨s', hs', hs'1⟩
    · rw [hs'] at h
      rcases D.arcs_meet_only_at_endpoints ho.1 hxu s s' h with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact absurd e2 ho.2.2
      · exact absurd e1 ho.2.1
      · refine ⟨e1, ?_⟩
        rcases e2 with e2 | e2
        · exact Or.inl (hs'0 e2)
        · exfalso
          rw [e2, Path.target] at h
          exact hvu s e1 h
    · rw [hs'] at h
      rcases D.arcs_meet_only_at_endpoints ho.1 huw s s' h with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact absurd e1 ho.2.1
      · exact absurd e2 ho.2.2
      · refine ⟨e1, ?_⟩
        rcases e2 with e2 | e2
        · exfalso
          rw [e2, Path.source] at h
          exact hvu s e1 h
        · exact Or.inr (hs'1 e2)
  have hex : ∀ a b : V, (ttShort G u x w).Adj a b → ∃ p : Path (pt a) (pt b),
      (∀ ho : G.Adj a b ∧ a ≠ u ∧ b ≠ u, ∀ t, p t = D.arc ho.1 t) ∧
      (a = x → b = w → ∀ t, p t = γ t) ∧ (a = w → b = x → ∀ t, p t = γ.symm t) := by
    intro a b h
    by_cases ho : G.Adj a b ∧ a ≠ u ∧ b ≠ u
    · refine ⟨(D.arc ho.1).cast (hpt a ho.2.1) (hpt b ho.2.2), ?_, ?_, ?_⟩
      · intro ho' t
        simp [Path.cast_coe]
      · intro h1 h2
        exfalso
        have := ho.1
        rw [h1, h2] at this
        exact hnxw this
      · intro h1 h2
        exfalso
        have := ho.1
        rw [h1, h2] at this
        exact hnxw this.symm
    · have hn : x ≠ w ∧ ((a = x ∧ b = w) ∨ (a = w ∧ b = x)) := h.resolve_left ho
      rcases hn.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨γ.cast (by rw [h1]; exact hpt x hxu') (by rw [h2]; exact hpt w hwu'), ?_, ?_, ?_⟩
        · intro ho'; exact absurd ho' ho
        · intro _ _ t; simp [Path.cast_coe]
        · intro h3 _; exact absurd (h1.symm.trans h3) hxw
      · refine ⟨γ.symm.cast (by rw [h1]; exact hpt w hwu') (by rw [h2]; exact hpt x hxu'),
          ?_, ?_, ?_⟩
        · intro ho'; exact absurd ho' ho
        · intro h3 _; exact absurd (h3.symm.trans h1) hxw
        · intro _ _ t; simp [Path.cast_coe]
  choose arcF harc using hex
  have hfarN : ∀ b, b ≠ u → pt u ≠ pt b := by
    intro b hb h
    rw [hptu, hpt b hb] at h
    have := hRv b
    rw [← h] at this
    linarith
  have hfarR : ∀ p : ℝ × ℝ, ‖p‖ ≤ R → p ≠ pt u := by
    intro p hp h
    rw [hptu] at h
    rw [h] at hp
    linarith
  refine ⟨{
    vertex := pt
    vertex_injective := ?_
    arc := fun {a b} h => arcF a b h
    arc_injective := ?_
    arc_reverse := ?_
    arc_avoids_vertices := ?_
    arcs_meet_only_at_endpoints := ?_ }⟩
  · intro a b hab
    by_cases ha : a = u <;> by_cases hb : b = u
    · rw [ha, hb]
    · exact absurd (by rw [ha] at hab; exact hab) (hfarN b hb)
    · exact absurd (by rw [hb] at hab; exact hab.symm) (hfarN a ha)
    · rw [hpt a ha, hpt b hb] at hab
      exact D.vertex_injective hab
  · intro a b h t t' htt
    by_cases ho : G.Adj a b ∧ a ≠ u ∧ b ≠ u
    · have e := (harc a b h).1 ho
      rw [e t, e t'] at htt
      exact D.arc_injective ho.1 htt
    · have hn : x ≠ w ∧ ((a = x ∧ b = w) ∨ (a = w ∧ b = x)) := h.resolve_left ho
      rcases hn.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have e := (harc a b h).2.1 h1 h2
        rw [e t, e t'] at htt
        exact hginj htt
      · have e := (harc a b h).2.2 h1 h2
        rw [e t, e t'] at htt
        rw [Path.symm_apply, Path.symm_apply] at htt
        exact unitInterval.symm_inj.1 (hginj htt)
  · intro a b h
    apply Path.ext
    funext t
    show (arcF b a h.symm) t = (arcF a b h) (unitInterval.symm t)
    by_cases ho : G.Adj a b ∧ a ≠ u ∧ b ≠ u
    · have ho' : G.Adj b a ∧ b ≠ u ∧ a ≠ u := ⟨ho.1.symm, ho.2.2, ho.2.1⟩
      rw [(harc b a h.symm).1 ho' t, (harc a b h).1 ho (unitInterval.symm t)]
      have := congrArg (fun γ : Path _ _ => γ t) (D.arc_reverse ho.1)
      simpa using this
    · have hn : x ≠ w ∧ ((a = x ∧ b = w) ∨ (a = w ∧ b = x)) := h.resolve_left ho
      rcases hn.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [(harc a b h).2.1 h1 h2 (unitInterval.symm t), (harc b a h.symm).2.2 h2 h1 t]
        try rfl
      · rw [(harc a b h).2.2 h1 h2 (unitInterval.symm t), (harc b a h.symm).2.1 h2 h1 t]
        show γ t = γ (unitInterval.symm (unitInterval.symm t))
        rw [unitInterval.symm_symm]
  · intro a b h t z hz
    by_cases ho : G.Adj a b ∧ a ≠ u ∧ b ≠ u
    · have hz' : D.arc ho.1 t = pt z := by rw [← (harc a b h).1 ho t]; exact hz
      by_cases hzu : z = u
      · exfalso
        rw [hzu] at hz'
        exact hfarR _ (hRa _ _ _ _) hz'
      · rw [hpt z hzu] at hz'
        exact D.arc_avoids_vertices ho.1 t z hz'
    · have hn : x ≠ w ∧ ((a = x ∧ b = w) ∨ (a = w ∧ b = x)) := h.resolve_left ho
      rcases hn.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hz' : γ t = pt z := by rw [← (harc a b h).2.1 h1 h2 t]; exact hz
        by_cases hzu : z = u
        · exfalso
          rw [hzu] at hz'
          exact hfarR _ (hγb t) hz'
        · rw [hpt z hzu] at hz'
          rcases hγav t z hz' with h3 | h3 | h3
          · left; rw [h1]; exact h3
          · exact absurd h3 hzu
          · right; rw [h2]; exact h3
      · have hz' : γ (unitInterval.symm t) = pt z := by
          have hz0 := hz
          rw [(harc a b h).2.2 h1 h2 t] at hz0
          exact hz0
        by_cases hzu : z = u
        · exfalso
          rw [hzu] at hz'
          exact hfarR _ (hγb _) hz'
        · rw [hpt z hzu] at hz'
          rcases hγav _ z hz' with h3 | h3 | h3
          · right; rw [h2]; exact h3
          · exact absurd h3 hzu
          · left; rw [h1]; exact h3
  · have hmeet2 : ∀ (a b : V) (ho : G.Adj a b ∧ a ≠ u ∧ b ≠ u) (s t : unitInterval),
        D.arc ho.1 s = γ.symm t → (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1) := by
      intro a b ho s t hst
      rw [Path.symm_apply] at hst
      obtain ⟨p1, p2⟩ := hmeet a b ho s _ hst
      refine ⟨p1, ?_⟩
      rcases p2 with h3 | h3
      · right
        rw [← unitInterval.symm_symm t, h3, unitInterval.symm_zero]
      · left
        rw [← unitInterval.symm_symm t, h3, unitInterval.symm_one]
    intro a b a' b' h k s t hst
    by_cases ho : G.Adj a b ∧ a ≠ u ∧ b ≠ u <;> by_cases ho' : G.Adj a' b' ∧ a' ≠ u ∧ b' ≠ u
    · rw [(harc a b h).1 ho s, (harc a' b' k).1 ho' t] at hst
      exact D.arcs_meet_only_at_endpoints ho.1 ho'.1 s t hst
    · have hn : x ≠ w ∧ ((a' = x ∧ b' = w) ∨ (a' = w ∧ b' = x)) := k.resolve_left ho'
      rcases hn.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [(harc a b h).1 ho s, (harc a' b' k).2.1 h1 h2 t] at hst
        exact Or.inr (Or.inr (hmeet a b ho s t hst))
      · rw [(harc a b h).1 ho s, (harc a' b' k).2.2 h1 h2 t] at hst
        exact Or.inr (Or.inr (hmeet2 a b ho s t hst))
    · have hn : x ≠ w ∧ ((a = x ∧ b = w) ∨ (a = w ∧ b = x)) := h.resolve_left ho
      rcases hn.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [(harc a b h).2.1 h1 h2 s, (harc a' b' k).1 ho' t] at hst
        obtain ⟨q1, q2⟩ := hmeet a' b' ho' t s hst.symm
        exact Or.inr (Or.inr ⟨q2, q1⟩)
      · rw [(harc a b h).2.2 h1 h2 s, (harc a' b' k).1 ho' t] at hst
        obtain ⟨q1, q2⟩ := hmeet2 a' b' ho' t s hst.symm
        exact Or.inr (Or.inr ⟨q2, q1⟩)
    · have hn : x ≠ w ∧ ((a = x ∧ b = w) ∨ (a = w ∧ b = x)) := h.resolve_left ho
      have hn' : x ≠ w ∧ ((a' = x ∧ b' = w) ∨ (a' = w ∧ b' = x)) := k.resolve_left ho'
      rcases hn.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hn'.2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inl ⟨h1.trans h3.symm, h2.trans h4.symm⟩
      · exact Or.inr (Or.inl ⟨h1.trans h4.symm, h2.trans h3.symm⟩)
      · exact Or.inr (Or.inl ⟨h1.trans h4.symm, h2.trans h3.symm⟩)
      · exact Or.inl ⟨h1.trans h3.symm, h2.trans h4.symm⟩

end TTShort


section L11

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Planar

theorem l11_row {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → ℝ) (l : ℝ)
    (h : (G.adjMatrix ℝ).mulVec v = l • v) (i : Fin n) :
    ∑ j, (if G.Adj i j then v j else 0) = l * v i := by
  have := congrFun h i
  simpa [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply, ite_mul] using this

theorem l11_swap {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → ℝ) (l : ℝ)
    (hrow : ∀ i, ∑ j, (if G.Adj i j then v j else 0) = l * v i) :
    l * ∑ i, v i = ∑ i, (∑ j, if G.Adj i j then (1:ℝ) else 0) * v i := by
  have h1 : ∑ i, ∑ j, (if G.Adj i j then v j else 0) = l * ∑ i, v i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => hrow i)
  rw [← h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : G.Adj j i
  · have h' : G.Adj i j := h.symm
    simp [h, h']
  · have h' : ¬ G.Adj i j := fun h'' => h h''.symm
    simp [h, h']

theorem l11_between {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : Finset (Fin n))
    (hd : Disjoint X Y) :
    ∑ i ∈ X, ∑ j ∈ Y, (if G.Adj i j then (1:ℝ) else 0) ≤
      (TaitTobin.Outerplanar.eBetween G X Y : ℝ) := by
  rw [← Finset.sum_product' (f := fun i j => if G.Adj i j then (1:ℝ) else 0), Finset.sum_boole]
  have key : ((X ×ˢ Y).filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).card ≤
      TaitTobin.Outerplanar.eBetween G X Y := by
    unfold TaitTobin.Outerplanar.eBetween
    refine Finset.card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hp
      simp only [Finset.coe_filter, SimpleGraph.mem_edgeFinset, Set.mem_setOf_eq,
        SimpleGraph.mem_edgeSet]
      exact ⟨hp.2, p.1, hp.1.1, p.2, hp.1.2, rfl⟩
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hp hq
      rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · exact absurd (h1 ▸ hp.1.1) (Finset.disjoint_left.1 hd |>.mt (not_not.2 hq.1.2))
  exact_mod_cast key

theorem l11_within {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) :
    ∑ i ∈ X, ∑ j ∈ X, (if G.Adj i j then (1:ℝ) else 0) ≤
      2 * (TaitTobin.Outerplanar.eIn G X : ℝ) := by
  rw [← Finset.sum_product' (f := fun i j => if G.Adj i j then (1:ℝ) else 0), Finset.sum_boole]
  have gen : ∀ E : Finset (Sym2 (Fin n)),
      (∀ e, e ∈ E ↔ (e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ X)) →
      ((X ×ˢ X).filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).card ≤ 2 * E.card := by
    intro E hE
    calc ((X ×ˢ X).filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).card
        ≤ (E ×ˢ (Finset.univ : Finset Bool)).card := by
          refine Finset.card_le_card_of_injOn (fun p => (s(p.1, p.2), decide (p.1 < p.2))) ?_ ?_
          · intro p hp
            simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hp
            simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hE, Finset.coe_univ,
              Set.mem_univ, and_true]
            refine ⟨hp.2, ?_⟩
            intro v hv
            rcases Sym2.mem_iff.1 hv with rfl | rfl
            · exact hp.1.1
            · exact hp.1.2
          · intro p hp q hq hpq
            simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hp hq
            have hpq' := Prod.mk.inj hpq
            rcases Sym2.eq_iff.1 hpq'.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Prod.ext h1 h2
            · exfalso
              have hne : p.1 ≠ p.2 := hp.2.ne
              have h3 := hpq'.2
              rw [← h1, ← h2] at h3
              rcases lt_or_gt_of_ne hne with hlt | hgt
              · simp [hlt, not_lt.2 hlt.le] at h3
              · simp [hgt, not_lt.2 hgt.le] at h3
      _ = 2 * E.card := by rw [Finset.card_product]; simp [mul_comm]
  have key : ((X ×ˢ X).filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).card ≤
      2 * TaitTobin.Outerplanar.eIn G X := by
    unfold TaitTobin.Outerplanar.eIn
    exact gen _ (fun e => by simp)
  have := (Nat.cast_le (α := ℝ)).2 key
  push_cast at this
  exact this

theorem l11_arith (ε m s : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1/80) (hm : 100 / ε^2 ≤ m)
    (hs : s ≤ 3/2 * m)
    (h : 10 * ε * (m^2 - 3 - 8 * ε * m^2) ≤ 18 * s / ε + 4 + 8 * ε * m^2) : False := by
  have hε2 : 0 < ε^2 := by positivity
  have hm' : 100 ≤ ε^2 * m := by
    rw [div_le_iff₀ hε2] at hm; linarith
  have hε2' : ε^2 ≤ 1/6400 := by nlinarith
  have hm0 : 0 ≤ m := by
    have : 0 ≤ 100 / ε^2 := by positivity
    linarith
  have hbig : 640000 ≤ m := by nlinarith
  have e1 : ε * (18 * s / ε) = 18 * s := by field_simp
  have h' := mul_le_mul_of_nonneg_left h hε0.le
  have e2 : ε * (18 * s / ε + 4 + 8 * ε * m^2) = 18 * s + 4 * ε + 8 * ε^2 * m^2 := by
    rw [mul_add, mul_add, e1]; ring
  rw [e2] at h'
  have h3 : ε^2 * m^2 ≤ 18 * s + 4 * ε + 30 * ε^2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - 80 * ε) (mul_nonneg hε2.le (sq_nonneg m))]
  have h4 : 100 * m ≤ ε^2 * m^2 := by nlinarith
  nlinarith

end L11

section L13

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Planar

/-- Delete every edge at `u`. -/
def ttDel {V : Type} (G : SimpleGraph V) (u : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ≠ u ∧ b ≠ u
  symm := ⟨fun a b h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩

theorem l13_contra {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : TaitTobin.Outerplanar.IsSpecMax IsPlanar G)
    (v : Fin n → ℝ) (hmv : (G.adjMatrix ℝ).mulVec v = specRad G • v)
    (hpos : ∀ i, 0 < v i) (hle : ∀ i, v i ≤ 1) (hn : 0 < n)
    (u x w : Fin n) (hxu : G.Adj x u) (huw : G.Adj u w) (hxw : x ≠ w) (hnxw : ¬ G.Adj x w)
    (d : ℝ) (hd : ∑ j, (if G.Adj u j then (1:ℝ) else 0) ≤ d) :
    v x * v w ≤ v u * d := by
  have hQ : (∑ i, ∑ j, (if G.Adj i j then v i * v j else 0)) =
      specRad G * ∑ i, v i * v i := by
    rw [← wk9_quad G v, hmv, dotProduct_smul, smul_eq_mul]
    rfl
  have hpl : IsPlanar (ttShort G u x w) := tt_short_planar G hG.1 u x w hxu huw hxw hnxw
  have hle1 : specRad (ttShort G u x w) ≤ specRad G := hG.2 _ hpl
  have hQ1 := tt_Q_le (ttShort G u x w) (by simpa using hn) v
  have hss : 0 ≤ ∑ i, v i * v i := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  have hle01 : ttDel G u ≤ ttShort G u x w := fun a b h => Or.inl h
  have hH1 : (ttShort G u x w).Adj x w := Or.inr ⟨hxw, Or.inl ⟨rfl, rfl⟩⟩
  have hH0 : ¬ (ttDel G u).Adj x w := fun h => hnxw h.1
  have hgain := tt_gain (ttDel G u) (ttShort G u x w) hle01 v (fun i => (hpos i).le) x w hH1 hH0
  have h0 : ∀ a b, 0 ≤ v a * v b := fun a b => mul_nonneg (hpos a).le (hpos b).le
  have key : ∀ i j, (if G.Adj i j then v i * v j else 0) ≤
      (if (ttDel G u).Adj i j then v i * v j else 0) +
      (if i = u then (if G.Adj u j then v u * v j else 0) else 0) +
      (if j = u then (if G.Adj i u then v i * v u else 0) else 0) := by
    intro i j
    by_cases hi : i = u
    · rw [hi]
      have hnd : ¬ (ttDel G u).Adj u j := fun h => h.2.1 rfl
      simp only [hnd, if_false, if_true, zero_add]
      split_ifs <;> nlinarith [h0 u j, h0 j u]
    · by_cases hj : j = u
      · rw [hj]
        have hnd : ¬ (ttDel G u).Adj i u := fun h => h.2.2 rfl
        simp only [hnd, hi, if_false, if_true, zero_add]
        split_ifs <;> nlinarith [h0 i u]
      · have hiff : (ttDel G u).Adj i j ↔ G.Adj i j := ⟨fun h => h.1, fun h => ⟨h, hi, hj⟩⟩
        simp only [hiff, hi, hj, if_false, add_zero]
        exact le_refl _
  have hsum : (∑ i, ∑ j, (if G.Adj i j then v i * v j else 0)) ≤
      (∑ i, ∑ j, (if (ttDel G u).Adj i j then v i * v j else 0)) +
      (∑ j, (if G.Adj u j then v u * v j else 0)) +
      (∑ i, (if G.Adj i u then v i * v u else 0)) := by
    have e1 : ∑ i, ∑ j, (if i = u then (if G.Adj u j then v u * v j else 0) else 0) =
        ∑ j, (if G.Adj u j then v u * v j else 0) := by
      rw [Finset.sum_comm]; simp
    have e2 : ∑ i, ∑ j, (if j = u then (if G.Adj i u then v i * v u else 0) else 0) =
        ∑ i, (if G.Adj i u then v i * v u else 0) := by simp
    rw [← e1, ← e2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => key i j)
  have hvu0 : 0 ≤ v u := (hpos u).le
  have hf : (∑ j, (if G.Adj u j then v u * v j else 0)) ≤ v u * d := by
    calc (∑ j, (if G.Adj u j then v u * v j else 0))
        ≤ ∑ j, v u * (if G.Adj u j then (1:ℝ) else 0) :=
          Finset.sum_le_sum (fun j _ => by
            by_cases h : G.Adj u j
            · simp only [h, if_true, mul_one]
              exact mul_le_of_le_one_right hvu0 (hle j)
            · simp [h])
      _ = v u * ∑ j, (if G.Adj u j then (1:ℝ) else 0) := by rw [Finset.mul_sum]
      _ ≤ v u * d := mul_le_mul_of_nonneg_left hd hvu0
  have hg : (∑ i, (if G.Adj i u then v i * v u else 0)) ≤ v u * d := by
    calc (∑ i, (if G.Adj i u then v i * v u else 0))
        ≤ ∑ i, v u * (if G.Adj u i then (1:ℝ) else 0) :=
          Finset.sum_le_sum (fun i _ => by
            by_cases h : G.Adj u i
            · have h' : G.Adj i u := h.symm
              simp only [h, h', if_true, mul_one]
              exact mul_le_of_le_one_left hvu0 (hle i)
            · have h' : ¬ G.Adj i u := fun h'' => h h''.symm
              simp [h, h'])
      _ = v u * ∑ i, (if G.Adj u i then (1:ℝ) else 0) := by rw [Finset.mul_sum]
      _ ≤ v u * d := mul_le_mul_of_nonneg_left hd hvu0
  have hspec : specRad (ttShort G u x w) * ∑ i, v i * v i ≤ specRad G * ∑ i, v i * v i :=
    mul_le_mul_of_nonneg_right hle1 hss
  nlinarith [hQ, hQ1, hgain, hsum, hf, hg, hspec]

set_option maxHeartbeats 2000000 in
theorem l13_few {n : ℕ} (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1/80)
    (G : SimpleGraph (Fin n)) (v : Fin n → ℝ) (w : Fin n)
    (hn3 : 3 ≤ n) (hnε : (100 / ε^2)^2 ≤ (n:ℝ))
    (h9b : ∑ z ∈ Sset ε v, v z ≤ (1 + 3 * ε) * Real.sqrt (2 * (n:ℝ) - 4))
    (h10 : ∀ z : Fin n, 1 / Real.sqrt (6 * (n:ℝ)) < v z)
    (h7 : ∀ u ∈ Lset ε v,
      (v u - ε) * Real.sqrt (2 * (n:ℝ) - 4) - 18 / ε ≤
        ∑ y ∈ (Sset ε v).filter (fun y => G.Adj u y), v y)
    (hwL : w ∈ Lset ε v) (hwv : 1 - 10 * ε < v w) :
    ((((Sset ε v).filter (fun y => ¬ G.Adj y w)).card : ℕ) : ℝ) ≤ 94 * ε * n := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (2 * (n:ℝ) - 4) := ⟨_, rfl⟩
  rw [← hs] at h9b h7
  have hn3r : (3:ℝ) ≤ n := by exact_mod_cast hn3
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = Real.sqrt n := ⟨_, rfl⟩
  have hm2 : m^2 = n := by rw [hm]; exact Real.sq_sqrt (by positivity)
  have hm0 : 0 ≤ m := by rw [hm]; exact Real.sqrt_nonneg _
  have hmε : 100 / ε^2 ≤ m := by
    have := Real.sqrt_le_sqrt hnε
    rw [Real.sqrt_sq (by positivity)] at this
    rwa [← hm] at this
  have hsm : s ≤ 3/2 * m := by
    rw [hs, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith

  -- nonneighbours of w in S
  have hw7 := h7 w hwL
  have hsum : ∑ y ∈ Sset ε v, v y =
      ∑ y ∈ (Sset ε v).filter (fun y => G.Adj w y), v y +
      ∑ y ∈ (Sset ε v).filter (fun y => ¬ G.Adj w y), v y :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hU : (Sset ε v).filter (fun y => ¬ G.Adj w y) = (Sset ε v).filter (fun y => ¬ G.Adj y w) :=
    Finset.filter_congr (fun y _ => by rw [G.adj_comm])
  rw [hU] at hsum
  have hUv : ∑ y ∈ (Sset ε v).filter (fun y => ¬ G.Adj y w), v y ≤ 14 * ε * s + 18 / ε := by
    have : (1 - 11 * ε) * s ≤ (v w - ε) * s :=
      mul_le_mul_of_nonneg_right (by linarith) hs0
    nlinarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt (6 * (n:ℝ)) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact Real.sqrt_pos.2 (by positivity)
  have hrm : r ≤ 5/2 * m := by
    rw [hr, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith
  have hcard : ((((Sset ε v).filter (fun y => ¬ G.Adj y w)).card : ℕ) : ℝ) * (1 / r) ≤
      ∑ y ∈ (Sset ε v).filter (fun y => ¬ G.Adj y w), v y := by
    have : ∑ y ∈ (Sset ε v).filter (fun y => ¬ G.Adj y w), (1 / r) ≤
        ∑ y ∈ (Sset ε v).filter (fun y => ¬ G.Adj y w), v y :=
      Finset.sum_le_sum (fun y _ => by rw [hr]; exact (h10 y).le)
    simpa using this
  have hcard2 : ((((Sset ε v).filter (fun y => ¬ G.Adj y w)).card : ℕ) : ℝ) ≤
      r * (14 * ε * s + 18 / ε) := by
    have h1 : ((((Sset ε v).filter (fun y => ¬ G.Adj y w)).card : ℕ) : ℝ) / r ≤
        14 * ε * s + 18 / ε := by
      rw [div_eq_mul_one_div]; exact hcard.trans hUv
    rwa [div_le_iff₀ hr0, mul_comm] at h1
  have hε2 : 0 < ε^2 := by positivity
  have hm' : 100 ≤ ε^2 * m := by
    rw [div_le_iff₀ hε2] at hmε; linarith
  have hfin : r * (14 * ε * s + 18 / ε) ≤ 94 * ε * n := by
    have h1 : r * (14 * ε * s) ≤ 5/2 * m * (14 * ε * (3/2 * m)) := by
      have := mul_le_mul hrm (mul_le_mul_of_nonneg_left hsm (by positivity : (0:ℝ) ≤ 14 * ε))
        (by positivity) (by positivity)
      linarith
    have h2 : r * (18 / ε) ≤ 5/2 * m * (18 / ε) :=
      mul_le_mul_of_nonneg_right hrm (by positivity)
    have h3 : 45 * m / ε ≤ 41.5 * ε * m^2 := by
      rw [div_le_iff₀ hε0]
      nlinarith [mul_le_mul_of_nonneg_right hm' hm0]
    have h4 : 5/2 * m * (18 / ε) = 45 * m / ε := by ring
    rw [← hm2]
    nlinarith
  exact hcard2.trans hfin

set_option maxHeartbeats 2000000 in
theorem l13_core {n : ℕ} (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1/500)
    (G : SimpleGraph (Fin n)) (hG : TaitTobin.Outerplanar.IsSpecMax IsPlanar G)
    (v : Fin n → ℝ) (x : Fin n)
    (hn3 : 3 ≤ n) (hnε : (100 / ε^2)^2 ≤ (n:ℝ))
    (hmv : (G.adjMatrix ℝ).mulVec v = specRad G • v)
    (hpos : ∀ i, 0 < v i) (hle : ∀ i, v i ≤ 1) (hx : v x = 1)
    (h9b : ∑ z ∈ Sset ε v, v z ≤ (1 + 3 * ε) * Real.sqrt (2 * (n:ℝ) - 4))
    (h10 : ∀ z : Fin n, 1 / Real.sqrt (6 * (n:ℝ)) < v z)
    (h7 : ∀ u ∈ Lset ε v,
      (v u - ε) * Real.sqrt (2 * (n:ℝ) - 4) - 18 / ε ≤
        ∑ y ∈ (Sset ε v).filter (fun y => G.Adj u y), v y)
    (hc1 : ((Lset ε v).card : ℝ) ≤ 3 * Real.sqrt (2 * (n:ℝ) - 4) / ε)
    (hc2 : TaitTobin.Outerplanar.eBetween G (Sset ε v) (Lset ε v) ≤ 2 * n - 4)
    (hc3 : TaitTobin.Outerplanar.eIn G (Sset ε v) ≤ 3 * n - 6)
    (w : Fin n) (hw : IsSecondHub G ε v x w) : G.Adj x w := by
  by_contra hnxw
  have hε1' : ε < 1 := by linarith
  have hSm : ∀ z, z ∈ Sset ε v ↔ v z ≤ ε := fun z => by simp [Sset]
  have hLm : ∀ z, z ∈ Lset ε v ↔ ε < v z := fun z => by simp [Lset]
  have hdisj : Disjoint (Sset ε v) (Lset ε v) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [hSm] at hz; rw [hLm] at hz'; linarith
  have hunion : Sset ε v ∪ Lset ε v = Finset.univ := by
    ext z
    simp only [Finset.mem_union, hSm, hLm, Finset.mem_univ, iff_true]
    exact le_or_gt _ _
  have hsplit : ∀ f : Fin n → ℝ,
      ∑ i, f i = ∑ i ∈ Sset ε v, f i + ∑ i ∈ Lset ε v, f i := by
    intro f; rw [← Finset.sum_union hdisj, hunion]
  have hxL : x ∈ Lset ε v := (hLm x).2 (by rw [hx]; exact hε1')
  have hBx := l13_few ε hε0 (by linarith) G v x hn3 hnε h9b h10 h7 hxL (by rw [hx]; linarith)
  obtain ⟨hwL, hwx, hwv, hBw⟩ := hw
  -- numerics
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (2 * (n:ℝ) - 4) := ⟨_, rfl⟩
  rw [← hs] at hc1
  have hn3r : (3:ℝ) ≤ n := by exact_mod_cast hn3
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = Real.sqrt n := ⟨_, rfl⟩
  have hm2 : m^2 = n := by rw [hm]; exact Real.sq_sqrt (by positivity)
  have hm0 : 0 ≤ m := by rw [hm]; exact Real.sqrt_nonneg _
  have hmε : 100 / ε^2 ≤ m := by
    have := Real.sqrt_le_sqrt hnε
    rw [Real.sqrt_sq (by positivity)] at this
    rwa [← hm] at this
  have hsm : s ≤ 3/2 * m := by
    rw [hs, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith
  have hε2 : 0 < ε^2 := by positivity
  have hm' : 100 ≤ ε^2 * m := by
    rw [div_le_iff₀ hε2] at hmε; linarith
  have hLcard : ((Lset ε v).card : ℝ) ≤ ε * n := by
    refine hc1.trans ?_
    rw [div_le_iff₀ hε0]
    nlinarith [mul_le_mul_of_nonneg_right hm' hm0]
  have hcardS : ((Sset ε v).card : ℝ) + ((Lset ε v).card : ℝ) = n := by
    have := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this.symm
  -- the common neighbours
  have hsub : Sset ε v ⊆ (Sset ε v).filter (fun y => G.Adj y x ∧ G.Adj y w) ∪
      ((Sset ε v).filter (fun y => ¬ G.Adj y x) ∪ (Sset ε v).filter (fun y => ¬ G.Adj y w)) := by
    intro y hy
    by_cases h1 : G.Adj y x
    · by_cases h2 : G.Adj y w
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hy, h1, h2⟩)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hy, h2⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hy, h1⟩))
  have hcard3 : (Sset ε v).card ≤ ((Sset ε v).filter (fun y => G.Adj y x ∧ G.Adj y w)).card +
      (((Sset ε v).filter (fun y => ¬ G.Adj y x)).card +
        ((Sset ε v).filter (fun y => ¬ G.Adj y w)).card) :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (Finset.card_union_le _ _) _))
  have hcard3r : ((Sset ε v).card : ℝ) ≤ (((Sset ε v).filter (fun y => G.Adj y x ∧ G.Adj y w)).card : ℝ) +
      ((((Sset ε v).filter (fun y => ¬ G.Adj y x)).card : ℝ) +
        (((Sset ε v).filter (fun y => ¬ G.Adj y w)).card : ℝ)) := by
    exact_mod_cast hcard3
  have hnpos : (0:ℝ) < n := by linarith
  have hcardC : (n:ℝ) / 2 ≤ (((Sset ε v).filter (fun y => G.Adj y x ∧ G.Adj y w)).card : ℝ) := by
    nlinarith
  -- degrees
  obtain ⟨D, hD⟩ : ∃ D : Fin n → ℝ, ∀ i, D i = ∑ j, if G.Adj i j then (1:ℝ) else 0 :=
    ⟨_, fun _ => rfl⟩
  have hD0 : ∀ i, 0 ≤ D i := fun i => by
    rw [hD]; exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)
  have hDsplit : ∀ i, D i = ∑ j ∈ Sset ε v, (if G.Adj i j then (1:ℝ) else 0) +
      ∑ j ∈ Lset ε v, (if G.Adj i j then (1:ℝ) else 0) := fun i => by
    rw [hD]; exact hsplit _
  have hSS := l11_within G (Sset ε v)
  have hSL := l11_between G (Sset ε v) (Lset ε v) hdisj
  have hc2r : (TaitTobin.Outerplanar.eBetween G (Sset ε v) (Lset ε v) : ℝ) ≤ 2 * n := by
    have := hc2.trans (Nat.sub_le (2 * n) 4)
    exact_mod_cast this
  have hc3r : (TaitTobin.Outerplanar.eIn G (Sset ε v) : ℝ) ≤ 3 * n := by
    have := hc3.trans (Nat.sub_le (3 * n) 6)
    exact_mod_cast this
  have hDS : ∑ i ∈ Sset ε v, D i ≤ 8 * n := by
    calc ∑ i ∈ Sset ε v, D i
        = ∑ i ∈ Sset ε v, ∑ j ∈ Sset ε v, (if G.Adj i j then (1:ℝ) else 0) +
          ∑ i ∈ Sset ε v, ∑ j ∈ Lset ε v, (if G.Adj i j then (1:ℝ) else 0) := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun i _ => hDsplit i)
      _ ≤ 8 * n := by linarith
  have hCne : ((Sset ε v).filter (fun y => G.Adj y x ∧ G.Adj y w)).Nonempty := by
    rw [← Finset.card_pos]
    have : (0:ℝ) < (((Sset ε v).filter (fun y => G.Adj y x ∧ G.Adj y w)).card : ℝ) := by
      linarith
    exact_mod_cast this
  obtain ⟨u, huC, hDu⟩ : ∃ u ∈ (Sset ε v).filter (fun y => G.Adj y x ∧ G.Adj y w), D u ≤ 16 := by
    by_contra hcon
    have hcon' : ∀ y ∈ (Sset ε v).filter (fun y => G.Adj y x ∧ G.Adj y w), 16 < D y :=
      fun y hy => not_le.1 (fun h => hcon ⟨y, hy, h⟩)
    have h1 : ∑ y ∈ (Sset ε v).filter (fun y => G.Adj y x ∧ G.Adj y w), (16:ℝ) <
        ∑ y ∈ (Sset ε v).filter (fun y => G.Adj y x ∧ G.Adj y w), D y :=
      Finset.sum_lt_sum_of_nonempty hCne (fun y hy => hcon' y hy)
    have h2 : ∑ y ∈ (Sset ε v).filter (fun y => G.Adj y x ∧ G.Adj y w), D y ≤
        ∑ y ∈ Sset ε v, D y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hD0 i)
    simp only [Finset.sum_const, nsmul_eq_mul] at h1
    nlinarith
  have huS : u ∈ Sset ε v := (Finset.mem_filter.1 huC).1
  have huv : v u ≤ ε := (hSm u).1 huS
  obtain ⟨hux, huw'⟩ := (Finset.mem_filter.1 huC).2
  have hfin := l13_contra G hG v hmv hpos hle (by omega) u x w hux.symm huw' (Ne.symm hwx)
    hnxw 16 (by rw [← hD]; exact hDu)
  rw [hx] at hfin
  nlinarith

end L13

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Planar in
theorem solution : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), TaitTobin.Outerplanar.IsSpecMax IsPlanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        ∀ w : Fin n, IsSecondHub G ε v x w → G.Adj x w := by
  refine ⟨1/500, by norm_num, fun ε hε0 hε1 => ?_⟩
  obtain ⟨N9, h9⟩ := TaitTobin.Planar.lemma_9 ε hε0
  obtain ⟨N10, h10⟩ := TaitTobin.Planar.lemma_10
  obtain ⟨N7, h7⟩ := TaitTobin.Planar.eq_7 ε hε0
  obtain ⟨NL, hL⟩ := TaitTobin.Planar.LS_counts ε hε0
  refine ⟨max (max N9 N10) (max (max N7 NL) (⌈(100 / ε^2)^2⌉₊ + 3)),
    fun n hn G hG v hv hpos hle x hx w hw => ?_⟩
  have hn' := hn
  simp only [ge_iff_le, max_le_iff] at hn'
  obtain ⟨⟨hn9, hn10⟩, ⟨hn7, hnL⟩, hn3⟩ := hn'
  have hn3' : 3 ≤ n := by omega
  have hnε : (100 / ε^2)^2 ≤ (n:ℝ) := by
    have h1 : (100 / ε^2)^2 ≤ (⌈(100 / ε^2)^2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈(100 / ε^2)^2⌉₊ : ℝ) ≤ n := by
      have : ⌈(100 / ε^2)^2⌉₊ ≤ n := by omega
      exact_mod_cast this
    linarith
  exact l13_core ε hε0 (by linarith) G hG v x hn3' hnε hv hpos hle hx
    (h9 n hn9 G hG v hv hpos hle x hx).2 (fun z => (h10 n hn10 G hG v hv hpos hle x hx) z)
    (fun u hu => (h7 n hn7 G hG v hv hpos hle x hx u hu))
    (hL n hnL G hG v hv hpos hle x hx).1 (hL n hnL G hG v hv hpos hle x hx).2.1
    (hL n hnL G hG v hv hpos hle x hx).2.2.1 w hw
