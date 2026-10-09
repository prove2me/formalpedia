-- Prove2me | solution 1 for ProjSchedTW.NetPresentValue.npv_vertex_optimal_iff_tree_signs
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T22:29:49.250325+00:00
-- url     : https://prove2.me/submissions/0daacd7d-b19a-4280-a1c0-656a5f4baf9e

import Mathlib
import Definitions.Def_ProjSchedTW_NetPresentValue_Project
import Definitions.Def_ProjSchedTW_NetPresentValue_Trees

set_option autoImplicit false



namespace ProjSchedTW.NetPresentValue.P488

open ProjSchedTW.NetPresentValue

variable {n : ℕ}

abbrev Gr (EG : Finset (Fin (n + 2) × Fin (n + 2))) : SimpleGraph (Fin (n + 2)) :=
  SimpleGraph.fromRel (fun a b => (a, b) ∈ EG)

lemma reach_closed {V : Type} {G : SimpleGraph V} (R : V → Prop)
    (hc : ∀ a b, G.Adj a b → R a → R b) {u v : V} (h : G.Reachable u v) (hu : R u) : R v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hc _ _ hadj hu)

lemma mem_subtreeAway (EG : Finset (Fin (n + 2) × Fin (n + 2))) (e : Fin (n + 2) × Fin (n + 2))
    (h : Fin (n + 2)) : h ∈ subtreeAway EG e ↔ ¬ (Gr (EG.erase e)).Reachable 0 h := by
  unfold subtreeAway; simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma zero_not_mem (EG : Finset (Fin (n + 2) × Fin (n + 2))) (e : Fin (n + 2) × Fin (n + 2)) :
    (0 : Fin (n + 2)) ∉ subtreeAway EG e := by
  rw [mem_subtreeAway]; simp

/-- Lemma A: the two ends of another arc lie on the same side. -/
lemma same_side (EG : Finset (Fin (n + 2) × Fin (n + 2))) (e e' : Fin (n + 2) × Fin (n + 2))
    (he' : e' ∈ EG) (hne : e' ≠ e) (hl : e'.1 ≠ e'.2) :
    (e'.1 ∈ subtreeAway EG e ↔ e'.2 ∈ subtreeAway EG e) := by
  rw [mem_subtreeAway, mem_subtreeAway, not_iff_not]
  have hadj : (Gr (EG.erase e)).Adj e'.1 e'.2 := by
    rw [SimpleGraph.fromRel_adj]
    exact ⟨hl, Or.inl (Finset.mem_erase.2 ⟨hne, he'⟩)⟩
  exact ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩

lemma card_edgeSet_le (F : Finset (Fin (n + 2) × Fin (n + 2))) :
    Nat.card (Gr F).edgeSet ≤ F.card := by
  classical
  rw [Nat.card_coe_set_eq]
  let I : Finset (Sym2 (Fin (n + 2))) := F.image (fun p : Fin (n + 2) × Fin (n + 2) => s(p.1, p.2))
  have hsub : (Gr F).edgeSet ⊆ (↑I : Set (Sym2 (Fin (n + 2)))) := by
    intro z hz
    induction z using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj] at hz
      simp only [I, Finset.coe_image, Set.mem_image, Finset.mem_coe]
      rcases hz.2 with h | h
      · exact ⟨(a, b), h, rfl⟩
      · exact ⟨(b, a), h, Sym2.eq_swap⟩
  calc Set.ncard (Gr F).edgeSet ≤ Set.ncard (↑I : Set (Sym2 (Fin (n + 2)))) :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = I.card := Set.ncard_coe_finset _
    _ ≤ F.card := Finset.card_image_le

/-- Lemma B: removing a tree arc disconnects one of its ends from `0`. -/
lemma not_both_reach (EG : Finset (Fin (n + 2) × Fin (n + 2)))
    (hT : ProjSchedTW.StableSchedules.IsSpanningTree EG)
    (e : Fin (n + 2) × Fin (n + 2)) (he : e ∈ EG) :
    ¬ ((Gr (EG.erase e)).Reachable 0 e.1 ∧ (Gr (EG.erase e)).Reachable 0 e.2) := by
  rintro ⟨h1, h2⟩
  have hall : ∀ h, (Gr (EG.erase e)).Reachable 0 h := by
    intro h
    refine reach_closed (G := Gr EG) (fun x => (Gr (EG.erase e)).Reachable 0 x) ?_
      (hT.2.preconnected 0 h) (SimpleGraph.Reachable.refl _)
    intro a b hab ha
    rw [SimpleGraph.fromRel_adj] at hab
    obtain ⟨hne, hab⟩ := hab
    rcases hab with hab | hab
    · by_cases hae : (a, b) = e
      · subst hae; exact h2
      · exact ha.trans (SimpleGraph.Adj.reachable (by
          rw [SimpleGraph.fromRel_adj]
          exact ⟨hne, Or.inl (Finset.mem_erase.2 ⟨hae, hab⟩)⟩))
    · by_cases hae : (b, a) = e
      · subst hae; exact h1
      · exact ha.trans (SimpleGraph.Adj.reachable (by
          rw [SimpleGraph.fromRel_adj]
          exact ⟨hne, Or.inr (Finset.mem_erase.2 ⟨hae, hab⟩)⟩))
  have hconn : (Gr (EG.erase e)).Connected :=
    { preconnected := fun x y => (hall x).symm.trans (hall y) }
  have h3 := hconn.card_vert_le_card_edgeSet_add_one
  have h4 := card_edgeSet_le (EG.erase e)
  rw [Finset.card_erase_of_mem he, hT.1] at h4
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
  omega

/-- Lemma C: removing a tree arc cannot disconnect both of its ends from `0`. -/
lemma not_both_unreach (EG : Finset (Fin (n + 2) × Fin (n + 2)))
    (hT : ProjSchedTW.StableSchedules.IsSpanningTree EG)
    (e : Fin (n + 2) × Fin (n + 2)) :
    ¬ (¬ (Gr (EG.erase e)).Reachable 0 e.1 ∧ ¬ (Gr (EG.erase e)).Reachable 0 e.2) := by
  rintro ⟨h1, h2⟩
  apply h1
  refine reach_closed (G := Gr EG) (fun x => (Gr (EG.erase e)).Reachable 0 x) ?_
    (hT.2.preconnected 0 e.1) (SimpleGraph.Reachable.refl _)
  intro a b hab ha
  rw [SimpleGraph.fromRel_adj] at hab
  obtain ⟨hne, hab⟩ := hab
  rcases hab with hab | hab
  · by_cases hae : (a, b) = e
    · subst hae; exact absurd ha h1
    · exact ha.trans (SimpleGraph.Adj.reachable (by
        rw [SimpleGraph.fromRel_adj]
        exact ⟨hne, Or.inl (Finset.mem_erase.2 ⟨hae, hab⟩)⟩))
  · by_cases hae : (b, a) = e
    · subst hae; exact absurd ha h2
    · exact ha.trans (SimpleGraph.Adj.reachable (by
        rw [SimpleGraph.fromRel_adj]
        exact ⟨hne, Or.inr (Finset.mem_erase.2 ⟨hae, hab⟩)⟩))

/-- N1 in the form used below. -/
lemma xor_side (EG : Finset (Fin (n + 2) × Fin (n + 2)))
    (hT : ProjSchedTW.StableSchedules.IsSpanningTree EG)
    (e : Fin (n + 2) × Fin (n + 2)) (he : e ∈ EG) :
    (e.2 ∈ subtreeAway EG e ∧ e.1 ∉ subtreeAway EG e) ∨
      (e.2 ∉ subtreeAway EG e ∧ e.1 ∈ subtreeAway EG e) := by
  have hB := not_both_reach EG hT e he
  have hC := not_both_unreach EG hT e
  rw [mem_subtreeAway, mem_subtreeAway]
  tauto

/-- The term of arc `e` in the telescoping identity. -/
noncomputable def term (EG : Finset (Fin (n + 2) × Fin (n + 2))) (g : Fin (n + 2) → ℝ)
    (e : Fin (n + 2) × Fin (n + 2)) : ℝ := by
  classical
  exact if e.2 ∈ subtreeAway EG e then g e.2 - g e.1 else g e.1 - g e.2

noncomputable def D (EG : Finset (Fin (n + 2) × Fin (n + 2))) (g : Fin (n + 2) → ℝ)
    (h : Fin (n + 2)) : ℝ := by
  classical
  exact ∑ e ∈ EG, if h ∈ subtreeAway EG e then term EG g e else 0

lemma D_arc (EG : Finset (Fin (n + 2) × Fin (n + 2)))
    (hT : ProjSchedTW.StableSchedules.IsSpanningTree EG) (hloop : ∀ e ∈ EG, e.1 ≠ e.2)
    (g : Fin (n + 2) → ℝ) (e' : Fin (n + 2) × Fin (n + 2)) (he' : e' ∈ EG) :
    D EG g e'.2 - D EG g e'.1 = g e'.2 - g e'.1 := by
  classical
  unfold D
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single e']
  · unfold term
    rcases xor_side EG hT e' he' with ⟨h2, h1⟩ | ⟨h2, h1⟩
    · simp [h1, h2]
    · simp [h1, h2]
  · intro e he hne
    have := same_side EG e e' he' (Ne.symm hne) (hloop e' he')
    by_cases h : e'.1 ∈ subtreeAway EG e
    · have h' := this.1 h
      simp [h, h']
    · have h' : e'.2 ∉ subtreeAway EG e := fun h2 => h (this.2 h2)
      simp [h, h']
  · intro h; exact absurd he' h

/-- N2: telescoping. -/
lemma D_eq (EG : Finset (Fin (n + 2) × Fin (n + 2)))
    (hT : ProjSchedTW.StableSchedules.IsSpanningTree EG) (hloop : ∀ e ∈ EG, e.1 ≠ e.2)
    (g : Fin (n + 2) → ℝ) (h : Fin (n + 2)) : D EG g h = g h - g 0 := by
  classical
  refine reach_closed (G := Gr EG) (fun x => D EG g x = g x - g 0) ?_
    (hT.2.preconnected 0 h) ?_
  · intro a b hab ha
    rw [SimpleGraph.fromRel_adj] at hab
    rcases hab.2 with hab | hab
    · have := D_arc EG hT hloop g (a, b) hab
      simp only at this
      linarith
    · have := D_arc EG hT hloop g (b, a) hab
      simp only at this
      linarith
  · simp only [sub_self]
    unfold D
    exact Finset.sum_eq_zero (fun e _ => by simp [zero_not_mem])

/-- N3: sufficiency, for any time-feasible `S`. -/
theorem tree_signs_sufficient (P : Project n) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (c : Fin (n + 2) → ℝ) (S : Fin (n + 2) → ℝ) (hS : S ∈ timeFeasibleSet P)
    (EG : Finset (Fin (n + 2) × Fin (n + 2))) (hEG : IsAssociatedTree P EG S)
    (hsign : TreeSignCondition P β c EG S) : IsTimeOptimal P β c S := by
  classical
  refine ⟨hS, fun S' hS' => ?_⟩
  obtain ⟨hsub, hT, ⟨hS0, hbind⟩, -⟩ := hEG
  have hloop : ∀ e ∈ EG, e.1 ≠ e.2 := fun e he => P.no_loop e (hsub he)
  set a : Fin (n + 2) → ℝ := fun h => c h * β ^ (S h + (P.p h : ℝ)) with ha
  set y : Fin (n + 2) → ℝ := fun h => β ^ (S' h - S h) with hy
  have hy0 : y 0 = 1 := by simp [hy, hS'.1, hS0]
  have hsplit : ∀ h, c h * β ^ (S' h + (P.p h : ℝ)) = a h * y h := by
    intro h
    simp only [ha, hy]
    rw [mul_assoc, ← Real.rpow_add hβ0]
    congr 2; ring
  -- key identity
  have hkey : ∑ h, a h * (y h - 1) = ∑ e ∈ EG, term EG y e * subtreeNPV P β c EG e S := by
    have : ∀ h, a h * (y h - 1) = a h * D EG y h := by
      intro h; rw [D_eq EG hT hloop y h, hy0]
    rw [Finset.sum_congr rfl (fun h _ => this h)]
    unfold D
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    have hs : ∀ (s : Finset (Fin (n + 2))) (f : Fin (n + 2) → ℝ),
        ∑ h ∈ s, f h = ∑ h, if h ∈ s then f h else 0 := fun s f => by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    unfold subtreeNPV
    rw [hs (subtreeAway EG e), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    by_cases hh : h ∈ subtreeAway EG e
    · simp only [hh, if_true, ha]; ring
    · simp [hh]
  have hle : ∑ e ∈ EG, term EG y e * subtreeNPV P β c EG e S ≤ 0 := by
    refine Finset.sum_nonpos (fun e he => ?_)
    have hb := hbind e he
    have hfe := hS'.2.2 e (hsub he)
    have hmono : y e.2 ≤ y e.1 := by
      simp only [hy]
      exact Real.rpow_le_rpow_of_exponent_ge hβ0 hβ1 (by linarith)
    obtain ⟨hf, hbk⟩ := hsign e he
    unfold term
    rcases xor_side EG hT e he with ⟨h2, h1⟩ | ⟨h2, h1⟩
    · rw [if_pos h2]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hf h2)
    · rw [if_neg h2]
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (hbk h1)
  unfold npvObjective
  rw [neg_le_neg_iff]
  have : ∑ i, c i * β ^ (S' i + (P.p i : ℝ)) - ∑ i, c i * β ^ (S i + (P.p i : ℝ)) =
      ∑ h, a h * (y h - 1) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [hsplit h]; simp only [ha]; ring
  linarith

/-- N7 (cone form): if the discounted cash flows are a nonnegative combination of the incidence
vectors of the tree arcs (away from node `0`), the tree sign conditions hold. -/
theorem tree_flow_sign (P : Project n) (β : ℝ) (c : Fin (n + 2) → ℝ)
    (S : Fin (n + 2) → ℝ) (EG : Finset (Fin (n + 2) × Fin (n + 2)))
    (hT : ProjSchedTW.StableSchedules.IsSpanningTree EG) (hloop : ∀ e ∈ EG, e.1 ≠ e.2)
    (u : Fin (n + 2) × Fin (n + 2) → ℝ) (hu0 : ∀ e ∈ EG, 0 ≤ u e)
    (hbal : ∀ h : Fin (n + 2), h ≠ 0 → c h * β ^ (S h + (P.p h : ℝ)) =
      ∑ e ∈ EG, u e * ((if e.2 = h then 1 else 0) - (if e.1 = h then 1 else 0))) :
    TreeSignCondition P β c EG S := by
  classical
  intro f hf
  have key : subtreeNPV P β c EG f S = ∑ e ∈ EG, u e *
      ((if e.2 ∈ subtreeAway EG f then 1 else 0) - (if e.1 ∈ subtreeAway EG f then 1 else 0)) := by
    unfold subtreeNPV
    rw [Finset.sum_congr rfl (fun h hh => hbal h (fun h0 => zero_not_mem EG f (h0 ▸ hh))),
      Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
  have key2 : subtreeNPV P β c EG f S = u f *
      ((if f.2 ∈ subtreeAway EG f then 1 else 0) - (if f.1 ∈ subtreeAway EG f then 1 else 0)) := by
    rw [key, Finset.sum_eq_single f]
    · intro e he hne
      have := same_side EG f e he hne (hloop e he)
      by_cases h : e.1 ∈ subtreeAway EG f
      · simp [h, this.1 h]
      · have h' : e.2 ∉ subtreeAway EG f := fun h2 => h (this.2 h2)
        simp [h, h']
    · intro h; exact absurd hf h
  have hu := hu0 f hf
  unfold IsForwardArc IsBackwardArc
  rcases xor_side EG hT f hf with ⟨h2, h1⟩ | ⟨h2, h1⟩
  · refine ⟨fun _ => ?_, fun h => absurd h h1⟩
    rw [key2]; simp [h1, h2, hu]
  · refine ⟨fun h => absurd h h2, fun _ => ?_⟩
    rw [key2]; simp [h1, h2, hu]

end ProjSchedTW.NetPresentValue.P488



namespace ProjSchedTW.NetPresentValue.P488K

open Finset

/-- Conic Carathéodory: a nonnegative combination can be rewritten with an independent support. -/
theorem conic_carath {ι : Type} [Fintype ι] {m : ℕ} (v : ι → (Fin m → ℝ)) :
    ∀ (N : ℕ) (u : ι → ℝ), (univ.filter (fun i => u i ≠ 0)).card ≤ N → (∀ i, 0 ≤ u i) →
    ∃ u' : ι → ℝ, (∀ i, 0 ≤ u' i) ∧ ∑ i, u' i • v i = ∑ i, u i • v i ∧
      LinearIndependent ℝ (fun i : {i // u' i ≠ 0} => v i) := by
  classical
  intro N
  induction N with
  | zero =>
    intro u hcard hu
    refine ⟨u, hu, rfl, ?_⟩
    have hempty : ∀ i, u i = 0 := by
      intro i; by_contra h
      have hm : i ∈ univ.filter (fun i => u i ≠ 0) := by simp [h]
      have := Finset.card_pos.2 ⟨i, hm⟩; omega
    haveI : IsEmpty {i // u i ≠ 0} := ⟨fun x => x.2 (hempty x.1)⟩
    exact linearIndependent_empty_type
  | succ N ih =>
    intro u hcard hu
    by_cases hli : LinearIndependent ℝ (fun i : {i // u i ≠ 0} => v i)
    · exact ⟨u, hu, rfl, hli⟩
    obtain ⟨g, hg0, j, hj⟩ : ∃ g : {i // u i ≠ 0} → ℝ, ∑ i, g i • v i = 0 ∧ ∃ j, 0 < g j := by
      obtain ⟨g, hg0, j, hj⟩ := Fintype.not_linearIndependent_iff.1 hli
      rcases lt_or_gt_of_ne hj with h | h
      · refine ⟨fun i => - g i, ?_, j, by simpa using h⟩
        simp [neg_smul, Finset.sum_neg_distrib, hg0]
      · exact ⟨g, hg0, j, h⟩
    let lam : ι → ℝ := fun i => if h : u i ≠ 0 then g ⟨i, h⟩ else 0
    have hlam0 : ∑ i, lam i • v i = 0 := by
      rw [← hg0]
      have h1 : ∑ i, lam i • v i = ∑ i ∈ univ.filter (fun i => u i ≠ 0), lam i • v i := by
        rw [Finset.sum_filter]; refine Finset.sum_congr rfl (fun i _ => ?_)
        split_ifs with h
        · rfl
        · simp [lam, h]
      rw [h1, Finset.sum_subtype (univ.filter (fun i => u i ≠ 0)) (p := fun i => u i ≠ 0)
        (by simp)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [lam, i.2]
    set s := univ.filter (fun i => 0 < lam i) with hs
    have hjs : (j : ι) ∈ s := by simp [s, lam, j.2, hj]
    obtain ⟨i0, hi0s, hmin⟩ := s.exists_min_image (fun i => u i / lam i) ⟨j, hjs⟩
    have hi0 : 0 < lam i0 := (Finset.mem_filter.1 hi0s).2
    set t := u i0 / lam i0 with ht
    have ht0 : 0 ≤ t := div_nonneg (hu i0) hi0.le
    set u' : ι → ℝ := fun i => u i - t * lam i with hu'def
    have hu' : ∀ i, 0 ≤ u' i := by
      intro i
      by_cases hi : 0 < lam i
      · have h1 := hmin i (by simp [s, hi])
        have h2 : t * lam i ≤ u i := by rwa [le_div_iff₀ hi] at h1
        simp only [u']; linarith
      · push_neg at hi
        have : t * lam i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hi
        simp only [u']; linarith [hu i]
    have hsub : univ.filter (fun i => u' i ≠ 0) ⊂ univ.filter (fun i => u i ≠ 0) := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨i0, ?_, ?_⟩
        · have hl : lam i0 ≠ 0 := hi0.ne'
          have : u i0 ≠ 0 := by
            intro h; apply hl; simp [lam, h]
          simpa using this
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
          show u i0 - u i0 / lam i0 * lam i0 = 0
          rw [div_mul_cancel₀ _ hi0.ne', sub_self]
      · intro i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro h1 h2
        apply h1
        have : lam i = 0 := by simp [lam, h2]
        simp [u', h2, this]
    have hcard' : (univ.filter (fun i => u' i ≠ 0)).card ≤ N := by
      have := Finset.card_lt_card hsub; omega
    obtain ⟨w, hw0, hwsum, hwli⟩ := ih u' hcard' hu'
    refine ⟨w, hw0, ?_, hwli⟩
    rw [hwsum]
    simp only [u', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hlam0,
      smul_zero, sub_zero]

/-- The cone generated by finitely many vectors is closed. -/
theorem cone_closed {ι : Type} [Fintype ι] {m : ℕ} (v : ι → (Fin m → ℝ)) :
    IsClosed {x : Fin m → ℝ | ∃ u : ι → ℝ, (∀ i, 0 ≤ u i) ∧ x = ∑ i, u i • v i} := by
  classical
  have heq : {x : Fin m → ℝ | ∃ u : ι → ℝ, (∀ i, 0 ≤ u i) ∧ x = ∑ i, u i • v i} =
      ⋃ T : {T : Finset ι // LinearIndependent ℝ (fun i : T => v i)},
        (Fintype.linearCombination ℝ (fun i : T.1 => v i)) '' {w | ∀ i, 0 ≤ w i} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, Fintype.linearCombination_apply]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨u', hu', hsum, hli⟩ := conic_carath v _ u le_rfl hu
      let T := univ.filter (fun i => u' i ≠ 0)
      let e : T → {i // u' i ≠ 0} := fun i => ⟨i.1, (Finset.mem_filter.1 i.2).2⟩
      have he : Function.Injective e := fun a b hab => by
        have h2 := congrArg Subtype.val hab
        exact Subtype.ext h2
      refine ⟨⟨T, hli.comp e he⟩, fun i => u' i, fun i => hu' i, ?_⟩
      rw [← hsum, Finset.sum_coe_sort T (fun i => u' i • v i), Finset.sum_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      split_ifs with h
      · rfl
      · push_neg at h; simp [h]
    · rintro ⟨T, w, hw, rfl⟩
      refine ⟨fun i => if h : i ∈ T.1 then w ⟨i, h⟩ else 0, fun i => ?_, ?_⟩
      · by_cases h : i ∈ T.1 <;> simp [h, hw]
      · rw [← Finset.sum_subset (Finset.subset_univ T.1) (fun i _ hi => by simp [hi]),
          ← Finset.sum_coe_sort T.1]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp [i.2]
  rw [heq]
  refine isClosed_iUnion_of_finite (fun T => ?_)
  have hker : LinearMap.ker (Fintype.linearCombination ℝ (fun i : T.1 => v i)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    rw [Fintype.linearCombination_apply] at hw
    funext i
    exact Fintype.linearIndependent_iff.1 T.2 w hw i
  have hce := LinearMap.isClosedEmbedding_of_injective hker
  refine hce.isClosedMap _ ?_
  have : {w : T.1 → ℝ | ∀ i, 0 ≤ w i} = ⋂ i, {w | 0 ≤ w i} := by ext; simp
  rw [this]
  exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))

/-- K1: Farkas for a finitely generated cone, with an independent support. -/
theorem cone_farkas_indep {ι : Type} [Fintype ι] {m : ℕ} (v : ι → (Fin m → ℝ))
    (b : Fin m → ℝ)
    (h : ∀ d : Fin m → ℝ, (∀ i, ∑ k, d k * v i k ≤ 0) → ∑ k, d k * b k ≤ 0) :
    ∃ u : ι → ℝ, (∀ i, 0 ≤ u i) ∧ b = ∑ i, u i • v i ∧
      LinearIndependent ℝ (fun i : {i // u i ≠ 0} => v i) := by
  classical
  set C := {x : Fin m → ℝ | ∃ u : ι → ℝ, (∀ i, 0 ≤ u i) ∧ x = ∑ i, u i • v i} with hC
  have hbC : b ∈ C := by
    by_contra hb
    have hconv : Convex ℝ C := by
      intro x hx y hy a c ha hc _
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨w, hw, rfl⟩ := hy
      refine ⟨fun i => a * u i + c * w i, fun i => ?_, ?_⟩
      · have := hu i; have := hw i; positivity
      · simp [Finset.smul_sum, add_smul, mul_smul, Finset.sum_add_distrib]
    obtain ⟨f, r, hfC, hfb⟩ := geometric_hahn_banach_closed_point hconv (cone_closed v) hb
    have h0 : (0 : Fin m → ℝ) ∈ C := ⟨0, fun _ => le_rfl, by simp⟩
    have hr : 0 < r := by simpa using hfC 0 h0
    have hfv : ∀ i, f (v i) ≤ 0 := by
      intro i; by_contra hpos; push_neg at hpos
      have hmem : (r / f (v i)) • v i ∈ C := by
        refine ⟨fun k => if k = i then r / f (v i) else 0, fun k => ?_, ?_⟩
        · by_cases hk : k = i <;> simp [hk, div_nonneg hr.le hpos.le]
        · simp [ite_smul]
      have := hfC _ hmem
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this
      exact lt_irrefl _ this
    let d : Fin m → ℝ := fun k => f (fun j => if k = j then 1 else 0)
    have hfx : ∀ x : Fin m → ℝ, f x = ∑ k, d k * x k := by
      intro x
      have := LinearMap.pi_apply_eq_sum_univ (f : (Fin m → ℝ) →ₗ[ℝ] ℝ) x
      simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
      rw [this]
      exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
    have h1 := h d (fun i => by rw [← hfx]; exact hfv i)
    rw [← hfx] at h1
    linarith
  obtain ⟨u, hu, hub⟩ := hbC
  obtain ⟨u', hu', hsum, hli⟩ := conic_carath v _ u le_rfl hu
  exact ⟨u', hu', by rw [hub, hsum], hli⟩

end ProjSchedTW.NetPresentValue.P488K



namespace ProjSchedTW.NetPresentValue.P488K

open ProjSchedTW.NetPresentValue

variable {n : ℕ}

/-- Along a walk the schedule gap dominates the walk length; if they are equal, every arc of
the walk is binding, so any property propagating along binding arcs propagates along it. -/
lemma walk_tight (P : Project n) (S : Fin (n + 2) → ℝ)
    (hS : ∀ e ∈ P.E, (P.δ e.1 e.2 : ℝ) ≤ S e.2 - S e.1)
    (Q : Fin (n + 2) → Prop)
    (hQ : ∀ e ∈ P.E, S e.2 - S e.1 = (P.δ e.1 e.2 : ℝ) → Q e.1 → Q e.2)
    {a i : Fin (n + 2)} {w : ℤ} (hw : WalkLength P a i w) :
    (w : ℝ) ≤ S i - S a ∧ ((w : ℝ) = S i - S a → Q a → Q i) := by
  induction hw with
  | refl => simp
  | @step j l w hw hjl ih =>
    have h1 : (P.δ j l : ℝ) ≤ S l - S j := hS (j, l) hjl
    push_cast
    refine ⟨by linarith [ih.1], fun heq hQa => ?_⟩
    have hb : S l - S j = (P.δ j l : ℝ) := by linarith [ih.1]
    have hw' : (w : ℝ) = S j - S a := by linarith [ih.1]
    exact hQ (j, l) hjl hb (ih.2 hw' hQa)

lemma zero_tight (P : Project n) (S : Fin (n + 2) → ℝ) (hS : S ∈ timeFeasibleSet P)
    (hreach : ∀ i : Fin (n + 2), ∃ w : ℤ, 0 ≤ w ∧ WalkLength P 0 i w)
    (Q : Fin (n + 2) → Prop)
    (hQ : ∀ e ∈ P.E, S e.2 - S e.1 = (P.δ e.1 e.2 : ℝ) → Q e.1 → Q e.2) (hQ0 : Q 0)
    (i : Fin (n + 2)) (hi : S i = 0) : Q i := by
  obtain ⟨w, hw0, hw⟩ := hreach i
  have h := walk_tight P S hS.2.2 Q hQ hw
  have hw0' : (0 : ℝ) ≤ w := by exact_mod_cast hw0
  rw [hi, hS.1] at h
  exact h.2 (by linarith [h.1]) hQ0

lemma exists_pos_le_finset (T : Finset ℝ) (hT : ∀ t ∈ T, 0 < t) : ∃ ε > 0, ∀ t ∈ T, ε ≤ t := by
  by_cases h : T.Nonempty
  · exact ⟨T.min' h, hT _ (T.min'_mem h), fun t ht => T.min'_le t ht⟩
  · exact ⟨1, one_pos, fun t ht => absurd ⟨t, ht⟩ h⟩

/-- K3: at a vertex the binding graph is connected. -/
theorem vertex_binding_connected (P : Project n)
    (hreach : ∀ i : Fin (n + 2), ∃ w : ℤ, 0 ≤ w ∧ WalkLength P 0 i w)
    (S : Fin (n + 2) → ℝ) (hS : S ∈ (timeFeasibleSet P).extremePoints ℝ) :
    (SimpleGraph.fromRel (fun a b => (a, b) ∈ P.E ∧
      S b - S a = (P.δ a b : ℝ))).Connected := by
  classical
  set G := SimpleGraph.fromRel (fun a b => (a, b) ∈ P.E ∧ S b - S a = (P.δ a b : ℝ)) with hG
  have hSf : S ∈ timeFeasibleSet P := hS.1
  have hadjG : ∀ e ∈ P.E, S e.2 - S e.1 = (P.δ e.1 e.2 : ℝ) → G.Adj e.1 e.2 := by
    intro e he hb
    rw [hG, SimpleGraph.fromRel_adj]
    exact ⟨P.no_loop e he, Or.inl ⟨by simpa using he, hb⟩⟩
  have hall : ∀ h, G.Reachable 0 h := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨x, hx⟩ := hcon
    let X : Fin (n + 2) → Prop := fun h => ¬ G.Reachable 0 h
    have hX0 : ¬ X 0 := fun h => h (SimpleGraph.Reachable.refl 0)
    have hadjX : ∀ a b, G.Adj a b → (X a ↔ X b) := by
      intro a b hab
      simp only [X, not_iff_not]
      exact ⟨fun h => h.trans hab.reachable, fun h => h.trans hab.symm.reachable⟩
    have hpos : ∀ h, X h → 0 < S h := by
      intro h hX
      rcases (hSf.2.1 h).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; apply hX
        exact zero_tight P S hSf hreach (fun h => G.Reachable 0 h)
          (fun e he hb hr => hr.trans (hadjG e he hb).reachable)
          (SimpleGraph.Reachable.refl 0) h heq.symm
    have hcross : ∀ e ∈ P.E, ¬ (X e.1 ↔ X e.2) → (P.δ e.1 e.2 : ℝ) < S e.2 - S e.1 := by
      intro e he hx
      rcases (hSf.2.2 e he).lt_or_eq with hlt | heq
      · exact hlt
      · exact absurd (hadjX _ _ (hadjG e he heq.symm)) hx
    obtain ⟨ε, hε, hεT⟩ := exists_pos_le_finset
      ((Finset.univ.filter X).image S ∪
        (P.E.filter (fun e => ¬ (X e.1 ↔ X e.2))).image (fun e => S e.2 - S e.1 - P.δ e.1 e.2))
      (by
        intro t ht
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
          true_and] at ht
        rcases ht with ⟨h, hX, rfl⟩ | ⟨e, ⟨he, hx⟩, rfl⟩
        · exact hpos h hX
        · have := hcross e he hx; linarith)
    have hεS : ∀ h, X h → ε ≤ S h := fun h hX =>
      hεT _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨h, by simp [hX], rfl⟩))
    have hεE : ∀ e ∈ P.E, ¬ (X e.1 ↔ X e.2) → ε ≤ S e.2 - S e.1 - P.δ e.1 e.2 := fun e he hx =>
      hεT _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨e, by simp [he, hx], rfl⟩))
    let ind : Fin (n + 2) → ℝ := fun h => if X h then 1 else 0
    have hfeas : ∀ σ : ℝ, -1 ≤ σ → σ ≤ 1 →
        (fun h => S h + σ * (ε * ind h)) ∈ timeFeasibleSet P := by
      intro σ hσ1 hσ2
      have hb1 : -ε ≤ σ * ε := by nlinarith
      have hb2 : σ * ε ≤ ε := by nlinarith
      refine ⟨?_, fun h => ?_, fun e he => ?_⟩
      · simp [ind, hX0, hSf.1]
      · by_cases hX : X h
        · have := hεS h hX
          simp only [ind, hX, if_true, mul_one]; linarith
        · simp only [ind, hX, if_false, mul_zero, add_zero]; exact hSf.2.1 h
      · have h0 := hSf.2.2 e he
        by_cases h1 : X e.1 <;> by_cases h2 : X e.2
        · simp only [ind, h1, h2, if_true]; linarith
        · have := hεE e he (by tauto)
          simp only [ind, h1, h2, if_true, if_false]; linarith
        · have := hεE e he (by tauto)
          simp only [ind, h1, h2, if_true, if_false]; linarith
        · simp only [ind, h1, h2, if_false]; linarith
    have hmid := (mem_extremePoints.1 hS).2 _ (hfeas 1 (by norm_num) le_rfl)
      _ (hfeas (-1) le_rfl (by norm_num))
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by
        funext h; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring⟩
    have := congrFun hmid.1 x
    simp only [ind, show X x from hx, if_true] at this
    linarith
  rw [SimpleGraph.connected_iff]
  exact ⟨fun u v => (hall u).symm.trans (hall v), inferInstance⟩

/-- K2: first-order optimality in the multiplicative coordinates `y_h = β^{S'_h - S_h}`. -/
theorem binding_dual_ineq (P : Project n) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (c : Fin (n + 2) → ℝ)
    (hreach : ∀ i : Fin (n + 2), ∃ w : ℤ, 0 ≤ w ∧ WalkLength P 0 i w)
    (S : Fin (n + 2) → ℝ) (hopt : IsTimeOptimal P β c S)
    (d : Fin (n + 2) → ℝ) (hd0 : d 0 = 0)
    (hd : ∀ e ∈ P.E, S e.2 - S e.1 = (P.δ e.1 e.2 : ℝ) → d e.2 ≤ d e.1) :
    ∑ h, d h * (c h * β ^ (S h + (P.p h : ℝ))) ≤ 0 := by
  classical
  have hSf := hopt.1
  have hlogβ : Real.log β < 0 := Real.log_neg hβ0 hβ1
  have hdz : ∀ h, S h = 0 → d h ≤ 0 := fun h hh =>
    zero_tight P S hSf hreach (fun h => d h ≤ 0) (fun e he hb h1 => (hd e he hb).trans h1)
      (le_of_eq hd0) h hh
  obtain ⟨η, hη, hηT⟩ := exists_pos_le_finset
    ((Finset.univ.filter (fun h => 0 < S h)).image S ∪
      (P.E.filter (fun e => (P.δ e.1 e.2 : ℝ) < S e.2 - S e.1)).image
        (fun e => (S e.2 - S e.1 - P.δ e.1 e.2) / 2))
    (by
      intro t ht
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and] at ht
      rcases ht with ⟨h, hh, rfl⟩ | ⟨e, ⟨_, hx⟩, rfl⟩
      · exact hh
      · linarith)
  have hηS : ∀ h, 0 < S h → η ≤ S h := fun h hh =>
    hηT _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨h, by simp [hh], rfl⟩))
  have hηE : ∀ e ∈ P.E, (P.δ e.1 e.2 : ℝ) < S e.2 - S e.1 →
      η ≤ (S e.2 - S e.1 - P.δ e.1 e.2) / 2 := fun e he hx =>
    hηT _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨e, by simp [he, hx], rfl⟩))
  let L : ℝ → Fin (n + 2) → ℝ := fun t h => Real.log (1 + t * d h) / Real.log β
  have h2 : ∀ h, ∀ᶠ t in nhds (0 : ℝ), 0 < 1 + t * d h ∧ |L t h| < η := by
    intro h
    have hc1 : ContinuousAt (fun t : ℝ => 1 + t * d h) 0 := by fun_prop
    have hc : ContinuousAt (fun t : ℝ => Real.log (1 + t * d h) / Real.log β) 0 :=
      (hc1.log (by simp)).div_const _
    have ht1 : Filter.Tendsto (fun t : ℝ => 1 + t * d h) (nhds 0) (nhds 1) := by
      have := hc1.tendsto; simpa using this
    have ht2 : Filter.Tendsto (fun t : ℝ => Real.log (1 + t * d h) / Real.log β) (nhds 0)
        (nhds 0) := by
      have := hc.tendsto; simpa using this
    have e1 := ht1.eventually_const_lt (show (0 : ℝ) < 1 by norm_num)
    have e2 := ht2 (Metric.ball_mem_nhds 0 hη)
    filter_upwards [e1, e2] with t ht1 ht2
    refine ⟨ht1, ?_⟩
    rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq, sub_zero] at ht2
    exact ht2
  have h3 := Filter.eventually_all.2 h2
  have h1 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht0, ht⟩ := (h1.and (nhdsWithin_le_nhds h3)).exists
  let S' : Fin (n + 2) → ℝ := fun h => S h + L t h
  have hfeas : S' ∈ timeFeasibleSet P := by
    refine ⟨?_, fun h => ?_, fun e he => ?_⟩
    · simp [S', L, hd0, hSf.1]
    · rcases (hSf.2.1 h).lt_or_eq with hlt | heq
      · have := hηS h hlt
        have := (abs_lt.1 (ht h).2).1
        simp only [S']; linarith
      · have hdh := hdz h heq.symm
        have hpos := (ht h).1
        have hle : 1 + t * d h ≤ 1 := by nlinarith
        have : 0 ≤ L t h := div_nonneg_of_nonpos (Real.log_nonpos hpos.le hle) hlogβ.le
        simp only [S']; linarith
    · rcases (hSf.2.2 e he).lt_or_eq with hlt | heq
      · have := hηE e he hlt
        have a1 := abs_lt.1 (ht e.1).2
        have a2 := abs_lt.1 (ht e.2).2
        simp only [S']; linarith
      · have hde := hd e he heq.symm
        have hp1 := (ht e.1).1
        have hp2 := (ht e.2).1
        have hle : 1 + t * d e.2 ≤ 1 + t * d e.1 := by nlinarith
        have : L t e.1 ≤ L t e.2 :=
          div_le_div_of_nonpos_of_le hlogβ.le (Real.log_le_log hp2 hle)
        simp only [S']; linarith
  have hterm : ∀ h, c h * β ^ (S' h + (P.p h : ℝ)) =
      c h * β ^ (S h + (P.p h : ℝ)) + t * (d h * (c h * β ^ (S h + (P.p h : ℝ)))) := by
    intro h
    have hL : L t h = Real.logb β (1 + t * d h) := Real.log_div_log
    rw [show S' h + (P.p h : ℝ) = (S h + (P.p h : ℝ)) + L t h by simp only [S']; ring,
      Real.rpow_add hβ0, hL, Real.rpow_logb hβ0 hβ1.ne (ht h).1]
    ring
  have hobj := hopt.2 S' hfeas
  simp only [npvObjective, hterm, Finset.sum_add_distrib, ← Finset.mul_sum] at hobj
  by_contra hcon
  push_neg at hcon
  have := mul_pos ht0 hcon
  linarith

end ProjSchedTW.NetPresentValue.P488K



namespace ProjSchedTW.NetPresentValue.P488K

open ProjSchedTW.NetPresentValue

/-- Incidence vector of arc `e`: `+1` at the head, `-1` at the tail. -/
noncomputable def inc {n : ℕ} (e : Fin (n + 2) × Fin (n + 2)) : Fin (n + 2) → ℝ :=
  fun h => (if e.2 = h then 1 else 0) - (if e.1 = h then 1 else 0)

variable {n : ℕ}

/-- Unit vector at a node. -/
noncomputable def ind (x : Fin (n + 2)) : Fin (n + 2) → ℝ := fun h => if x = h then 1 else 0

lemma inc_eq (e : Fin (n + 2) × Fin (n + 2)) : inc e = ind e.2 - ind e.1 := rfl

lemma rc {V : Type} {G : SimpleGraph V} (R : V → Prop)
    (hc : ∀ a b, G.Adj a b → R a → R b) {u v : V} (h : G.Reachable u v) (hu : R u) : R v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hc _ _ hadj hu)

lemma indep_no_pair (F : Finset (Fin (n + 2) × Fin (n + 2)))
    (hind : LinearIndependent ℝ (fun e : F => inc (e : Fin (n + 2) × Fin (n + 2))))
    (e : Fin (n + 2) × Fin (n + 2)) (he : e ∈ F) (hs : e.swap ∈ F) (hne : e.1 ≠ e.2) :
    False := by
  have hx : (⟨e.swap, hs⟩ : F) ∉ ({x | x ≠ ⟨e.swap, hs⟩} : Set F) := by simp
  apply hind.notMem_span_image hx
  have hmem : inc e ∈ (fun x : F => inc (x : Fin (n + 2) × Fin (n + 2))) ''
      {x | x ≠ ⟨e.swap, hs⟩} := by
    refine ⟨⟨e, he⟩, fun h => hne ?_, rfl⟩
    have := congrArg (fun x : F => (x : Fin (n + 2) × Fin (n + 2)).1) h
    simpa using this
  have hsw : inc e.swap = - inc e := by
    funext h; simp only [inc, Prod.fst_swap, Prod.snd_swap, Pi.neg_apply]; ring
  show inc e.swap ∈ _
  rw [hsw]
  exact Submodule.neg_mem _ (Submodule.subset_span hmem)

lemma indep_acyclic (F : Finset (Fin (n + 2) × Fin (n + 2)))
    (hind : LinearIndependent ℝ (fun e : F => inc (e : Fin (n + 2) × Fin (n + 2)))) :
    (SimpleGraph.fromRel (fun a b => (a, b) ∈ F)).IsAcyclic := by
  classical
  set H := SimpleGraph.fromRel (fun a b => (a, b) ∈ F) with hH
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro a b hab
  rw [SimpleGraph.isBridge_iff]
  intro hr
  have hab' := hab
  rw [hH, SimpleGraph.fromRel_adj] at hab'
  obtain ⟨f, hfF, hfs⟩ : ∃ f ∈ F, (f.1 = a ∧ f.2 = b) ∨ (f.1 = b ∧ f.2 = a) := by
    rcases hab'.2 with hf | hf
    · exact ⟨_, hf, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, hf, Or.inr ⟨rfl, rfl⟩⟩
  set W := Submodule.span ℝ ((fun x : F => inc (x : Fin (n + 2) × Fin (n + 2))) ''
    {x | x ≠ ⟨f, hfF⟩}) with hW
  have hgen : ∀ g ∈ F, s(g.1, g.2) ≠ s(a, b) → inc g ∈ W := by
    intro g hg hgs
    refine Submodule.subset_span ⟨⟨g, hg⟩, fun heq => hgs ?_, rfl⟩
    have h1 : g = f := congrArg Subtype.val heq
    subst h1
    rw [Sym2.eq_iff]; tauto
  have hclaim : ind b - ind a ∈ W := by
    refine rc (G := H.deleteEdges {s(a, b)}) (fun x => ind x - ind a ∈ W) ?_ hr (by simp)
    intro x y hxy hx
    rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at hxy
    obtain ⟨hxyH, hns⟩ := hxy
    rw [hH, SimpleGraph.fromRel_adj] at hxyH
    rcases hxyH.2 with h | h
    · have hm := hgen (x, y) h hns
      have : ind y - ind a = (ind x - ind a) + inc (x, y) := by rw [inc_eq]; abel
      rw [this]; exact W.add_mem hx hm
    · have hm := hgen (y, x) h (by rw [Sym2.eq_swap]; exact hns)
      have : ind y - ind a = (ind x - ind a) - inc (y, x) := by rw [inc_eq]; abel
      rw [this]; exact W.sub_mem hx hm
  have hx : (⟨f, hfF⟩ : F) ∉ ({x | x ≠ ⟨f, hfF⟩} : Set F) := by simp
  apply hind.notMem_span_image hx
  show inc f ∈ W
  rcases hfs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [inc_eq, h1, h2]; exact hclaim
  · rw [inc_eq, h1, h2, show ind a - ind b = -(ind b - ind a) by abel]
    exact W.neg_mem hclaim

/-- K4: independent binding arcs extend to an associated spanning tree. -/
theorem indep_arcs_extend_to_tree (P : Project n) (S : Fin (n + 2) → ℝ)
    (hS0 : S 0 = 0)
    (hconn : (SimpleGraph.fromRel (fun a b => (a, b) ∈ P.E ∧
      S b - S a = (P.δ a b : ℝ))).Connected)
    (F : Finset (Fin (n + 2) × Fin (n + 2))) (hFE : F ⊆ P.E)
    (hFb : ∀ e ∈ F, S e.2 - S e.1 = (P.δ e.1 e.2 : ℝ))
    (hind : LinearIndependent ℝ (fun e : F => inc (e : Fin (n + 2) × Fin (n + 2)))) :
    ∃ EG, F ⊆ EG ∧ IsAssociatedTree P EG S := by
  classical
  set G := SimpleGraph.fromRel (fun a b => (a, b) ∈ P.E ∧ S b - S a = (P.δ a b : ℝ)) with hG
  set H := SimpleGraph.fromRel (fun a b => (a, b) ∈ F) with hH
  have hloopF : ∀ e ∈ F, e.1 ≠ e.2 := fun e he => P.no_loop e (hFE he)
  have hHG : H ≤ G := by
    intro x y hxy
    rw [hH, SimpleGraph.fromRel_adj] at hxy
    rw [hG, SimpleGraph.fromRel_adj]
    refine ⟨hxy.1, ?_⟩
    rcases hxy.2 with h | h
    · exact Or.inl ⟨hFE h, hFb _ h⟩
    · exact Or.inr ⟨hFE h, hFb _ h⟩
  obtain ⟨T, hHT, hTG, hT⟩ :=
    hconn.exists_isTree_le_of_le_of_isAcyclic hHG (indep_acyclic F hind)
  let ok : Fin (n + 2) × Fin (n + 2) → Prop := fun e =>
    e ∈ P.E ∧ S e.2 - S e.1 = (P.δ e.1 e.2 : ℝ)
  obtain ⟨EG, hmem⟩ : ∃ EG : Finset (Fin (n + 2) × Fin (n + 2)), ∀ e, e ∈ EG ↔
      T.Adj e.1 e.2 ∧ ok e ∧ (ok e.swap → e.swap ∉ F ∧ (e ∈ F ∨ e.1 < e.2)) :=
    ⟨Finset.univ.filter (fun e : Fin (n + 2) × Fin (n + 2) =>
      T.Adj e.1 e.2 ∧ ok e ∧ (ok e.swap → e.swap ∉ F ∧ (e ∈ F ∨ e.1 < e.2))),
      fun e => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]⟩
  have hsurj : ∀ x y, T.Adj x y → (x, y) ∈ EG ∨ (y, x) ∈ EG := by
    intro x y hxy
    have hGxy := hTG hxy
    rw [hG, SimpleGraph.fromRel_adj] at hGxy
    obtain ⟨hne, hok⟩ := hGxy
    have hok' : ok (x, y) ∨ ok (y, x) := hok
    by_cases h1 : ok (x, y) <;> by_cases h2 : ok (y, x)
    · by_cases hf1 : (x, y) ∈ F
      · left; rw [hmem]
        exact ⟨hxy, h1, fun _ => ⟨fun hs => indep_no_pair F hind (x, y) hf1 hs hne, Or.inl hf1⟩⟩
      · by_cases hf2 : (y, x) ∈ F
        · right; rw [hmem]
          exact ⟨hxy.symm, h2, fun _ =>
            ⟨fun hs => indep_no_pair F hind (y, x) hf2 hs hne.symm, Or.inl hf2⟩⟩
        · rcases lt_or_gt_of_ne hne with hlt | hlt
          · left; rw [hmem]; exact ⟨hxy, h1, fun _ => ⟨hf2, Or.inr hlt⟩⟩
          · right; rw [hmem]; exact ⟨hxy.symm, h2, fun _ => ⟨hf1, Or.inr hlt⟩⟩
    · left; rw [hmem]; exact ⟨hxy, h1, fun h => absurd h h2⟩
    · right; rw [hmem]; exact ⟨hxy.symm, h2, fun h => absurd h h1⟩
    · exact absurd hok' (by tauto)
  have hfromRel : SimpleGraph.fromRel (fun a b => (a, b) ∈ EG) = T := by
    ext x y
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨_, h | h⟩
      · exact ((hmem _).1 h).1
      · exact ((hmem _).1 h).1.symm
    · intro hxy; exact ⟨hxy.ne, hsurj x y hxy⟩
  have hcardT : T.edgeFinset.card + 1 = n + 2 := by
    have := hT.card_edgeFinset; simpa using this
  have hcard : EG.card = T.edgeFinset.card := by
    refine Finset.card_bij (fun e _ => s(e.1, e.2)) ?_ ?_ ?_
    · intro e he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact ((hmem e).1 he).1
    · intro e he e' he' heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · exfalso
        have A := (hmem e).1 he
        have B := (hmem e').1 he'
        have hsw : e' = e.swap := Prod.ext h2.symm h1.symm
        subst hsw
        have hA := A.2.2 B.2.1
        have hB := B.2.2 (by simpa using A.2.1)
        simp only [Prod.swap_swap, Prod.fst_swap, Prod.snd_swap] at hB
        rcases hA.2 with h | h
        · exact hB.1 h
        · rcases hB.2 with h' | h'
          · exact hA.1 h'
          · exact lt_asymm h h'
    · intro z hz
      rw [SimpleGraph.mem_edgeFinset] at hz
      induction z using Sym2.ind with
      | h x y =>
        rw [SimpleGraph.mem_edgeSet] at hz
        rcases hsurj x y hz with h | h
        · exact ⟨(x, y), h, rfl⟩
        · exact ⟨(y, x), h, Sym2.eq_swap⟩
  refine ⟨EG, fun e he => ?_, fun e he => ((hmem e).1 he).2.1.1, ⟨by omega, ?_⟩,
    ⟨hS0, fun e he => ((hmem e).1 he).2.1.2⟩, ?_⟩
  · have hadj : H.Adj e.1 e.2 := by
      rw [hH, SimpleGraph.fromRel_adj]
      exact ⟨hloopF e he, Or.inl (by simpa using he)⟩
    rw [hmem]
    exact ⟨hHT hadj, ⟨hFE he, hFb e he⟩, fun _ =>
      ⟨fun hs => indep_no_pair F hind e he hs (hloopF e he), Or.inl he⟩⟩
  · rw [hfromRel]; exact hT.connected
  · rintro T' ⟨hT'0, hT'e⟩
    funext x
    have hreach : (SimpleGraph.fromRel (fun a b => (a, b) ∈ EG)).Reachable 0 x := by
      rw [hfromRel]; exact hT.connected.preconnected 0 x
    refine rc (fun x => T' x = S x) ?_ hreach (by rw [hT'0, hS0])
    intro a b hab hRa
    rw [SimpleGraph.fromRel_adj] at hab
    rcases hab.2 with h | h
    · have h1 := hT'e _ h
      have h2 := ((hmem _).1 h).2.1.2
      simp only at h1 h2 hRa ⊢
      linarith
    · have h1 := hT'e _ h
      have h2 := ((hmem _).1 h).2.1.2
      simp only at h1 h2 hRa ⊢
      linarith

end ProjSchedTW.NetPresentValue.P488K

open ProjSchedTW.NetPresentValue in
theorem solution {n : ℕ} (P : Project n) (β : ℝ) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (c : Fin (n + 2) → ℝ)
    (hreach : ∀ i : Fin (n + 2), ∃ w : ℤ, 0 ≤ w ∧ WalkLength P 0 i w)
    (S : Fin (n + 2) → ℝ) (hS : S ∈ (timeFeasibleSet P).extremePoints ℝ) :
    (∀ EG : Finset (Fin (n + 2) × Fin (n + 2)), IsAssociatedTree P EG S →
      TreeSignCondition P β c EG S → IsTimeOptimal P β c S) ∧
    (β < 1 → IsTimeOptimal P β c S →
      ∃ EG : Finset (Fin (n + 2) × Fin (n + 2)), IsAssociatedTree P EG S ∧
        TreeSignCondition P β c EG S) := by
  classical
  have hSf : S ∈ timeFeasibleSet P := extremePoints_subset hS
  refine ⟨fun EG hEG hsign => P488.tree_signs_sufficient P β hβ0 hβ1 c S hSf EG hEG hsign, ?_⟩
  intro hβ1' hopt
  set a : Fin (n + 2) → ℝ := fun h => c h * β ^ (S h + (P.p h : ℝ)) with ha
  set B := P.E.filter (fun e => S e.2 - S e.1 = (P.δ e.1 e.2 : ℝ)) with hB
  let v : ({e // e ∈ B} ⊕ Bool) → (Fin (n + 2) → ℝ)
    | Sum.inl e => P488K.inc (e : Fin (n + 2) × Fin (n + 2))
    | Sum.inr true => Pi.single 0 1
    | Sum.inr false => -Pi.single 0 1
  have hdual : ∀ d : Fin (n + 2) → ℝ, (∀ i, ∑ k, d k * v i k ≤ 0) → ∑ k, d k * a k ≤ 0 := by
    intro d hd
    have h1 := hd (Sum.inr true)
    have h2 := hd (Sum.inr false)
    simp only [v, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib] at h1 h2
    rw [Finset.sum_eq_single (0 : Fin (n + 2)) (fun k _ hk => by simp [hk])
      (fun h => absurd (Finset.mem_univ _) h)] at h1 h2
    simp only [Pi.single_eq_same, mul_one] at h1 h2
    have hd0 : d 0 = 0 := by linarith
    refine P488K.binding_dual_ineq P β hβ0 hβ1' c hreach S hopt d hd0 (fun e he hb => ?_)
    have h3 := hd (Sum.inl ⟨e, Finset.mem_filter.2 ⟨he, hb⟩⟩)
    simp only [v, P488K.inc, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at h3
    linarith
  obtain ⟨u, hu0, hab, hind⟩ := P488K.cone_farkas_indep v a hdual
  let w : Fin (n + 2) × Fin (n + 2) → ℝ := fun e => if h : e ∈ B then u (Sum.inl ⟨e, h⟩) else 0
  set F := B.filter (fun e => w e ≠ 0) with hF
  have hFB : F ⊆ B := Finset.filter_subset _ _
  have hFE : F ⊆ P.E := fun e he => (Finset.mem_filter.1 (hFB he)).1
  have hFb : ∀ e ∈ F, S e.2 - S e.1 = (P.δ e.1 e.2 : ℝ) := fun e he =>
    (Finset.mem_filter.1 (hFB he)).2
  have hind' : LinearIndependent ℝ (fun e : F => P488K.inc (e : Fin (n + 2) × Fin (n + 2))) := by
    let g : F → {i // u i ≠ 0} := fun e => ⟨Sum.inl ⟨e.1, hFB e.2⟩, by
      have := (Finset.mem_filter.1 e.2).2
      simpa [w, hFB e.2] using this⟩
    have hg : Function.Injective g := by
      intro x y hxy
      simp only [g, Subtype.mk.injEq, Sum.inl.injEq] at hxy
      exact Subtype.ext hxy
    exact hind.comp g hg
  obtain ⟨EG, hFEG, hEG⟩ := P488K.indep_arcs_extend_to_tree P S hSf.1
    (P488K.vertex_binding_connected P hreach S hS) F hFE hFb hind'
  refine ⟨EG, hEG, ?_⟩
  have hloop : ∀ e ∈ EG, e.1 ≠ e.2 := fun e he => P.no_loop e (hEG.1 he)
  refine P488.tree_flow_sign P β c S EG hEG.2.1 hloop w (fun e _ => ?_) (fun h hh => ?_)
  · simp only [w]; split_ifs <;> simp [hu0]
  · -- balance at `h ≠ 0`
    have hval : a h = ∑ e ∈ B, w e * P488K.inc e h := by
      have := congrFun hab h
      rw [Finset.sum_apply, Fintype.sum_sum_type] at this
      simp only [Pi.smul_apply, smul_eq_mul, v, Fintype.univ_bool, Finset.mem_singleton,
        Finset.mem_insert, Finset.sum_insert, Finset.sum_singleton, Pi.neg_apply,
        Pi.single_apply, hh, if_false, neg_zero, mul_zero, add_zero, Bool.true_eq_false,
        not_false_eq_true] at this
      rw [this, ← Finset.sum_coe_sort B]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      simp [w, e.2]
    have hsF : ∑ e ∈ F, w e * P488K.inc e h = ∑ e ∈ B, w e * P488K.inc e h :=
      Finset.sum_subset hFB (fun e _ he => by
        have : w e = 0 := by
          by_contra hne; exact he (Finset.mem_filter.2 ⟨by assumption, hne⟩)
        simp [this])
    have hsF' : ∑ e ∈ F, w e * P488K.inc e h = ∑ e ∈ EG, w e * P488K.inc e h :=
      Finset.sum_subset hFEG (fun e _ he => by
        have : w e = 0 := by
          by_contra hne
          have heB : e ∈ B := by
            by_contra hnB; exact hne (by simp [w, hnB])
          exact he (Finset.mem_filter.2 ⟨heB, hne⟩)
        simp [this])
    have : c h * β ^ (S h + (P.p h : ℝ)) = a h := rfl
    rw [this, hval, ← hsF, hsF']
    rfl
