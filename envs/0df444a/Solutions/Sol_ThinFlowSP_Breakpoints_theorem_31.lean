-- Prove2me | solution 1 for ThinFlowSP.Breakpoints.theorem_31
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T08:26:58.48522+00:00
-- url     : https://prove2.me/submissions/45c5fc2d-17c3-49d5-aa22-e1143524f9e8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Model
import Theorems.Thm_ThinFlowSP_Breakpoints_lemma_29
import Theorems.Thm_ThinFlowSP_Breakpoints_lemma_30
import Theorems.Thm_ThinFlowSP_Breakpoints_proposition_17
import Theorems.Thm_ThinFlowSP_Breakpoints_corollary_15

namespace ThinFlowSP.Breakpoints


/-- structural property of SP nets -/
def SPGood (G : Net) : Prop :=
  (∃ h : G.V → ℝ, h G.s = 0 ∧ h G.t = 1 ∧ ∀ a, h (G.tail a) < h (G.head a)) ∧
  (∀ v, Reaches G G.s v) ∧ (∀ v, Reaches G v G.t)

theorem reaches_map {G H : Net} (f : G.V → H.V) (g : G.A → H.A)
    (ht : ∀ a, H.tail (g a) = f (G.tail a)) (hh : ∀ a, H.head (g a) = f (G.head a))
    {u v : G.V} (huv : Reaches G u v) : Reaches H (f u) (f v) := by
  unfold Reaches at *
  refine huv.lift f ?_
  rintro x y ⟨a, rfl, rfl⟩
  exact ⟨g a, ht a, hh a⟩

theorem spgood_arc : SPGood Net.arc := by
  refine ⟨⟨(fun b : Bool => if b then (1:ℝ) else 0 : Net.arc.V → ℝ), rfl, rfl, ?_⟩, ?_, ?_⟩
  · intro a; show (if false = true then (1:ℝ) else 0) < (if true = true then (1:ℝ) else 0); norm_num
  · intro v
    cases v
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨(), rfl, rfl⟩
  · intro v
    cases v
    · exact Relation.ReflTransGen.single ⟨(), rfl, rfl⟩
    · exact Relation.ReflTransGen.refl

theorem spgood_series {G₁ G₂ : Net} (h₁ : SPGood G₁) (h₂ : SPGood G₂) :
    SPGood (G₁.series G₂) := by
  obtain ⟨⟨p₁, p₁s, p₁t, hp₁⟩, r₁s, r₁t⟩ := h₁
  obtain ⟨⟨p₂, p₂s, p₂t, hp₂⟩, r₂s, r₂t⟩ := h₂
  have hst₂ : G₂.t ≠ G₂.s := by intro h; have := hp₂; rw [h, p₂s] at p₂t; norm_num at p₂t
  -- the two embeddings are graph homomorphisms
  have R1 : ∀ {u v : G₁.V}, Reaches G₁ u v →
      Reaches (G₁.series G₂) (Sum.inl u) (Sum.inl v) := fun h =>
    reaches_map (G := G₁) (H := G₁.series G₂) Sum.inl Sum.inl (fun _ => rfl) (fun _ => rfl) h
  have R2 : ∀ {u v : G₂.V}, Reaches G₂ u v →
      Reaches (G₁.series G₂) (seriesEmb G₁ G₂ u) (seriesEmb G₁ G₂ v) := fun h =>
    reaches_map (G := G₂) (H := G₁.series G₂) (seriesEmb G₁ G₂) Sum.inr (fun _ => rfl)
      (fun _ => rfl) h
  have e_s : seriesEmb G₁ G₂ G₂.s = Sum.inl G₁.t := by simp [seriesEmb]
  refine ⟨⟨Sum.elim (fun v => p₁ v / 2) (fun v => (1 + p₂ v.1) / 2), ?_, ?_, ?_⟩, ?_, ?_⟩
  · show p₁ G₁.s / 2 = 0
    rw [p₁s]; norm_num
  · show Sum.elim (fun v => p₁ v / 2) (fun v => (1 + p₂ v.1) / 2) (seriesEmb G₁ G₂ G₂.t) = 1
    simp [seriesEmb, hst₂, p₂t]
  · have hemb : ∀ v, Sum.elim (fun v => p₁ v / 2) (fun (v : {v : G₂.V // v ≠ G₂.s}) =>
        (1 + p₂ v.1) / 2) (seriesEmb G₁ G₂ v) = (1 + p₂ v) / 2 := by
      intro v
      by_cases hv : v = G₂.s
      · subst hv; simp [seriesEmb, p₁t, p₂s]
      · simp [seriesEmb, hv]
    rintro (a | a)
    · show p₁ (G₁.tail a) / 2 < p₁ (G₁.head a) / 2
      linarith [hp₁ a]
    · show Sum.elim _ _ (seriesEmb G₁ G₂ (G₂.tail a)) < Sum.elim _ _ (seriesEmb G₁ G₂ (G₂.head a))
      rw [hemb, hemb]; linarith [hp₂ a]
  · rintro (v | ⟨v, hv⟩)
    · exact R1 (r₁s v)
    · have h2 := R2 (r₂s v)
      rw [e_s] at h2
      have : seriesEmb G₁ G₂ v = Sum.inr ⟨v, hv⟩ := by simp [seriesEmb, hv]
      rw [this] at h2
      exact (R1 (r₁s G₁.t)).trans h2
  · rintro (v | ⟨v, hv⟩)
    · have h2 := R2 (r₂s G₂.t)
      rw [e_s] at h2
      exact (R1 (r₁t v)).trans h2
    · have h2 := R2 (r₂t v)
      have : seriesEmb G₁ G₂ v = Sum.inr ⟨v, hv⟩ := by simp [seriesEmb, hv]
      rw [this] at h2
      exact h2

theorem spgood_par {G₁ G₂ : Net} (h₁ : SPGood G₁) (h₂ : SPGood G₂) :
    SPGood (G₁.par G₂) := by
  obtain ⟨⟨p₁, p₁s, p₁t, hp₁⟩, r₁s, r₁t⟩ := h₁
  obtain ⟨⟨p₂, p₂s, p₂t, hp₂⟩, r₂s, r₂t⟩ := h₂
  have R1 : ∀ {u v : G₁.V}, Reaches G₁ u v →
      Reaches (G₁.par G₂) (Sum.inl u) (Sum.inl v) := fun h =>
    reaches_map (G := G₁) (H := G₁.par G₂) Sum.inl Sum.inl (fun _ => rfl) (fun _ => rfl) h
  have R2 : ∀ {u v : G₂.V}, Reaches G₂ u v →
      Reaches (G₁.par G₂) (parEmb G₁ G₂ u) (parEmb G₁ G₂ v) := fun h =>
    reaches_map (G := G₂) (H := G₁.par G₂) (parEmb G₁ G₂) Sum.inr (fun _ => rfl)
      (fun _ => rfl) h
  have e_s : parEmb G₁ G₂ G₂.s = Sum.inl G₁.s := by simp [parEmb]
  have hst₂ : G₂.t ≠ G₂.s := by intro h; rw [h, p₂s] at p₂t; norm_num at p₂t
  have e_t : parEmb G₁ G₂ G₂.t = Sum.inl G₁.t := by simp [parEmb, hst₂]
  have hemb : ∀ v, Sum.elim p₁ (fun (v : {v : G₂.V // v ≠ G₂.s ∧ v ≠ G₂.t}) => p₂ v.1)
      (parEmb G₁ G₂ v) = p₂ v := by
    intro v
    by_cases hv : v = G₂.s
    · subst hv; simp [parEmb, p₁s, p₂s]
    · by_cases hv' : v = G₂.t
      · subst hv'; simp [parEmb, hv, p₁t, p₂t]
      · simp [parEmb, hv, hv']
  refine ⟨⟨Sum.elim p₁ (fun v => p₂ v.1), p₁s, p₁t, ?_⟩, ?_, ?_⟩
  · rintro (a | a)
    · exact hp₁ a
    · show Sum.elim _ _ (parEmb G₁ G₂ (G₂.tail a)) < Sum.elim _ _ (parEmb G₁ G₂ (G₂.head a))
      rw [hemb, hemb]; exact hp₂ a
  · rintro (v | ⟨v, hv, hv'⟩)
    · exact R1 (r₁s v)
    · have h2 := R2 (r₂s v)
      rw [e_s] at h2
      have : parEmb G₁ G₂ v = Sum.inr ⟨v, hv, hv'⟩ := by simp [parEmb, hv, hv']
      rw [this] at h2
      exact h2
  · rintro (v | ⟨v, hv, hv'⟩)
    · exact R1 (r₁t v)
    · have h2 := R2 (r₂t v)
      rw [e_t] at h2
      have : parEmb G₁ G₂ v = Sum.inr ⟨v, hv, hv'⟩ := by simp [parEmb, hv, hv']
      rw [this] at h2
      exact h2

theorem spgood_toNet : ∀ T : SPTerm, SPGood T.toNet
  | .arc => spgood_arc
  | .series T₁ T₂ => spgood_series (spgood_toNet T₁) (spgood_toNet T₂)
  | .par T₁ T₂ => spgood_par (spgood_toNet T₁) (spgood_toNet T₂)

theorem SPGood.acyclic {G : Net} (h : SPGood G) : IsAcyclic G := by
  obtain ⟨⟨p, -, -, hp⟩, -, -⟩ := h
  have key : ∀ u v, Relation.TransGen (Adj G) u v → p u < p v := by
    intro u v huv
    induction huv with
    | single hab => obtain ⟨a, rfl, rfl⟩ := hab; exact hp a
    | tail _ hab ih => obtain ⟨a, ha, rfl⟩ := hab; subst ha; exact ih.trans (hp a)
  intro v hv
  exact lt_irrefl _ (key v v hv)

theorem SPGood.st {G : Net} (h : SPGood G) : G.s ≠ G.t := by
  obtain ⟨⟨p, hs, ht, -⟩, -, -⟩ := h
  intro e; rw [e, ht] at hs; norm_num at hs

theorem SPGood.spg {G : Net} (h : SPGood G) : IsShortestPathGraph G :=
  ⟨h.acyclic, h.2.1⟩

theorem SPGood.twoTerminal {G : Net} (h : SPGood G) : IsTwoTerminalDAG G := by
  have hac := h.acyclic
  obtain ⟨-, rs, rt⟩ := h
  refine ⟨hac, ?_, ?_⟩
  · intro v
    constructor
    · intro hv
      by_contra hne
      rcases Relation.ReflTransGen.cases_tail (rs v) with e | ⟨c, -, ⟨a, -, ha⟩⟩
      · exact hne e
      · exact hv a ha
    · rintro rfl a ha
      -- cycle s →* tail a → s
      apply hac G.s
      exact Relation.TransGen.tail' (rs (G.tail a)) ⟨a, rfl, ha⟩
  · intro v
    constructor
    · intro hv
      by_contra hne
      rcases Relation.ReflTransGen.cases_head (rt v) with e | ⟨c, ⟨a, ha, -⟩, -⟩
      · exact hne e
      · exact hv a ha
    · rintro rfl a ha
      apply hac G.t
      exact Relation.TransGen.head' ⟨a, ha, rfl⟩ (rt (G.head a))


theorem card_series_V (G₁ G₂ : Net) :
    Fintype.card (G₁.series G₂).V + 1 = Fintype.card G₁.V + Fintype.card G₂.V := by
  show Fintype.card (G₁.V ⊕ {v : G₂.V // v ≠ G₂.s}) + 1 = _
  rw [Fintype.card_sum, Fintype.card_subtype, Finset.filter_ne' , Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have : 0 < Fintype.card G₂.V := Fintype.card_pos_iff.mpr ⟨G₂.s⟩
  omega

theorem card_par_V (G₁ G₂ : Net) (h : G₂.s ≠ G₂.t) :
    Fintype.card (G₁.par G₂).V + 2 = Fintype.card G₁.V + Fintype.card G₂.V := by
  show Fintype.card (G₁.V ⊕ {v : G₂.V // v ≠ G₂.s ∧ v ≠ G₂.t}) + 2 = _
  rw [Fintype.card_sum, Fintype.card_subtype]
  have e : (Finset.univ.filter fun v : G₂.V => v ≠ G₂.s ∧ v ≠ G₂.t) = (Finset.univ.erase G₂.s).erase G₂.t := by
    ext v; simp [and_comm]
  rw [e, Finset.card_erase_of_mem (by simp [Ne.symm h]), Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have : 1 < Fintype.card G₂.V := Fintype.one_lt_card_iff.mpr ⟨G₂.s, G₂.t, h⟩
  omega

theorem card_series_A (G₁ G₂ : Net) :
    Fintype.card (G₁.series G₂).A = Fintype.card G₁.A + Fintype.card G₂.A := by
  show Fintype.card (G₁.A ⊕ G₂.A) = _
  rw [Fintype.card_sum]

theorem card_par_A (G₁ G₂ : Net) :
    Fintype.card (G₁.par G₂).A = Fintype.card G₁.A + Fintype.card G₂.A := by
  show Fintype.card (G₁.A ⊕ G₂.A) = _
  rw [Fintype.card_sum]


theorem breakpoints_congr {ι : Type} (f g : ℝ → ι → ℝ) (h : ∀ y, 0 < y → f y = g y) :
    breakpoints f = breakpoints g := by
  have key : ∀ f g : ℝ → ι → ℝ, (∀ y, 0 < y → f y = g y) →
      breakpoints f ⊆ breakpoints g := by
    intro f g h x ⟨hx, hnot⟩
    refine ⟨hx, ?_⟩
    rintro ⟨ε, hε, m, c, hmc⟩
    apply hnot
    refine ⟨min ε x, lt_min hε hx, m, c, ?_⟩
    intro y hy i
    have hy0 : 0 < y := by
      have := hy.1; have := min_le_right ε x; linarith
    have hy' : y ∈ Set.Ioo (x - ε) (x + ε) := by
      constructor
      · have := hy.1; have := min_le_left ε x; linarith
      · have := hy.2; have := min_le_left ε x; linarith
    rw [h y hy0]
    exact hmc y hy' i
  exact Set.Subset.antisymm (key f g h) (key g f fun y hy => (h y hy).symm)

/-- the unique arc of the arc network -/
def arcArc : Net.arc.A := ()

theorem arcArc_eq (b : Net.arc.A) : b = arcArc := rfl

theorem arc_label (Astar : Finset Net.arc.A) (ν : Net.arc.A → ℝ) (ρ : ℝ → Net.arc.V → ℝ)
    (hρ : IsLabelFunction Net.arc Astar ν ρ) (y : ℝ) (hy : 0 ≤ y) :
    ρ y false = 1 ∧ ρ y true = rhoArc Astar ν arcArc 1 y := by
  obtain ⟨hs, x, hx, hl⟩ := hρ y hy
  have hs' : ρ y false = 1 := hs
  have hxv : x arcArc = y := by
    have := hx.2.2
    have e1 : outflow Net.arc x Net.arc.s = x arcArc := by
      unfold outflow
      exact Finset.sum_eq_single_of_mem arcArc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
        (fun b _ hb => (hb (arcArc_eq b)).elim)
    have e2 : inflow Net.arc x Net.arc.s = 0 := by
      unfold inflow
      apply Finset.sum_eq_zero
      intro b hb
      have h := (Finset.mem_filter.mp hb).2
      exact Bool.noConfusion h
    rw [e1, e2, sub_zero] at this; exact this
  refine ⟨hs', ?_⟩
  obtain ⟨⟨a, -, ha⟩, -⟩ := hl.2.1 true (by simp [Net.arc])
  rw [arcArc_eq a] at ha
  rw [ha]
  have : Net.arc.tail arcArc = false := rfl
  rw [this, hs', hxv]

theorem arc_not_bp (ρ : ℝ → Net.arc.V → ℝ) (x ε a b : ℝ) (hε : 0 < ε)
    (h : ∀ y ∈ Set.Ioo (x - ε) (x + ε), ρ y false = 1 ∧ ρ y true = a * y + b) :
    x ∉ breakpoints ρ := by
  rintro ⟨-, hnot⟩
  apply hnot
  refine ⟨ε, hε, fun i : Bool => if i then a else 0, fun i : Bool => if i then b else 1, ?_⟩
  intro y hy i
  cases i
  · simp [(h y hy).1]
  · simp [(h y hy).2]

theorem arc_bound (Astar : Finset Net.arc.A) (ν : Net.arc.A → ℝ) (hν : ∀ a, 0 < ν a)
    (ρ : ℝ → Net.arc.V → ℝ) (hρ : IsLabelFunction Net.arc Astar ν ρ) :
    (breakpoints ρ).ncard + Astar.card + Fintype.card Net.arc.V ≤
      2 * Fintype.card Net.arc.A + 1 := by
  have cV : Fintype.card Net.arc.V = 2 := by
    show Fintype.card Bool = 2; rfl
  have cA : Fintype.card Net.arc.A = 1 := by
    show Fintype.card Unit = 1; rfl
  have hν0 := hν arcArc
  by_cases hA : arcArc ∈ Astar
  · have hAc : Astar.card = 1 := by
      rw [Finset.card_eq_one]; exact ⟨arcArc, by ext u; rw [arcArc_eq u]; simp [hA]⟩
    have : breakpoints ρ = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      have hx0 := hx.1
      refine arc_not_bp ρ x x (1 / ν arcArc) 0 hx0 (fun y hy => ?_) hx
      have hy0 : 0 ≤ y := by have := hy.1; linarith
      obtain ⟨h1, h2⟩ := arc_label Astar ν ρ hρ y hy0
      refine ⟨h1, ?_⟩
      rw [h2]; unfold rhoArc; rw [if_pos hA]; ring
    rw [this, Set.ncard_empty, hAc, cV, cA]
  · have hAc : Astar.card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro u; rw [arcArc_eq u]; exact hA
    have hsub : breakpoints ρ ⊆ {ν arcArc} := by
      intro x hx
      by_contra hne
      have hne : x ≠ ν arcArc := hne
      have hx0 := hx.1
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · refine arc_not_bp ρ x (min x (ν arcArc - x)) 0 1 (lt_min hx0 (by linarith)) (fun y hy => ?_) hx
        have h1 := min_le_left x (ν arcArc - x); have h2 := min_le_right x (ν arcArc - x)
        have hy0 : 0 ≤ y := by have := hy.1; linarith
        have hyν : y ≤ ν arcArc := by have := hy.2; linarith
        obtain ⟨e1, e2⟩ := arc_label Astar ν ρ hρ y hy0
        refine ⟨e1, ?_⟩
        rw [e2]; unfold rhoArc; rw [if_neg hA]
        have : y / ν arcArc ≤ 1 := by rw [div_le_one hν0]; exact hyν
        rw [max_eq_left this]; ring
      · refine arc_not_bp ρ x (x - ν arcArc) (1 / ν arcArc) 0 (by linarith) (fun y hy => ?_) hx
        have hyν : ν arcArc ≤ y := by have := hy.1; linarith
        have hy0 : 0 ≤ y := by linarith
        obtain ⟨e1, e2⟩ := arc_label Astar ν ρ hρ y hy0
        refine ⟨e1, ?_⟩
        rw [e2]; unfold rhoArc; rw [if_neg hA]
        have : 1 ≤ y / ν arcArc := by rw [le_div_iff₀ hν0]; linarith
        rw [max_eq_right this]; ring
    have : (breakpoints ρ).ncard ≤ 1 := by
      calc (breakpoints ρ).ncard ≤ ({ν arcArc} : Set ℝ).ncard :=
            Set.ncard_le_ncard hsub (Set.finite_singleton _)
        _ = 1 := Set.ncard_singleton _
    rw [hAc, cV, cA]; omega


/-- Existence (Proposition 17) and uniqueness on `[0,∞)` (Corollary 15). -/
theorem prop17_unique (G : Net) (hG : SPGood G) (Astar : Finset G.A) (ν : G.A → ℝ)
    (hν : ∀ a, 0 < ν a) :
    ∃ ρ₀ : ℝ → G.V → ℝ, IsLabelFunction G Astar ν ρ₀ ∧ ContinuousOn ρ₀ (Set.Ici 0) ∧
      (breakpoints ρ₀).Finite ∧
      ∀ ρ : ℝ → G.V → ℝ, IsLabelFunction G Astar ν ρ → ∀ y, 0 ≤ y → ρ y = ρ₀ y := by
  obtain ⟨ρ₀, χ, hc, hf, -, -, hpar⟩ :=
    proposition_17 G Astar ν hG.spg hG.st hν
  refine ⟨ρ₀, fun y hy => ⟨(hpar y hy).2.2, χ y, (hpar y hy).1, (hpar y hy).2.1⟩, hc, hf, ?_⟩
  intro ρ hρ y hy
  obtain ⟨hs, x, hx, hl⟩ := hρ y hy
  exact corollary_15 G Astar ν hG.spg hG.st hν x (χ y) (ρ y) (ρ₀ y) y hx (hpar y hy).1 hl
    (hpar y hy).2.1 (by rw [hs, (hpar y hy).2.2])

theorem exists_label (G : Net) (hG : SPGood G) (Astar : Finset G.A) (ν : G.A → ℝ)
    (hν : ∀ a, 0 < ν a) : ∃ ρ : ℝ → G.V → ℝ, IsLabelFunction G Astar ν ρ := by
  obtain ⟨ρ₀, h, -⟩ := prop17_unique G hG Astar ν hν
  exact ⟨ρ₀, h⟩

theorem label_regular (G : Net) (hG : SPGood G) (Astar : Finset G.A) (ν : G.A → ℝ)
    (hν : ∀ a, 0 < ν a) (ρ : ℝ → G.V → ℝ) (hρ : IsLabelFunction G Astar ν ρ) :
    ContinuousOn ρ (Set.Ici 0) ∧ (breakpoints ρ).Finite := by
  obtain ⟨ρ₀, -, hc, hf, hu⟩ := prop17_unique G hG Astar ν hν
  refine ⟨hc.congr (fun y hy => hu ρ hρ y hy), ?_⟩
  rw [breakpoints_congr ρ ρ₀ (fun y hy => hu ρ hρ y hy.le)]
  exact hf

def SPBound (G : Net) : Prop :=
  ∀ (Astar : Finset G.A) (ν : G.A → ℝ), (∀ a, 0 < ν a) →
    ∀ ρ : ℝ → G.V → ℝ, IsLabelFunction G Astar ν ρ →
      (breakpoints ρ).ncard + Astar.card + Fintype.card G.V ≤ 2 * Fintype.card G.A + 1

theorem series_step (G₁ G₂ : Net) (g₁ : SPGood G₁) (g₂ : SPGood G₂)
    (b₁ : SPBound G₁) (b₂ : SPBound G₂) : SPBound (G₁.series G₂) := by
  intro Astar ν hν ρ hρ
  have g := spgood_series g₁ g₂
  obtain ⟨ρ₁, hρ₁⟩ := exists_label G₁ g₁ Astar.toLeft (fun a => ν (Sum.inl a)) (fun a => hν _)
  obtain ⟨ρ₂, hρ₂⟩ := exists_label G₂ g₂ Astar.toRight (fun a => ν (Sum.inr a)) (fun a => hν _)
  have h29 := lemma_29 G₁ G₂ g₁.twoTerminal g₂.twoTerminal Astar ν hν ρ ρ₁ ρ₂ hρ hρ₁ hρ₂
  have f := (label_regular _ g Astar ν hν ρ hρ).2
  have f₁ := (label_regular _ g₁ _ _ (fun a => hν _) ρ₁ hρ₁).2
  have f₂ := (label_regular _ g₂ _ _ (fun a => hν _) ρ₂ hρ₂).2
  rw [← f.cast_ncard_eq, ← f₁.cast_ncard_eq, ← f₂.cast_ncard_eq] at h29
  norm_cast at h29
  have i₁ := b₁ Astar.toLeft _ (fun a => hν _) ρ₁ hρ₁
  have i₂ := b₂ Astar.toRight _ (fun a => hν _) ρ₂ hρ₂
  have cS : Astar.toLeft.card + Astar.toRight.card = @Finset.card (G₁.series G₂).A Astar :=
    Finset.card_toLeft_add_card_toRight
  have cV := card_series_V G₁ G₂
  have cA := card_series_A G₁ G₂
  omega

theorem par_step (G₁ G₂ : Net) (g₁ : SPGood G₁) (g₂ : SPGood G₂)
    (b₁ : SPBound G₁) (b₂ : SPBound G₂) : SPBound (G₁.par G₂) := by
  intro Astar ν hν ρ hρ
  have g := spgood_par g₁ g₂
  obtain ⟨ρ₁, hρ₁⟩ := exists_label G₁ g₁ Astar.toLeft (fun a => ν (Sum.inl a)) (fun a => hν _)
  obtain ⟨ρ₂, hρ₂⟩ := exists_label G₂ g₂ Astar.toRight (fun a => ν (Sum.inr a)) (fun a => hν _)
  have h30 := lemma_30 G₁ G₂ g₁.twoTerminal g₂.twoTerminal Astar ν hν ρ ρ₁ ρ₂ hρ hρ₁ hρ₂
  have f := (label_regular _ g Astar ν hν ρ hρ).2
  have f₁ := (label_regular _ g₁ _ _ (fun a => hν _) ρ₁ hρ₁).2
  have f₂ := (label_regular _ g₂ _ _ (fun a => hν _) ρ₂ hρ₂).2
  rw [← f.cast_ncard_eq, ← f₁.cast_ncard_eq, ← f₂.cast_ncard_eq] at h30
  norm_cast at h30
  have i₁ := b₁ Astar.toLeft _ (fun a => hν _) ρ₁ hρ₁
  have i₂ := b₂ Astar.toRight _ (fun a => hν _) ρ₂ hρ₂
  have cS : Astar.toLeft.card + Astar.toRight.card = @Finset.card (G₁.par G₂).A Astar :=
    Finset.card_toLeft_add_card_toRight
  have cV := card_par_V G₁ G₂ g₂.st
  have cA := card_par_A G₁ G₂
  omega

theorem sp_bound : ∀ T : SPTerm, SPBound T.toNet
  | .arc => fun Astar ν hν ρ hρ => arc_bound Astar ν hν ρ hρ
  | .series T₁ T₂ => series_step _ _ (spgood_toNet T₁) (spgood_toNet T₂) (sp_bound T₁) (sp_bound T₂)
  | .par T₁ T₂ => par_step _ _ (spgood_toNet T₁) (spgood_toNet T₂) (sp_bound T₁) (sp_bound T₂)

end ThinFlowSP.Breakpoints

open ThinFlowSP.Breakpoints in
theorem solution (T : SPTerm) (Astar : Finset T.toNet.A) (ν : T.toNet.A → ℝ)
    (hν : ∀ a, 0 < ν a) :
    (∃ ρ : ℝ → T.toNet.V → ℝ, IsLabelFunction T.toNet Astar ν ρ) ∧
    ∀ ρ : ℝ → T.toNet.V → ℝ, IsLabelFunction T.toNet Astar ν ρ →
      ContinuousOn ρ (Set.Ici 0) ∧ (breakpoints ρ).Finite ∧
      ((breakpoints ρ).ncard : ℤ) ≤
        2 * (Fintype.card T.toNet.A : ℤ) - (Astar.card : ℤ) - (Fintype.card T.toNet.V : ℤ) + 1 := by
  have g := spgood_toNet T
  refine ⟨exists_label _ g Astar ν hν, fun ρ hρ => ?_⟩
  obtain ⟨hc, hf⟩ := label_regular _ g Astar ν hν ρ hρ
  refine ⟨hc, hf, ?_⟩
  have := sp_bound T Astar ν hν ρ hρ
  omega
