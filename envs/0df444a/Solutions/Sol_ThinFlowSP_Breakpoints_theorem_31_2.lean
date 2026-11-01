-- Prove2me | solution 2 for ThinFlowSP.Breakpoints.theorem_31
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T08:58:02.365806+00:00
-- url     : https://prove2.me/submissions/f2e2a90a-1f9d-48c6-a080-5711d72dc83c

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Model
import Theorems.Thm_ThinFlowSP_Breakpoints_corollary_15
import Theorems.Thm_ThinFlowSP_Breakpoints_lemma_18
import Theorems.Thm_ThinFlowSP_Breakpoints_lemma_29
import Theorems.Thm_ThinFlowSP_Breakpoints_lemma_30


namespace ThinFlowSP.Breakpoints

set_option allowUnsafeReducibility true in
attribute [local reducible] Net.series Net.par

/-! ### General facts -/

theorem div_le_rhoArc {G : Net} (Astar : Finset G.A) (ν : G.A → ℝ) (a : G.A) (lv xa : ℝ) :
    xa / ν a ≤ rhoArc Astar ν a lv xa := by
  unfold rhoArc; split_ifs
  · exact le_rfl
  · exact le_max_right _ _

theorem sum_net' (G : Net) (y : G.A → ℝ) (U : Finset G.V) :
    ∑ u ∈ U, (outflow G y u - inflow G y u) =
      ∑ a, ((if G.tail a ∈ U then y a else 0) - (if G.head a ∈ U then y a else 0)) := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  congr 1
  · unfold outflow
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_ite_eq]
  · unfold inflow
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_ite_eq]

theorem net_t' (G : Net) (hst : G.s ≠ G.t) (y : G.A → ℝ) (val : ℝ) (hy : IsStaticFlow G y val) :
    outflow G y G.t - inflow G y G.t = -val := by
  have h := sum_net' G y Finset.univ
  simp only [Finset.mem_univ, if_true, sub_self, Finset.sum_const_zero] at h
  rw [Fintype.sum_eq_add G.s G.t hst (fun v hv => hy.2.1 v hv.1 hv.2), hy.2.2] at h
  linarith

theorem rhoArc_smul' {G : Net} (Astar : Finset G.A) (ν : G.A → ℝ) (a : G.A) {c : ℝ} (hc : 0 ≤ c)
    (lv xa : ℝ) : rhoArc Astar ν a (c * lv) (c * xa) = c * rhoArc Astar ν a lv xa := by
  unfold rhoArc
  split_ifs
  · ring
  · rw [mul_max_of_nonneg _ _ hc, mul_div_assoc]

theorem staticFlow_smul' {G : Net} {x : G.A → ℝ} {val c : ℝ} (hc : 0 ≤ c)
    (hx : IsStaticFlow G x val) : IsStaticFlow G (c • x) (c * val) := by
  have hout : ∀ v, outflow G (c • x) v = c * outflow G x v := by
    intro v; unfold outflow; rw [Finset.mul_sum]; rfl
  have hin : ∀ v, inflow G (c • x) v = c * inflow G x v := by
    intro v; unfold inflow; rw [Finset.mul_sum]; rfl
  refine ⟨fun a => ?_, fun v h1 h2 => ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hc (hx.1 a)
  · rw [hout, hin, ← mul_sub, hx.2.1 v h1 h2, mul_zero]
  · rw [hout, hin, ← mul_sub, hx.2.2]

theorem labels_smul' {G : Net} {Astar : Finset G.A} {ν : G.A → ℝ} {x : G.A → ℝ} {l : G.V → ℝ}
    {c : ℝ} (hc : 0 < c) (hl : IsThinFlowLabels G Astar ν x l) :
    IsThinFlowLabels G Astar ν (c • x) (c • l) := by
  simp only [IsThinFlowLabels, Pi.smul_apply, smul_eq_mul]
  refine ⟨fun v => mul_nonneg hc.le (hl.1 v), fun w hw => ?_, fun a ha => ?_⟩
  · obtain ⟨⟨a, ha, e⟩, hlb⟩ := hl.2.1 w hw
    refine ⟨⟨a, ha, ?_⟩, ?_⟩
    · rw [rhoArc_smul' Astar ν a hc.le, e]
    · rintro r ⟨b, hb, rfl⟩
      rw [rhoArc_smul' Astar ν b hc.le]
      exact mul_le_mul_of_nonneg_left (hlb ⟨b, hb, rfl⟩) hc.le
  · have ha' : 0 < x a := by
      by_contra h; push Not at h; nlinarith
    rw [rhoArc_smul' Astar ν a hc.le, hl.2.2 a ha']

/-- In a two-terminal DAG every vertex is reachable from `s`. -/
theorem tt_reach {G : Net} (h : IsTwoTerminalDAG G) : ∀ v, Reaches G G.s v := by
  have : IsTrans G.V (Relation.TransGen (Adj G)) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  have : Std.Irrefl (Relation.TransGen (Adj G)) := ⟨h.1⟩
  have wf := Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen (Adj G))
  intro v
  induction v using wf.induction with
  | _ v ih =>
    by_cases hv : v = G.s
    · rw [hv]; exact Relation.ReflTransGen.refl
    · have : ¬ ∀ a, G.head a ≠ v := fun h' => hv ((h.2.1 v).mp h')
      push Not at this
      obtain ⟨a, ha⟩ := this
      have hadj : Adj G (G.tail a) v := ⟨a, rfl, ha⟩
      exact (ih (G.tail a) (Relation.TransGen.single hadj)).tail hadj

theorem tt_spg {G : Net} (h : IsTwoTerminalDAG G) : IsShortestPathGraph G := ⟨h.1, tt_reach h⟩

theorem tt_head_ne_s {G : Net} (h : IsTwoTerminalDAG G) (a : G.A) : G.head a ≠ G.s :=
  ((h.2.1 G.s).mpr rfl) a

theorem tt_tail_ne_t {G : Net} (h : IsTwoTerminalDAG G) (a : G.A) : G.tail a ≠ G.t :=
  ((h.2.2 G.t).mpr rfl) a

theorem st_of_label {G : Net} (h : IsTwoTerminalDAG G) {Astar : Finset G.A} {ν : G.A → ℝ}
    {ρ : ℝ → G.V → ℝ} (hρ : IsLabelFunction G Astar ν ρ) : G.s ≠ G.t := by
  intro hst
  obtain ⟨-, x, hx, -⟩ := hρ 1 zero_le_one
  have h1 : outflow G x G.s = 0 := by
    unfold outflow
    apply Finset.sum_eq_zero
    intro a ha
    exact absurd ((Finset.mem_filter.mp ha).2.trans hst) (tt_tail_ne_t h a)
  have h2 : inflow G x G.s = 0 := by
    unfold inflow
    apply Finset.sum_eq_zero
    intro a ha
    exact absurd (Finset.mem_filter.mp ha).2 (tt_head_ne_s h a)
  have := hx.2.2
  rw [h1, h2] at this
  norm_num at this

/-- The label at `t` of a thin flow of positive value is positive. -/
theorem label_t_pos {G : Net} (hst : G.s ≠ G.t) {Astar : Finset G.A} {ν : G.A → ℝ}
    (hν : ∀ a, 0 < ν a) {x : G.A → ℝ} {l : G.V → ℝ} {y : ℝ} (hy : 0 < y)
    (hx : IsStaticFlow G x y) (hl : IsThinFlowLabels G Astar ν x l) : 0 < l G.t := by
  have hnet := net_t' G hst x y hx
  have hout : 0 ≤ outflow G x G.t := Finset.sum_nonneg fun a _ => hx.1 a
  have hin : 0 < inflow G x G.t := by linarith
  unfold inflow at hin
  obtain ⟨a, ha, hxa⟩ := Finset.exists_lt_of_sum_lt (f := fun _ => (0:ℝ)) (g := x)
    (by rw [Finset.sum_const_zero]; exact hin)
  have hha := (Finset.mem_filter.mp ha).2
  rw [← hha, hl.2.2 a hxa]
  exact lt_of_lt_of_le (div_pos hxa (hν a)) (div_le_rhoArc _ _ _ _ _)

/-! ### Series composition -/

section Series

variable (G₁ G₂ : Net)

theorem sum_series_A (f : (G₁.series G₂).A → ℝ) :
    ∑ a, f a = ∑ a : G₁.A, f (Sum.inl a) + ∑ a : G₂.A, f (Sum.inr a) :=
  Fintype.sum_sum_type f

theorem seriesEmb_eq_inl (w : G₂.V) (v : G₁.V) :
    seriesEmb G₁ G₂ w = Sum.inl v ↔ w = G₂.s ∧ G₁.t = v := by
  unfold seriesEmb
  split_ifs with h
  · simp [h]
  · simp [h]

theorem seriesEmb_eq_inr (w : G₂.V) (v : {v : G₂.V // v ≠ G₂.s}) :
    seriesEmb G₁ G₂ w = Sum.inr v ↔ w = v.1 := by
  unfold seriesEmb
  split_ifs with h
  · simp only [false_iff]; intro e; exact v.2 (e ▸ h)
  · constructor
    · intro e; cases e; rfl
    · intro e; subst e; rfl

theorem series_outflow_inl (x : G₁.A ⊕ G₂.A → ℝ) (v : G₁.V) :
    outflow (G₁.series G₂) x (Sum.inl v) = outflow G₁ (fun a => x (Sum.inl a)) v +
      ∑ a : G₂.A, if G₂.tail a = G₂.s ∧ G₁.t = v then x (Sum.inr a) else 0 := by
  unfold outflow
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [sum_series_A]
  congr 1
  · apply Finset.sum_congr rfl; intro a _
    simp [Net.series]
  · apply Finset.sum_congr rfl; intro a _
    simp only [Net.series, Sum.elim_inr, seriesEmb_eq_inl]

theorem series_inflow_inl (x : G₁.A ⊕ G₂.A → ℝ) (v : G₁.V) :
    inflow (G₁.series G₂) x (Sum.inl v) = inflow G₁ (fun a => x (Sum.inl a)) v +
      ∑ a : G₂.A, if G₂.head a = G₂.s ∧ G₁.t = v then x (Sum.inr a) else 0 := by
  unfold inflow
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [sum_series_A]
  congr 1
  · apply Finset.sum_congr rfl; intro a _
    simp [Net.series]
  · apply Finset.sum_congr rfl; intro a _
    simp only [Net.series, Sum.elim_inr, seriesEmb_eq_inl]

theorem series_outflow_inr (x : G₁.A ⊕ G₂.A → ℝ) (v : {v : G₂.V // v ≠ G₂.s}) :
    outflow (G₁.series G₂) x (Sum.inr v) = outflow G₂ (fun a => x (Sum.inr a)) v.1 := by
  unfold outflow
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [sum_series_A]
  rw [Finset.sum_eq_zero (fun a _ => by simp [Net.series]), zero_add]
  apply Finset.sum_congr rfl; intro a _
  simp only [Net.series, Sum.elim_inr, seriesEmb_eq_inr]

theorem series_inflow_inr (x : G₁.A ⊕ G₂.A → ℝ) (v : {v : G₂.V // v ≠ G₂.s}) :
    inflow (G₁.series G₂) x (Sum.inr v) = inflow G₂ (fun a => x (Sum.inr a)) v.1 := by
  unfold inflow
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [sum_series_A]
  rw [Finset.sum_eq_zero (fun a _ => by simp [Net.series]), zero_add]
  apply Finset.sum_congr rfl; intro a _
  simp only [Net.series, Sum.elim_inr, seriesEmb_eq_inr]

end Series

end ThinFlowSP.Breakpoints


namespace ThinFlowSP.Breakpoints

set_option allowUnsafeReducibility true in
attribute [local reducible] Net.series Net.par

section Series2

variable {G₁ G₂ : Net}

theorem series_s : (G₁.series G₂).s = Sum.inl G₁.s := rfl

theorem series_t (hst₂ : G₂.s ≠ G₂.t) :
    (G₁.series G₂).t = Sum.inr ⟨G₂.t, hst₂.symm⟩ := by
  show seriesEmb G₁ G₂ G₂.t = _
  exact (seriesEmb_eq_inr G₁ G₂ _ _).mpr rfl

theorem rhoArc_toLeft (Astar : Finset (G₁.A ⊕ G₂.A)) (ν : G₁.A ⊕ G₂.A → ℝ) (a : G₁.A)
    (lv xa : ℝ) :
    rhoArc (G := G₁) (Finset.toLeft Astar) (fun a => ν (Sum.inl a)) a lv xa =
      rhoArc (G := G₁.series G₂) Astar ν (Sum.inl a) lv xa := by
  show (if a ∈ Astar.toLeft then xa / ν (Sum.inl a) else max lv (xa / ν (Sum.inl a))) =
    (if (Sum.inl a : G₁.A ⊕ G₂.A) ∈ Astar then xa / ν (Sum.inl a)
      else max lv (xa / ν (Sum.inl a)))
  simp only [Finset.mem_toLeft]

theorem rhoArc_toRight (Astar : Finset (G₁.A ⊕ G₂.A)) (ν : G₁.A ⊕ G₂.A → ℝ) (a : G₂.A)
    (lv xa : ℝ) :
    rhoArc (G := G₂) (Finset.toRight Astar) (fun a => ν (Sum.inr a)) a lv xa =
      rhoArc (G := G₁.series G₂) Astar ν (Sum.inr a) lv xa := by
  show (if a ∈ Astar.toRight then xa / ν (Sum.inr a) else max lv (xa / ν (Sum.inr a))) =
    (if (Sum.inr a : G₁.A ⊕ G₂.A) ∈ Astar then xa / ν (Sum.inr a)
      else max lv (xa / ν (Sum.inr a)))
  simp only [Finset.mem_toRight]

theorem series_restrict₁ (tt₂ : IsTwoTerminalDAG G₂)
    (hst₁ : G₁.s ≠ G₁.t) (hst₂ : G₂.s ≠ G₂.t) {Astar : Finset (G₁.A ⊕ G₂.A)}
    {ν : G₁.A ⊕ G₂.A → ℝ} {x : G₁.A ⊕ G₂.A → ℝ} {l : (G₁.series G₂).V → ℝ} {y : ℝ}
    (hx : IsStaticFlow (G₁.series G₂) x y) (hl : IsThinFlowLabels (G₁.series G₂) Astar ν x l) :
    IsStaticFlow G₁ (fun a => x (Sum.inl a)) y ∧
    IsThinFlowLabels G₁ (Finset.toLeft Astar) (fun a => ν (Sum.inl a)) (fun a => x (Sum.inl a))
      (fun v => l (Sum.inl v)) := by
  refine ⟨⟨fun a => hx.1 _, fun v hvs hvt => ?_, ?_⟩, fun v => hl.1 _, fun w hw => ?_, fun a ha => ?_⟩
  · have h := hx.2.1 (Sum.inl v) (by rw [series_s]; exact fun e => hvs (Sum.inl.inj e))
      (by rw [series_t hst₂]; exact Sum.inl_ne_inr)
    rw [series_outflow_inl, series_inflow_inl] at h
    have : G₁.t ≠ v := Ne.symm hvt
    simpa [this] using h
  · have h := hx.2.2
    rw [series_s, series_outflow_inl, series_inflow_inl] at h
    have : G₁.t ≠ G₁.s := Ne.symm hst₁
    simpa [this] using h
  · have h := hl.2.1 (Sum.inl w) (by rw [series_s]; exact fun e => hw (Sum.inl.inj e))
    convert h using 1
    ext r
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨Sum.inl a, by rw [← ha]; rfl, (rhoArc_toLeft Astar ν a _ _)⟩
    · rintro ⟨a, ha, rfl⟩
      rcases a with a | a
      · refine ⟨a, Sum.inl.inj ha, (rhoArc_toLeft Astar ν a _ _).symm⟩
      · exfalso
        have := ((seriesEmb_eq_inl G₁ G₂ _ _).mp ha).1
        exact tt_head_ne_s tt₂ a this
  · have := hl.2.2 (Sum.inl a) ha
    simp only at this ⊢
    rw [rhoArc_toLeft]
    exact this

theorem series_restrict₂ (tt₁ : IsTwoTerminalDAG G₁) (tt₂ : IsTwoTerminalDAG G₂)
    (hst₁ : G₁.s ≠ G₁.t) (hst₂ : G₂.s ≠ G₂.t) {Astar : Finset (G₁.A ⊕ G₂.A)}
    {ν : G₁.A ⊕ G₂.A → ℝ} {x : G₁.A ⊕ G₂.A → ℝ} {l : (G₁.series G₂).V → ℝ} {y : ℝ}
    (hx : IsStaticFlow (G₁.series G₂) x y) (hl : IsThinFlowLabels (G₁.series G₂) Astar ν x l) :
    IsStaticFlow G₂ (fun a => x (Sum.inr a)) y ∧
    IsThinFlowLabels G₂ (Finset.toRight Astar) (fun a => ν (Sum.inr a)) (fun a => x (Sum.inr a))
      (fun v => l (seriesEmb G₁ G₂ v)) := by
  have hemb : ∀ v (hv : v ≠ G₂.s), seriesEmb G₁ G₂ v = Sum.inr ⟨v, hv⟩ :=
    fun v hv => (seriesEmb_eq_inr G₁ G₂ _ _).mpr rfl
  refine ⟨⟨fun a => hx.1 _, fun v hvs hvt => ?_, ?_⟩, fun v => hl.1 _, fun w hw => ?_, fun a ha => ?_⟩
  · have h := hx.2.1 (Sum.inr ⟨v, hvs⟩) (by rw [series_s]; exact Sum.inr_ne_inl)
      (by rw [series_t hst₂]; intro e; exact hvt (congrArg Subtype.val (Sum.inr.inj e)))
    rw [series_outflow_inr, series_inflow_inr] at h
    exact h
  · -- flow through the junction `t₁ = s₂`
    have h := hx.2.1 (Sum.inl G₁.t) (by rw [series_s]; exact fun e => hst₁ (Sum.inl.inj e).symm)
      (by rw [series_t hst₂]; exact Sum.inl_ne_inr)
    rw [series_outflow_inl, series_inflow_inl] at h
    have r1 := (series_restrict₁ tt₂ hst₁ hst₂ hx hl).1
    have hnet := net_t' G₁ hst₁ _ y r1
    have ho1 : outflow G₁ (fun a => x (Sum.inl a)) G₁.t = 0 := by
      unfold outflow
      apply Finset.sum_eq_zero
      intro a ha
      exact absurd (Finset.mem_filter.mp ha).2 (tt_tail_ne_t tt₁ a)
    have hi2 : inflow G₂ (fun a => x (Sum.inr a)) G₂.s = 0 := by
      unfold inflow
      apply Finset.sum_eq_zero
      intro a ha
      exact absurd (Finset.mem_filter.mp ha).2 (tt_head_ne_s tt₂ a)
    have hz : (∑ a : G₂.A, if G₂.head a = G₂.s ∧ G₁.t = G₁.t then x (Sum.inr a) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      simp [tt_head_ne_s tt₂ a]
    have ho2 : outflow G₂ (fun a => x (Sum.inr a)) G₂.s =
        ∑ a : G₂.A, if G₂.tail a = G₂.s ∧ G₁.t = G₁.t then x (Sum.inr a) else 0 := by
      unfold outflow
      rw [Finset.sum_filter]
      simp
    rw [hz, ho1] at h
    rw [hi2, ho2]
    linarith
  · have h := hl.2.1 (Sum.inr ⟨w, hw⟩) (by rw [series_s]; exact Sum.inr_ne_inl)
    show IsLeast _ (l (seriesEmb G₁ G₂ w))
    rw [hemb w hw]
    convert h using 1
    ext r
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨Sum.inr a, ?_, (rhoArc_toRight Astar ν a _ _)⟩
      show seriesEmb G₁ G₂ (G₂.head a) = _
      rw [ha]; exact hemb w hw
    · rintro ⟨a, ha, rfl⟩
      rcases a with a | a
      · exact absurd ha Sum.inl_ne_inr
      · refine ⟨a, ?_, (rhoArc_toRight Astar ν a _ _).symm⟩
        exact (seriesEmb_eq_inr G₁ G₂ _ _).mp ha
  · have := hl.2.2 (Sum.inr a) ha
    simp only at this ⊢
    rw [rhoArc_toRight]
    exact this

theorem series_formula₁ (tt₁ : IsTwoTerminalDAG G₁) (tt₂ : IsTwoTerminalDAG G₂)
    (hst₁ : G₁.s ≠ G₁.t) (hst₂ : G₂.s ≠ G₂.t) (Astar : Finset (G₁.A ⊕ G₂.A))
    (ν : G₁.A ⊕ G₂.A → ℝ) (hν : ∀ a, 0 < ν a)
    (ρ : ℝ → (G₁.series G₂).V → ℝ) (ρ₁ : ℝ → G₁.V → ℝ)
    (hρ : IsLabelFunction (G₁.series G₂) Astar ν ρ)
    (hρ₁ : IsLabelFunction G₁ Astar.toLeft (fun a => ν (Sum.inl a)) ρ₁)
    (y : ℝ) (hy : 0 ≤ y) (v : G₁.V) : ρ y (Sum.inl v) = ρ₁ y v := by
  obtain ⟨hs, x, hx, hl⟩ := hρ y hy
  obtain ⟨r1, l1⟩ := series_restrict₁ tt₂ hst₁ hst₂ hx hl
  obtain ⟨hs1, x1, hx1, hl1⟩ := hρ₁ y hy
  have := corollary_15 G₁ Astar.toLeft (fun a => ν (Sum.inl a)) (tt_spg tt₁) hst₁
    (fun a => hν _) _ x1 _ (ρ₁ y) y r1 hx1 l1 hl1 (by rw [hs1]; exact hs)
  exact congrFun this v

theorem series_formula₂ (tt₁ : IsTwoTerminalDAG G₁) (tt₂ : IsTwoTerminalDAG G₂)
    (hst₁ : G₁.s ≠ G₁.t) (hst₂ : G₂.s ≠ G₂.t) (Astar : Finset (G₁.A ⊕ G₂.A))
    (ν : G₁.A ⊕ G₂.A → ℝ) (hν : ∀ a, 0 < ν a)
    (ρ : ℝ → (G₁.series G₂).V → ℝ) (ρ₁ : ℝ → G₁.V → ℝ) (ρ₂ : ℝ → G₂.V → ℝ)
    (hρ : IsLabelFunction (G₁.series G₂) Astar ν ρ)
    (hρ₁ : IsLabelFunction G₁ Astar.toLeft (fun a => ν (Sum.inl a)) ρ₁)
    (hρ₂ : IsLabelFunction G₂ Astar.toRight (fun a => ν (Sum.inr a)) ρ₂)
    (y : ℝ) (hy : 0 < y) (v : {v : G₂.V // v ≠ G₂.s}) :
    ρ y (Sum.inr v) = ρ₁ y G₁.t * ρ₂ (y / ρ₁ y G₁.t) v.1 := by
  obtain ⟨hs, x, hx, hl⟩ := hρ y hy.le
  obtain ⟨r2, l2⟩ := series_restrict₂ tt₁ tt₂ hst₁ hst₂ hx hl
  set c := ρ₁ y G₁.t with hc
  have hc0 : 0 < c := by
    obtain ⟨-, x1, hx1, hl1⟩ := hρ₁ y hy.le
    exact label_t_pos hst₁ (fun a => hν _) hy hx1 hl1
  have hcs : ρ y (seriesEmb G₁ G₂ G₂.s) = c := by
    have : seriesEmb G₁ G₂ G₂.s = Sum.inl G₁.t := (seriesEmb_eq_inl G₁ G₂ _ _).mpr ⟨rfl, rfl⟩
    rw [this, hc]
    exact series_formula₁ tt₁ tt₂ hst₁ hst₂ Astar ν hν ρ ρ₁ hρ hρ₁ y hy.le G₁.t
  have hd0 : 0 < 1 / c := one_div_pos.mpr hc0
  have sf := staticFlow_smul' hd0.le r2
  have sl := labels_smul' hd0 l2
  rw [show 1 / c * y = y / c by ring] at sf
  obtain ⟨hs2, x2, hx2, hl2⟩ := hρ₂ (y / c) (div_nonneg hy.le hc0.le)
  have := corollary_15 G₂ Astar.toRight (fun a => ν (Sum.inr a)) (tt_spg tt₂) hst₂
    (fun a => hν _) _ x2 _ (ρ₂ (y / c)) (y / c) sf hx2 sl hl2
    (by simp only [Pi.smul_apply, smul_eq_mul]; rw [hcs, hs2]; field_simp)
  have hv := congrFun this v.1
  simp only [Pi.smul_apply, smul_eq_mul] at hv
  have : seriesEmb G₁ G₂ v.1 = Sum.inr v := (seriesEmb_eq_inr G₁ G₂ _ _).mpr rfl
  rw [this] at hv
  rw [← hv]
  field_simp

end Series2

end ThinFlowSP.Breakpoints


namespace ThinFlowSP.Breakpoints

open Filter Topology

/-- In a shortest path graph, the flow on every arc is at most the flow value. -/
theorem flow_le_val {G : Net} (hG : IsShortestPathGraph G) (hst : G.s ≠ G.t) {x : G.A → ℝ}
    {val : ℝ} (hx : IsStaticFlow G x val) (hval : 0 ≤ val) (a : G.A) : x a ≤ val := by
  classical
  set U : Finset G.V := Finset.univ.filter (fun v => Reaches G v (G.tail a)) with hU
  have memU : ∀ v, v ∈ U ↔ Reaches G v (G.tail a) := fun v => by simp [hU]
  have key := sum_net' G x U
  -- right-hand side is at least `x a`
  have hg : ∀ b, 0 ≤ (if G.tail b ∈ U then x b else 0) - (if G.head b ∈ U then x b else 0) := by
    intro b
    by_cases hh : G.head b ∈ U
    · have ht : G.tail b ∈ U := by
        rw [memU] at hh ⊢
        exact Relation.ReflTransGen.head ⟨b, rfl, rfl⟩ hh
      simp [ht, hh]
    · by_cases ht : G.tail b ∈ U
      · simp [ht, hh, hx.1 b]
      · simp [ht, hh]
  have hta : G.tail a ∈ U := (memU _).mpr Relation.ReflTransGen.refl
  have hha : G.head a ∉ U := by
    rw [memU]
    intro h
    exact hG.1 (G.tail a) (Relation.TransGen.head' ⟨a, rfl, rfl⟩ h)
  have h1 : x a ≤ ∑ b, ((if G.tail b ∈ U then x b else 0) - (if G.head b ∈ U then x b else 0)) := by
    have := Finset.single_le_sum (fun b _ => hg b) (Finset.mem_univ a)
    simpa [hta, hha] using this
  -- left-hand side is at most `val`
  have h2 : ∑ u ∈ U, (outflow G x u - inflow G x u) ≤ val := by
    rw [← Finset.sum_filter_add_sum_filter_not U (fun u => u = G.s ∨ u = G.t)]
    have hz : ∑ u ∈ U.filter (fun u => ¬ (u = G.s ∨ u = G.t)), (outflow G x u - inflow G x u) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      have := (Finset.mem_filter.mp hu).2
      push Not at this
      exact hx.2.1 u this.1 this.2
    rw [hz, add_zero]
    have hsub : U.filter (fun u => u = G.s ∨ u = G.t) ⊆ {G.s, G.t} := by
      intro u hu
      have := (Finset.mem_filter.mp hu).2
      simp only [Finset.mem_insert, Finset.mem_singleton]; exact this
    have hnt := net_t' G hst x val hx
    calc ∑ u ∈ U.filter (fun u => u = G.s ∨ u = G.t), (outflow G x u - inflow G x u)
        ≤ ∑ u ∈ U.filter (fun u => u = G.s ∨ u = G.t),
            (if u = G.s then val else 0) := by
          apply Finset.sum_le_sum
          intro u hu
          rcases (Finset.mem_filter.mp hu).2 with h | h
          · subst h; rw [hx.2.2]; simp
          · subst h; rw [hnt]; simp [Ne.symm hst]; linarith
      _ ≤ ∑ u ∈ ({G.s, G.t} : Finset G.V), (if u = G.s then val else 0) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro u _ _; split_ifs <;> linarith
      _ = val := by
          rw [Finset.sum_pair hst]; simp [Ne.symm hst]
  linarith

/-- A non-decreasing function `f ≥ 0` with `f(y)/y` non-increasing is continuous on `(0,∞)`. -/
theorem cont_of_mono_ratio (f : ℝ → ℝ) (hmono : MonotoneOn f (Set.Ici 0))
    (hanti : AntitoneOn (fun r => f r / r) (Set.Ioi 0)) (hnn : ∀ y, 0 ≤ y → 0 ≤ f y)
    (y₀ : ℝ) (hy₀ : 0 < y₀) : ContinuousAt f y₀ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  set K := f (2 * y₀) + 1 with hK
  have hK0 : 0 < K := by have := hnn (2 * y₀) (by linarith); linarith
  refine ⟨min (y₀ / 2) (ε * y₀ / (4 * K)), lt_min (by linarith) (by positivity), ?_⟩
  intro y hy
  rw [Real.dist_eq] at hy ⊢
  have hy1 : |y - y₀| < y₀ / 2 := lt_of_lt_of_le hy (min_le_left _ _)
  have hy2 : |y - y₀| < ε * y₀ / (4 * K) := lt_of_lt_of_le hy (min_le_right _ _)
  rw [abs_lt] at hy1
  have hypos : 0 < y := by linarith
  have hfy0 : f y₀ ≤ f (2 * y₀) := hmono (Set.mem_Ici.mpr hy₀.le)
    (Set.mem_Ici.mpr (by linarith)) (by linarith)
  have hfy : f y ≤ f (2 * y₀) := hmono (Set.mem_Ici.mpr hypos.le)
    (Set.mem_Ici.mpr (by linarith)) (by linarith)
  have hfy0n := hnn y₀ hy₀.le
  have hfyn := hnn y hypos.le
  rcases le_total y₀ y with h | h
  · have m1 : f y₀ ≤ f y := hmono (Set.mem_Ici.mpr hy₀.le) (Set.mem_Ici.mpr hypos.le) h
    have m2 : f y / y ≤ f y₀ / y₀ := hanti hy₀ hypos h
    rw [div_le_div_iff₀ hypos hy₀] at m2
    -- f y - f y₀ ≤ f y₀ (y - y₀) / y₀
    have m3 : (f y - f y₀) * y₀ ≤ f y₀ * (y - y₀) := by nlinarith
    have hd : y - y₀ < ε * y₀ / (4 * K) := by rw [abs_lt] at hy2; linarith
    have m4 : f y₀ * (y - y₀) ≤ K * (ε * y₀ / (4 * K)) := by
      apply mul_le_mul (by linarith) hd.le (by linarith) hK0.le
    have m5 : K * (ε * y₀ / (4 * K)) = ε * y₀ / 4 := by field_simp
    rw [abs_of_nonneg (by linarith)]
    have : (f y - f y₀) * y₀ < ε * y₀ := by nlinarith
    nlinarith
  · have m1 : f y ≤ f y₀ := hmono (Set.mem_Ici.mpr hypos.le) (Set.mem_Ici.mpr hy₀.le) h
    have m2 : f y₀ / y₀ ≤ f y / y := hanti hypos hy₀ h
    rw [div_le_div_iff₀ hy₀ hypos] at m2
    have m3 : (f y₀ - f y) * y ≤ f y * (y₀ - y) := by nlinarith
    have hd : y₀ - y < ε * y₀ / (4 * K) := by rw [abs_lt] at hy2; linarith
    have m4 : f y * (y₀ - y) ≤ K * (ε * y₀ / (4 * K)) := by
      apply mul_le_mul (by linarith) hd.le (by linarith) hK0.le
    have m5 : K * (ε * y₀ / (4 * K)) = ε * y₀ / 4 := by field_simp
    rw [abs_of_nonpos (by linarith)]
    have : (f y₀ - f y) * y < ε * y := by nlinarith
    nlinarith

theorem rhoArc_mono' {G : Net} (Astar : Finset G.A) (ν : G.A → ℝ) (a : G.A) (hν : 0 < ν a)
    {lv lv' xa xa' : ℝ} (hl : lv ≤ lv') (hx : xa ≤ xa') :
    rhoArc Astar ν a lv xa ≤ rhoArc Astar ν a lv' xa' := by
  have h : xa / ν a ≤ xa' / ν a := div_le_div_of_nonneg_right hx hν.le
  unfold rhoArc
  split_ifs
  · exact h
  · exact max_le_max hl h

theorem rhoArc_shift {G : Net} (Astar : Finset G.A) (ν : G.A → ℝ) (a : G.A) (hν : 0 < ν a)
    (lv e : ℝ) : rhoArc Astar ν a (lv + e) (e * ν a) = rhoArc Astar ν a lv 0 + e := by
  unfold rhoArc
  have : e * ν a / ν a = e := by field_simp
  split_ifs
  · rw [this]; simp
  · rw [this, zero_div, ← max_add_add_right, zero_add]

/-- Right-continuity at `0` of a label function. -/
theorem label_cont_zero {G : Net} (hG : IsShortestPathGraph G) (hst : G.s ≠ G.t)
    {Astar : Finset G.A} {ν : G.A → ℝ} (hν : ∀ a, 0 < ν a) {ρ : ℝ → G.V → ℝ}
    (hρ : IsLabelFunction G Astar ν ρ) (v : G.V) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ y, 0 ≤ y → y < δ → ρ y v < ρ 0 v + ε := by
  have hmono : ∀ u, MonotoneOn (fun r => ρ r u) (Set.Ici 0) := fun u =>
    ((lemma_18 G Astar ν hG hst hν).2 ρ hρ u).1
  have hnn : ∀ y, 0 ≤ y → ∀ u, 0 ≤ ρ y u := by
    intro y hy u
    obtain ⟨-, x, -, hl⟩ := hρ y hy
    exact hl.1 u
  set L : G.V → ℝ := fun u => ⨅ y : Set.Ioi (0:ℝ), ρ y u with hL
  have hne : Nonempty (Set.Ioi (0:ℝ)) := ⟨⟨1, by norm_num⟩⟩
  have hbdd : ∀ u, BddBelow (Set.range fun y : Set.Ioi (0:ℝ) => ρ y u) := by
    intro u; refine ⟨0, ?_⟩; rintro _ ⟨y, rfl⟩; exact hnn y (le_of_lt y.2) u
  have hLle : ∀ u (y : ℝ), 0 < y → L u ≤ ρ y u := fun u y hy =>
    ciInf_le (hbdd u) ⟨y, hy⟩
  have hLge : ∀ u (c : ℝ), (∀ y : ℝ, 0 < y → c ≤ ρ y u) → c ≤ L u := fun u c h =>
    le_ciInf fun y => h y y.2
  have hLlt : ∀ u (c : ℝ), L u < c → ∃ y : ℝ, 0 < y ∧ ρ y u < c := by
    intro u c h
    obtain ⟨y, hy⟩ := exists_lt_of_ciInf_lt h
    exact ⟨y, y.2, hy⟩
  -- `L` are thin-flow labels of the zero flow
  have hL0 : IsThinFlowLabels G Astar ν 0 L := by
    refine ⟨fun u => hLge u 0 (fun y hy => hnn y hy.le u), fun w hw => ?_, fun a ha => ?_⟩
    · -- lower bound
      have hlow : ∀ a, G.head a = w → L w ≤ rhoArc Astar ν a (L (G.tail a)) 0 := by
        intro a ha
        by_contra hcon
        push Not at hcon
        set d := L w - rhoArc Astar ν a (L (G.tail a)) 0 with hd
        have hd0 : 0 < d := by linarith
        obtain ⟨y₁, hy₁, hy₁'⟩ := hLlt (G.tail a) (L (G.tail a) + d / 2) (by linarith)
        set y := min y₁ (d / 4 * ν a) with hy
        have hy0 : 0 < y := lt_min hy₁ (by have := hν a; positivity)
        obtain ⟨-, x, hx, hl⟩ := hρ y hy0.le
        have e1 : ρ y w ≤ rhoArc Astar ν a (ρ y (G.tail a)) (x a) := (hl.2.1 w hw).2 ⟨a, ha, rfl⟩
        have e2 : ρ y (G.tail a) ≤ L (G.tail a) + d / 2 := by
          have := hmono (G.tail a) (Set.mem_Ici.mpr hy0.le) (Set.mem_Ici.mpr hy₁.le)
            (min_le_left _ _)
          simp only at this; linarith
        have e3 : x a ≤ d / 2 * ν a := by
          have := flow_le_val hG hst hx hy0.le a
          have := min_le_right y₁ (d / 4 * ν a)
          have := hν a
          nlinarith
        have e4 := rhoArc_mono' Astar ν a (hν a) e2 e3
        rw [rhoArc_shift Astar ν a (hν a)] at e4
        have e5 := hLle w y hy0
        linarith
      -- membership: a minimizing arc
      obtain ⟨-, x1, -, hl1⟩ := hρ 1 zero_le_one
      obtain ⟨⟨a₁, ha₁, -⟩, -⟩ := hl1.2.1 w hw
      have hnonempty : (Finset.univ.filter fun a => G.head a = w).Nonempty :=
        ⟨a₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha₁⟩⟩
      obtain ⟨a', ha', hmin⟩ := Finset.exists_min_image _
        (fun a => rhoArc Astar ν a (L (G.tail a)) 0) hnonempty
      have ha'w : G.head a' = w := (Finset.mem_filter.mp ha').2
      refine ⟨⟨a', ha'w, le_antisymm (hlow a' ha'w) ?_⟩, ?_⟩
      · show rhoArc Astar ν a' (L (G.tail a')) 0 ≤ L w
        apply hLge
        intro y hy
        obtain ⟨-, x, hx, hl⟩ := hρ y hy.le
        obtain ⟨⟨b, hb, hbe⟩, -⟩ := hl.2.1 w hw
        rw [hbe]
        calc rhoArc Astar ν a' (L (G.tail a')) 0 ≤ rhoArc Astar ν b (L (G.tail b)) 0 :=
              hmin b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
          _ ≤ rhoArc Astar ν b (ρ y (G.tail b)) (x b) :=
              rhoArc_mono' Astar ν b (hν b) (hLle _ y hy) (hx.1 b)
      · rintro r ⟨b, hb, rfl⟩
        exact hlow b hb
    · simp at ha
  have hLs : L G.s = 1 := by
    apply le_antisymm
    · have := hLle G.s 1 one_pos
      rw [(hρ 1 zero_le_one).1] at this; exact this
    · exact hLge G.s 1 (fun y hy => by rw [(hρ y hy.le).1])
  have hzero : IsStaticFlow G (0 : G.A → ℝ) 0 := by
    refine ⟨fun a => le_rfl, fun u _ _ => ?_, ?_⟩ <;> simp [outflow, inflow]
  obtain ⟨hs0, x0, hx0, hl0⟩ := hρ 0 le_rfl
  have hLeq : L = ρ 0 := corollary_15 G Astar ν hG hst hν 0 x0 L (ρ 0) 0 hzero hx0 hL0 hl0
    (by rw [hLs, hs0])
  obtain ⟨y, hy, hyv⟩ := hLlt v (ρ 0 v + ε) (by rw [hLeq]; linarith)
  refine ⟨y, hy, fun y' hy' hy'y => ?_⟩
  have := hmono v (Set.mem_Ici.mpr hy') (Set.mem_Ici.mpr hy.le) hy'y.le
  simp only at this
  linarith

/-- Every label function of a shortest path graph is continuous on `[0, ∞)`. -/
theorem label_continuousOn {G : Net} (hG : IsShortestPathGraph G) (hst : G.s ≠ G.t)
    {Astar : Finset G.A} {ν : G.A → ℝ} (hν : ∀ a, 0 < ν a) {ρ : ℝ → G.V → ℝ}
    (hρ : IsLabelFunction G Astar ν ρ) : ContinuousOn ρ (Set.Ici 0) := by
  have hmono : ∀ u, MonotoneOn (fun r => ρ r u) (Set.Ici 0) := fun u =>
    ((lemma_18 G Astar ν hG hst hν).2 ρ hρ u).1
  have hanti : ∀ u, AntitoneOn (fun r => ρ r u / r) (Set.Ioi 0) := fun u =>
    ((lemma_18 G Astar ν hG hst hν).2 ρ hρ u).2
  have hnn : ∀ y, 0 ≤ y → ∀ u, 0 ≤ ρ y u := by
    intro y hy u
    obtain ⟨-, x, -, hl⟩ := hρ y hy
    exact hl.1 u
  rw [continuousOn_pi]
  intro u y₀ hy₀
  rcases (Set.mem_Ici.mp hy₀).lt_or_eq with hpos | hz
  · exact (cont_of_mono_ratio (fun r => ρ r u) (hmono u) (hanti u) (fun y hy => hnn y hy u)
      y₀ hpos).continuousWithinAt
  · subst hz
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := label_cont_zero hG hst hν hρ u ε hε
    refine ⟨δ, hδ, fun y hy hyd => ?_⟩
    have hy0 : 0 ≤ y := hy
    rw [Real.dist_eq, abs_lt] at hyd ⊢
    have h1 := h y hy0 (by linarith)
    have h2 := hmono u (Set.mem_Ici.mpr le_rfl) hy (hy0)
    simp only at h2
    constructor <;> linarith

end ThinFlowSP.Breakpoints


namespace ThinFlowSP.Breakpoints

set_option allowUnsafeReducibility true in
attribute [local reducible] Net.series Net.par

theorem labels_smul0 {G : Net} {Astar : Finset G.A} {ν : G.A → ℝ} {x : G.A → ℝ} {l : G.V → ℝ}
    {c : ℝ} (hc : 0 ≤ c) (hl : IsThinFlowLabels G Astar ν x l) :
    IsThinFlowLabels G Astar ν (c • x) (c • l) := by
  simp only [IsThinFlowLabels, Pi.smul_apply, smul_eq_mul]
  refine ⟨fun v => mul_nonneg hc (hl.1 v), fun w hw => ?_, fun a ha => ?_⟩
  · obtain ⟨⟨a, ha, e⟩, hlb⟩ := hl.2.1 w hw
    refine ⟨⟨a, ha, ?_⟩, ?_⟩
    · rw [rhoArc_smul' Astar ν a hc, e]
    · rintro r ⟨b, hb, rfl⟩
      rw [rhoArc_smul' Astar ν b hc]
      exact mul_le_mul_of_nonneg_left (hlb ⟨b, hb, rfl⟩) hc
  · have ha' : 0 < x a := by
      by_contra h; push Not at h; nlinarith
    rw [rhoArc_smul' Astar ν a hc, hl.2.2 a ha']

section SeriesGlue

variable {G₁ G₂ : Net}

theorem seriesEmb_label (l₁ : G₁.V → ℝ) (l₂ : G₂.V → ℝ) (h : l₂ G₂.s = l₁ G₁.t) (v : G₂.V) :
    (Sum.elim l₁ (fun u : {u : G₂.V // u ≠ G₂.s} => l₂ u.1) : (G₁.series G₂).V → ℝ)
      (seriesEmb G₁ G₂ v) = l₂ v := by
  unfold seriesEmb
  split_ifs with hv
  · subst hv; simp [h]
  · simp

theorem series_glue (tt₁ : IsTwoTerminalDAG G₁) (tt₂ : IsTwoTerminalDAG G₂)
    (hst₁ : G₁.s ≠ G₁.t) (hst₂ : G₂.s ≠ G₂.t) {Astar : Finset (G₁.A ⊕ G₂.A)}
    {ν : G₁.A ⊕ G₂.A → ℝ} {x₁ : G₁.A → ℝ} {x₂ : G₂.A → ℝ} {l₁ : G₁.V → ℝ} {l₂ : G₂.V → ℝ}
    {y : ℝ} (hx₁ : IsStaticFlow G₁ x₁ y) (hx₂ : IsStaticFlow G₂ x₂ y)
    (hl₁ : IsThinFlowLabels G₁ Astar.toLeft (fun a => ν (Sum.inl a)) x₁ l₁)
    (hl₂ : IsThinFlowLabels G₂ Astar.toRight (fun a => ν (Sum.inr a)) x₂ l₂)
    (h : l₂ G₂.s = l₁ G₁.t) :
    IsStaticFlow (G₁.series G₂) (Sum.elim x₁ x₂) y ∧
    IsThinFlowLabels (G₁.series G₂) Astar ν (Sum.elim x₁ x₂)
      (Sum.elim l₁ (fun u : {u : G₂.V // u ≠ G₂.s} => l₂ u.1)) := by
  set l : (G₁.series G₂).V → ℝ := Sum.elim l₁ (fun u : {u : G₂.V // u ≠ G₂.s} => l₂ u.1) with hl
  have hemb := seriesEmb_label l₁ l₂ h
  have ho1 : outflow G₁ x₁ G₁.t = 0 := by
    unfold outflow; apply Finset.sum_eq_zero; intro a ha
    exact absurd (Finset.mem_filter.mp ha).2 (tt_tail_ne_t tt₁ a)
  have hi2 : inflow G₂ x₂ G₂.s = 0 := by
    unfold inflow; apply Finset.sum_eq_zero; intro a ha
    exact absurd (Finset.mem_filter.mp ha).2 (tt_head_ne_s tt₂ a)
  have hz : ∀ v : G₁.V, (∑ a : G₂.A, if G₂.head a = G₂.s ∧ G₁.t = v then x₂ a else 0) = 0 := by
    intro v; apply Finset.sum_eq_zero; intro a _
    simp [tt_head_ne_s tt₂ a]
  have hz' : ∀ v : G₁.V, G₁.t ≠ v →
      (∑ a : G₂.A, if G₂.tail a = G₂.s ∧ G₁.t = v then x₂ a else 0) = 0 := by
    intro v hv; apply Finset.sum_eq_zero; intro a _
    simp [hv]
  have ho2 : outflow G₂ x₂ G₂.s =
      ∑ a : G₂.A, if G₂.tail a = G₂.s ∧ G₁.t = G₁.t then x₂ a else 0 := by
    unfold outflow; rw [Finset.sum_filter]; simp
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rintro (a | a)
    · exact hx₁.1 a
    · exact hx₂.1 a
  · rintro (v | ⟨v, hv⟩) hs ht
    · have hvs : v ≠ G₁.s := fun e => hs (by rw [e])
      have h1 := series_outflow_inl G₁ G₂ (Sum.elim x₁ x₂) v
      have h2 := series_inflow_inl G₁ G₂ (Sum.elim x₁ x₂) v
      simp only [Sum.elim_inl, Sum.elim_inr] at h1 h2
      rw [h1, h2, hz v, add_zero]
      by_cases hvt : v = G₁.t
      · subst hvt
        rw [ho1, zero_add, ← ho2]
        have n1 := net_t' G₁ hst₁ x₁ y hx₁
        have n2 := hx₂.2.2
        rw [ho1] at n1; rw [hi2] at n2
        linarith
      · rw [hz' v (Ne.symm hvt), add_zero]
        exact hx₁.2.1 v hvs hvt
    · have hvt : v ≠ G₂.t := by
        intro e; apply ht; rw [series_t hst₂]; subst e; rfl
      rw [series_outflow_inr, series_inflow_inr]
      exact hx₂.2.1 v hv hvt
  · have h1 := series_outflow_inl G₁ G₂ (Sum.elim x₁ x₂) G₁.s
    have h2 := series_inflow_inl G₁ G₂ (Sum.elim x₁ x₂) G₁.s
    simp only [Sum.elim_inl, Sum.elim_inr] at h1 h2
    rw [series_s, h1, h2, hz' G₁.s (Ne.symm hst₁), hz, add_zero, add_zero]
    exact hx₁.2.2
  · rintro (v | v)
    · exact hl₁.1 v
    · exact hl₂.1 v.1
  · rintro (w | ⟨w, hw⟩) hws
    · have hw' : w ≠ G₁.s := fun e => hws (by rw [e])
      have h1 := hl₁.2.1 w hw'
      show IsLeast _ (l₁ w)
      convert h1 using 1
      ext r
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨a, ha, rfl⟩
        rcases a with a | a
        · exact ⟨a, Sum.inl.inj ha, (rhoArc_toLeft Astar ν a _ _).symm⟩
        · exfalso
          exact tt_head_ne_s tt₂ a ((seriesEmb_eq_inl G₁ G₂ _ _).mp ha).1
      · rintro ⟨a, ha, rfl⟩
        exact ⟨Sum.inl a, by rw [← ha]; rfl, rhoArc_toLeft Astar ν a _ _⟩
    · have h1 := hl₂.2.1 w hw
      show IsLeast _ (l₂ w)
      convert h1 using 1
      ext r
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨a, ha, rfl⟩
        rcases a with a | a
        · exact absurd ha Sum.inl_ne_inr
        · refine ⟨a, (seriesEmb_eq_inr G₁ G₂ _ _).mp ha, ?_⟩
          rw [← rhoArc_toRight Astar ν a]
          congr 1
          exact hemb _
      · rintro ⟨a, ha, rfl⟩
        refine ⟨Sum.inr a, ?_, ?_⟩
        · show seriesEmb G₁ G₂ (G₂.head a) = _
          exact (seriesEmb_eq_inr G₁ G₂ _ _).mpr ha
        · rw [← rhoArc_toRight Astar ν a]
          congr 1
          exact (hemb _).symm
  · rintro (a | a) ha
    · rw [← rhoArc_toLeft Astar ν a]
      exact hl₁.2.2 a ha
    · rw [← rhoArc_toRight Astar ν a]
      have := hl₂.2.2 a ha
      rw [← hemb (G₂.head a), ← hemb (G₂.tail a)] at this
      exact this

end SeriesGlue

theorem inflow_t_eq {G : Net} (tt : IsTwoTerminalDAG G) (hst : G.s ≠ G.t) {x : G.A → ℝ} {y : ℝ}
    (hx : IsStaticFlow G x y) : inflow G x G.t = y := by
  have h := net_t' G hst x y hx
  have ho : outflow G x G.t = 0 := by
    unfold outflow; apply Finset.sum_eq_zero; intro a ha
    exact absurd (Finset.mem_filter.mp ha).2 (tt_tail_ne_t tt a)
  linarith

theorem pos_of_arc_into_t {G : Net} (tt : IsTwoTerminalDAG G) (hst : G.s ≠ G.t) {x : G.A → ℝ}
    {y : ℝ} (hx : IsStaticFlow G x y) (a : G.A) (ha : G.head a = G.t) (hxa : 0 < x a) : 0 < y := by
  rw [← inflow_t_eq tt hst hx]
  unfold inflow
  exact lt_of_lt_of_le hxa (Finset.single_le_sum (fun b _ => hx.1 b)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩))

section ParGlue

variable {G₁ G₂ : Net}

theorem parEmb_s : parEmb G₁ G₂ G₂.s = Sum.inl G₁.s := by simp [parEmb]

theorem parEmb_t (h₂ : G₂.s ≠ G₂.t) : parEmb G₁ G₂ G₂.t = Sum.inl G₁.t := by
  simp [parEmb, Ne.symm h₂]

theorem parEmb_eq_inl (w : G₂.V) (v : G₁.V) :
    parEmb G₁ G₂ w = Sum.inl v ↔ (w = G₂.s ∧ G₁.s = v) ∨ (w ≠ G₂.s ∧ w = G₂.t ∧ G₁.t = v) := by
  unfold parEmb
  split_ifs with h1 h2
  · simp [h1]
  · subst h2; simp [h1]
  · simp [h1, h2]

theorem parEmb_eq_inr (w : G₂.V) (v : {v : G₂.V // v ≠ G₂.s ∧ v ≠ G₂.t}) :
    parEmb G₁ G₂ w = Sum.inr v ↔ w = v.1 := by
  unfold parEmb
  split_ifs with h1 h2
  · simp only [false_iff]; intro e; exact v.2.1 (e ▸ h1)
  · simp only [false_iff]; intro e; exact v.2.2 (e ▸ h2)
  · constructor
    · intro e; cases e; rfl
    · intro e; subst e; rfl

theorem sum_par_A (f : (G₁.par G₂).A → ℝ) :
    ∑ a, f a = ∑ a : G₁.A, f (Sum.inl a) + ∑ a : G₂.A, f (Sum.inr a) :=
  Fintype.sum_sum_type f

theorem par_outflow_inl (x : G₁.A ⊕ G₂.A → ℝ) (v : G₁.V) :
    outflow (G₁.par G₂) x (Sum.inl v) = outflow G₁ (fun a => x (Sum.inl a)) v +
      ∑ a : G₂.A, if parEmb G₁ G₂ (G₂.tail a) = Sum.inl v then x (Sum.inr a) else 0 := by
  unfold outflow
  rw [Finset.sum_filter, Finset.sum_filter, sum_par_A]
  congr 1
  apply Finset.sum_congr rfl; intro a _
  simp [Net.par]

theorem par_inflow_inl (x : G₁.A ⊕ G₂.A → ℝ) (v : G₁.V) :
    inflow (G₁.par G₂) x (Sum.inl v) = inflow G₁ (fun a => x (Sum.inl a)) v +
      ∑ a : G₂.A, if parEmb G₁ G₂ (G₂.head a) = Sum.inl v then x (Sum.inr a) else 0 := by
  unfold inflow
  rw [Finset.sum_filter, Finset.sum_filter, sum_par_A]
  congr 1
  apply Finset.sum_congr rfl; intro a _
  simp [Net.par]

theorem par_outflow_inr (x : G₁.A ⊕ G₂.A → ℝ) (v : {v : G₂.V // v ≠ G₂.s ∧ v ≠ G₂.t}) :
    outflow (G₁.par G₂) x (Sum.inr v) = outflow G₂ (fun a => x (Sum.inr a)) v.1 := by
  unfold outflow
  rw [Finset.sum_filter, Finset.sum_filter, sum_par_A]
  rw [Finset.sum_eq_zero (fun a _ => by simp [Net.par]), zero_add]
  apply Finset.sum_congr rfl; intro a _
  simp only [Net.par, Sum.elim_inr, parEmb_eq_inr]

theorem par_inflow_inr (x : G₁.A ⊕ G₂.A → ℝ) (v : {v : G₂.V // v ≠ G₂.s ∧ v ≠ G₂.t}) :
    inflow (G₁.par G₂) x (Sum.inr v) = inflow G₂ (fun a => x (Sum.inr a)) v.1 := by
  unfold inflow
  rw [Finset.sum_filter, Finset.sum_filter, sum_par_A]
  rw [Finset.sum_eq_zero (fun a _ => by simp [Net.par]), zero_add]
  apply Finset.sum_congr rfl; intro a _
  simp only [Net.par, Sum.elim_inr, parEmb_eq_inr]

theorem par_s : (G₁.par G₂).s = Sum.inl G₁.s := rfl
theorem par_t : (G₁.par G₂).t = Sum.inl G₁.t := rfl

theorem rhoArc_parL (Astar : Finset (G₁.A ⊕ G₂.A)) (ν : G₁.A ⊕ G₂.A → ℝ) (a : G₁.A)
    (lv xa : ℝ) :
    rhoArc (G := G₁) (Finset.toLeft Astar) (fun a => ν (Sum.inl a)) a lv xa =
      rhoArc (G := G₁.par G₂) Astar ν (Sum.inl a) lv xa := by
  show (if a ∈ Astar.toLeft then xa / ν (Sum.inl a) else max lv (xa / ν (Sum.inl a))) =
    (if (Sum.inl a : G₁.A ⊕ G₂.A) ∈ Astar then xa / ν (Sum.inl a)
      else max lv (xa / ν (Sum.inl a)))
  simp only [Finset.mem_toLeft]

theorem rhoArc_parR (Astar : Finset (G₁.A ⊕ G₂.A)) (ν : G₁.A ⊕ G₂.A → ℝ) (a : G₂.A)
    (lv xa : ℝ) :
    rhoArc (G := G₂) (Finset.toRight Astar) (fun a => ν (Sum.inr a)) a lv xa =
      rhoArc (G := G₁.par G₂) Astar ν (Sum.inr a) lv xa := by
  show (if a ∈ Astar.toRight then xa / ν (Sum.inr a) else max lv (xa / ν (Sum.inr a))) =
    (if (Sum.inr a : G₁.A ⊕ G₂.A) ∈ Astar then xa / ν (Sum.inr a)
      else max lv (xa / ν (Sum.inr a)))
  simp only [Finset.mem_toRight]

/-- The glued labels of a parallel composition. -/
def parLabels (G₁ G₂ : Net) (l₁ : G₁.V → ℝ) (l₂ : G₂.V → ℝ) (lam : ℝ) : (G₁.par G₂).V → ℝ :=
  Sum.elim (fun v => if v = G₁.t then lam else l₁ v)
    (fun u : {u : G₂.V // u ≠ G₂.s ∧ u ≠ G₂.t} => l₂ u.1)

theorem parLabels_emb (hst₁ : G₁.s ≠ G₁.t) (l₁ : G₁.V → ℝ) (l₂ : G₂.V → ℝ) (lam : ℝ)
    (hs : l₁ G₁.s = l₂ G₂.s) (w : G₂.V) (hw : w ≠ G₂.t) :
    parLabels G₁ G₂ l₁ l₂ lam (parEmb G₁ G₂ w) = l₂ w := by
  unfold parEmb parLabels
  split_ifs with h1
  · subst h1; simp [hst₁, hs]
  · simp

theorem par_glue (tt₁ : IsTwoTerminalDAG G₁) (tt₂ : IsTwoTerminalDAG G₂)
    (hst₁ : G₁.s ≠ G₁.t) (hst₂ : G₂.s ≠ G₂.t) {Astar : Finset (G₁.A ⊕ G₂.A)}
    {ν : G₁.A ⊕ G₂.A → ℝ} {x₁ : G₁.A → ℝ} {x₂ : G₂.A → ℝ} {l₁ : G₁.V → ℝ} {l₂ : G₂.V → ℝ}
    {y₁ y₂ lam : ℝ} (hx₁ : IsStaticFlow G₁ x₁ y₁) (hx₂ : IsStaticFlow G₂ x₂ y₂)
    (hl₁ : IsThinFlowLabels G₁ Astar.toLeft (fun a => ν (Sum.inl a)) x₁ l₁)
    (hl₂ : IsThinFlowLabels G₂ Astar.toRight (fun a => ν (Sum.inr a)) x₂ l₂)
    (hs : l₁ G₁.s = l₂ G₂.s) (hlam : lam = min (l₁ G₁.t) (l₂ G₂.t))
    (h₁ : 0 < y₁ → lam = l₁ G₁.t) (h₂ : 0 < y₂ → lam = l₂ G₂.t) :
    IsStaticFlow (G₁.par G₂) (Sum.elim x₁ x₂) (y₁ + y₂) ∧
    IsThinFlowLabels (G₁.par G₂) Astar ν (Sum.elim x₁ x₂) (parLabels G₁ G₂ l₁ l₂ lam) := by
  set L := parLabels G₁ G₂ l₁ l₂ lam with hL
  have hemb : ∀ w, w ≠ G₂.t → L (parEmb G₁ G₂ w) = l₂ w := parLabels_emb hst₁ l₁ l₂ lam hs
  have hLin : ∀ v, v ≠ G₁.t → L (Sum.inl v) = l₁ v := by
    intro v hv; simp [hL, parLabels, hv]
  have hLt : L (Sum.inl G₁.t) = lam := by simp [hL, parLabels]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rintro (a | a)
    · exact hx₁.1 a
    · exact hx₂.1 a
  · rintro (v | ⟨v, hv⟩) hs' ht'
    · have hvs : v ≠ G₁.s := fun e => hs' (by rw [e])
      have hvt : v ≠ G₁.t := fun e => ht' (by rw [e])
      have h1 := par_outflow_inl (G₁ := G₁) (G₂ := G₂) (Sum.elim x₁ x₂) v
      have h2 := par_inflow_inl (G₁ := G₁) (G₂ := G₂) (Sum.elim x₁ x₂) v
      have hz : ∀ w : G₂.V, ¬ parEmb G₁ G₂ w = Sum.inl v := by
        intro w hw
        rcases (parEmb_eq_inl w v).mp hw with ⟨-, e⟩ | ⟨-, -, e⟩
        · exact hvs e.symm
        · exact hvt e.symm
      simp only [Sum.elim_inl, Sum.elim_inr, hz, if_false, Finset.sum_const_zero,
        add_zero] at h1 h2
      rw [h1, h2]
      exact hx₁.2.1 v hvs hvt
    · rw [par_outflow_inr, par_inflow_inr]
      exact hx₂.2.1 v hv.1 hv.2
  · have h1 := par_outflow_inl (G₁ := G₁) (G₂ := G₂) (Sum.elim x₁ x₂) G₁.s
    have h2 := par_inflow_inl (G₁ := G₁) (G₂ := G₂) (Sum.elim x₁ x₂) G₁.s
    have hiff : ∀ w : G₂.V, parEmb G₁ G₂ w = Sum.inl G₁.s ↔ w = G₂.s := by
      intro w; rw [parEmb_eq_inl]
      constructor
      · rintro (⟨h, -⟩ | ⟨-, -, h⟩)
        · exact h
        · exact absurd h.symm hst₁
      · intro h; exact Or.inl ⟨h, rfl⟩
    simp only [Sum.elim_inl, Sum.elim_inr, hiff] at h1 h2
    rw [par_s, h1, h2]
    have o2 : (∑ a : G₂.A, if G₂.tail a = G₂.s then x₂ a else 0) = outflow G₂ x₂ G₂.s := by
      unfold outflow; rw [Finset.sum_filter]
    have i2 : (∑ a : G₂.A, if G₂.head a = G₂.s then x₂ a else 0) = inflow G₂ x₂ G₂.s := by
      unfold inflow; rw [Finset.sum_filter]
    rw [o2, i2]
    have := hx₁.2.2; have := hx₂.2.2
    linarith
  · rintro (v | v)
    · by_cases hv : v = G₁.t
      · subst hv; rw [hLt, hlam]; exact le_min (hl₁.1 _) (hl₂.1 _)
      · rw [hLin v hv]; exact hl₁.1 v
    · exact hl₂.1 v.1
  · rintro (w | ⟨w, hw⟩) hws
    · have hw' : w ≠ G₁.s := fun e => hws (by rw [e])
      by_cases hwt : w = G₁.t
      · subst hwt
        rw [hLt, hlam]
        have hU := (hl₁.2.1 G₁.t (Ne.symm hst₁)).union (hl₂.2.1 G₂.t (Ne.symm hst₂))
        convert hU using 1
        on_goal 1 => exact rfl
        ext r
        simp only [Set.mem_union, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨a, ha, rfl⟩
          rcases a with a | a
          · left
            refine ⟨a, Sum.inl.inj ha, ?_⟩
            rw [← rhoArc_parL Astar ν a]
            congr 1
            exact hLin _ (tt_tail_ne_t tt₁ a)
          · right
            have hh : G₂.head a = G₂.t := by
              rcases (parEmb_eq_inl _ _).mp ha with ⟨-, e⟩ | ⟨-, e, -⟩
              · exact absurd e hst₁
              · exact e
            refine ⟨a, hh, ?_⟩
            rw [← rhoArc_parR Astar ν a]
            congr 1
            exact hemb _ (tt_tail_ne_t tt₂ a)
        · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
          · refine ⟨Sum.inl a, by rw [← ha]; rfl, ?_⟩
            rw [← rhoArc_parL Astar ν a]
            congr 1
            exact (hLin _ (tt_tail_ne_t tt₁ a)).symm
          · refine ⟨Sum.inr a, ?_, ?_⟩
            · show parEmb G₁ G₂ (G₂.head a) = _
              rw [ha]; exact parEmb_t hst₂
            · rw [← rhoArc_parR Astar ν a]
              congr 1
              exact (hemb _ (tt_tail_ne_t tt₂ a)).symm
      · rw [hLin w hwt]
        have h1 := hl₁.2.1 w hw'
        convert h1 using 1
        ext r
        simp only [Set.mem_ofPred_eq]
        constructor
        · rintro ⟨a, ha, rfl⟩
          rcases a with a | a
          · refine ⟨a, Sum.inl.inj ha, ?_⟩
            rw [← rhoArc_parL Astar ν a]
            congr 1
            exact hLin _ (tt_tail_ne_t tt₁ a)
          · exfalso
            rcases (parEmb_eq_inl _ _).mp ha with ⟨-, e⟩ | ⟨-, -, e⟩
            · exact hw' e.symm
            · exact hwt e.symm
        · rintro ⟨a, ha, rfl⟩
          refine ⟨Sum.inl a, by rw [← ha]; rfl, ?_⟩
          rw [← rhoArc_parL Astar ν a]
          congr 1
          exact (hLin _ (tt_tail_ne_t tt₁ a)).symm
    · have h1 := hl₂.2.1 w hw.1
      show IsLeast _ (l₂ w)
      convert h1 using 1
      ext r
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨a, ha, rfl⟩
        rcases a with a | a
        · exact absurd ha Sum.inl_ne_inr
        · refine ⟨a, (parEmb_eq_inr _ _).mp ha, ?_⟩
          rw [← rhoArc_parR Astar ν a]
          congr 1
          exact hemb _ (tt_tail_ne_t tt₂ a)
      · rintro ⟨a, ha, rfl⟩
        refine ⟨Sum.inr a, ?_, ?_⟩
        · show parEmb G₁ G₂ (G₂.head a) = _
          exact (parEmb_eq_inr _ _).mpr ha
        · rw [← rhoArc_parR Astar ν a]
          congr 1
          exact (hemb _ (tt_tail_ne_t tt₂ a)).symm
  · rintro (a | a) ha
    · rw [← rhoArc_parL Astar ν a]
      have e := hl₁.2.2 a ha
      have ht : L (Sum.inl (G₁.tail a)) = l₁ (G₁.tail a) := hLin _ (tt_tail_ne_t tt₁ a)
      show L (Sum.inl (G₁.head a)) = rhoArc _ _ a (L (Sum.inl (G₁.tail a))) (x₁ a)
      rw [ht]
      by_cases hh : G₁.head a = G₁.t
      · rw [hh, hLt, h₁ (pos_of_arc_into_t tt₁ hst₁ hx₁ a hh ha), ← hh]; exact e
      · rw [hLin _ hh]; exact e
    · rw [← rhoArc_parR Astar ν a]
      have e := hl₂.2.2 a ha
      show L (parEmb G₁ G₂ (G₂.head a)) = rhoArc _ _ a (L (parEmb G₁ G₂ (G₂.tail a))) (x₂ a)
      rw [hemb _ (tt_tail_ne_t tt₂ a)]
      by_cases hh : G₂.head a = G₂.t
      · rw [hh, parEmb_t hst₂, hLt, h₂ (pos_of_arc_into_t tt₂ hst₂ hx₂ a hh ha), ← hh]; exact e
      · rw [hemb _ hh]; exact e

end ParGlue

end ThinFlowSP.Breakpoints


namespace ThinFlowSP.Breakpoints

set_option allowUnsafeReducibility true in
attribute [local reducible] Net.series Net.par

theorem exists_label_series {G₁ G₂ : Net} (tt₁ : IsTwoTerminalDAG G₁) (tt₂ : IsTwoTerminalDAG G₂)
    (hst₁ : G₁.s ≠ G₁.t) (hst₂ : G₂.s ≠ G₂.t) (Astar : Finset (G₁.A ⊕ G₂.A))
    (ν : G₁.A ⊕ G₂.A → ℝ) (hν : ∀ a, 0 < ν a)
    (ρ₁ : ℝ → G₁.V → ℝ) (ρ₂ : ℝ → G₂.V → ℝ)
    (hρ₁ : IsLabelFunction G₁ Astar.toLeft (fun a => ν (Sum.inl a)) ρ₁)
    (hρ₂ : IsLabelFunction G₂ Astar.toRight (fun a => ν (Sum.inr a)) ρ₂) :
    ∃ ρ : ℝ → (G₁.series G₂).V → ℝ, IsLabelFunction (G₁.series G₂) Astar ν ρ := by
  refine ⟨fun y => Sum.elim (ρ₁ y)
    (fun u : {u : G₂.V // u ≠ G₂.s} => ρ₁ y G₁.t * ρ₂ (y / ρ₁ y G₁.t) u.1), fun y hy => ?_⟩
  obtain ⟨hs1, x1, hx1, hl1⟩ := hρ₁ y hy
  set c := ρ₁ y G₁.t with hc
  have hc0 : 0 ≤ c := hl1.1 _
  obtain ⟨hs2, x2, hx2, hl2⟩ := hρ₂ (y / c) (div_nonneg hy hc0)
  have sf := staticFlow_smul' hc0 hx2
  have hval : c * (y / c) = y := by
    rcases hc0.lt_or_eq with hpos | hzero
    · field_simp
    · rcases hy.lt_or_eq with hy' | hy'
      · exact absurd (label_t_pos hst₁ (fun a => hν _) hy' hx1 hl1) (by rw [← hc, ← hzero]; exact lt_irrefl 0)
      · rw [← hy']; simp
  rw [hval] at sf
  have sl := labels_smul0 hc0 hl2
  obtain ⟨g1, g2⟩ := series_glue tt₁ tt₂ hst₁ hst₂ hx1 sf hl1 sl
    (by simp only [Pi.smul_apply, smul_eq_mul]; rw [hs2, mul_one])
  refine ⟨hs1, _, g1, ?_⟩
  convert g2 using 2
  funext u
  simp [hc]

theorem split_exists (f₁ f₂ : ℝ → ℝ) (h₁ : ContinuousOn f₁ (Set.Ici 0))
    (h₂ : ContinuousOn f₂ (Set.Ici 0)) (y : ℝ) (hy : 0 ≤ y) :
    ∃ y₁ y₂ lam : ℝ, 0 ≤ y₁ ∧ 0 ≤ y₂ ∧ y₁ + y₂ = y ∧ lam = min (f₁ y₁) (f₂ y₂) ∧
      (0 < y₁ → lam = f₁ y₁) ∧ (0 < y₂ → lam = f₂ y₂) := by
  by_cases c1 : f₂ y ≤ f₁ 0
  · exact ⟨0, y, f₂ y, le_rfl, hy, by ring, (min_eq_right c1).symm, fun h => absurd h (lt_irrefl 0),
      fun _ => rfl⟩
  by_cases c2 : f₁ y ≤ f₂ 0
  · exact ⟨y, 0, f₁ y, hy, le_rfl, by ring, (min_eq_left c2).symm, fun _ => rfl,
      fun h => absurd h (lt_irrefl 0)⟩
  push Not at c1 c2
  have hφ : ContinuousOn (fun z => f₁ z - f₂ (y - z)) (Set.Icc 0 y) := by
    apply ContinuousOn.sub
    · exact h₁.mono (fun z hz => hz.1)
    · apply h₂.comp (continuousOn_const.sub continuousOn_id)
      intro z hz
      show 0 ≤ y - z; linarith [hz.2]
  have h0 : (0:ℝ) ∈ Set.Icc ((fun z => f₁ z - f₂ (y - z)) 0) ((fun z => f₁ z - f₂ (y - z)) y) := by
    simp only [Set.mem_Icc, sub_zero, sub_self]
    constructor <;> linarith
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hy hφ h0
  simp only at hz0
  refine ⟨z, y - z, f₁ z, hz.1, by linarith [hz.2], by ring, ?_, fun _ => rfl, fun _ => by linarith⟩
  rw [show f₂ (y - z) = f₁ z by linarith, min_self]

theorem exists_label_par {G₁ G₂ : Net} (tt₁ : IsTwoTerminalDAG G₁) (tt₂ : IsTwoTerminalDAG G₂)
    (hst₁ : G₁.s ≠ G₁.t) (hst₂ : G₂.s ≠ G₂.t) (Astar : Finset (G₁.A ⊕ G₂.A))
    (ν : G₁.A ⊕ G₂.A → ℝ) (hν : ∀ a, 0 < ν a)
    (ρ₁ : ℝ → G₁.V → ℝ) (ρ₂ : ℝ → G₂.V → ℝ)
    (hρ₁ : IsLabelFunction G₁ Astar.toLeft (fun a => ν (Sum.inl a)) ρ₁)
    (hρ₂ : IsLabelFunction G₂ Astar.toRight (fun a => ν (Sum.inr a)) ρ₂) :
    ∃ ρ : ℝ → (G₁.par G₂).V → ℝ, IsLabelFunction (G₁.par G₂) Astar ν ρ := by
  have c₁ := label_continuousOn (tt_spg tt₁) hst₁ (fun a => hν _) hρ₁
  have c₂ := label_continuousOn (tt_spg tt₂) hst₂ (fun a => hν _) hρ₂
  have f₁c : ContinuousOn (fun z => ρ₁ z G₁.t) (Set.Ici 0) := (continuousOn_pi.mp c₁) G₁.t
  have f₂c : ContinuousOn (fun z => ρ₂ z G₂.t) (Set.Ici 0) := (continuousOn_pi.mp c₂) G₂.t
  choose! Y₁ Y₂ Λ hY using fun y (hy : 0 ≤ y) => split_exists _ _ f₁c f₂c y hy
  refine ⟨fun y => parLabels G₁ G₂ (ρ₁ (Y₁ y)) (ρ₂ (Y₂ y)) (Λ y), fun y hy => ?_⟩
  obtain ⟨hy1, hy2, hsum, hlam, hp1, hp2⟩ := hY y hy
  obtain ⟨hs1, x1, hx1, hl1⟩ := hρ₁ (Y₁ y) hy1
  obtain ⟨hs2, x2, hx2, hl2⟩ := hρ₂ (Y₂ y) hy2
  obtain ⟨g1, g2⟩ := par_glue tt₁ tt₂ hst₁ hst₂ hx1 hx2 hl1 hl2 (by rw [hs1, hs2]) hlam hp1 hp2
  rw [hsum] at g1
  refine ⟨?_, _, g1, g2⟩
  show parLabels G₁ G₂ (ρ₁ (Y₁ y)) (ρ₂ (Y₂ y)) (Λ y) (Sum.inl G₁.s) = 1
  simp [parLabels, hst₁, hs1]

end ThinFlowSP.Breakpoints


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


end ThinFlowSP.Breakpoints

namespace ThinFlowSP.Breakpoints

set_option allowUnsafeReducibility true in
attribute [local reducible] Net.series Net.par

theorem exists_label_arc (Astar : Finset Net.arc.A) (ν : Net.arc.A → ℝ) (hν : ∀ a, 0 < ν a) :
    ∃ ρ : ℝ → Net.arc.V → ℝ, IsLabelFunction Net.arc Astar ν ρ := by
  refine ⟨fun y => (fun b : Bool => if b then rhoArc Astar ν arcArc 1 y else 1 : Net.arc.V → ℝ),
    fun y hy => ⟨rfl, fun _ => y, ⟨fun _ => hy, ?_, ?_⟩, ?_, ?_, ?_⟩⟩
  · intro v hs ht
    exfalso
    cases v
    · exact hs rfl
    · exact ht rfl
  · have e1 : outflow Net.arc (fun _ => y) Net.arc.s = y := by
      unfold outflow
      exact Finset.sum_eq_single_of_mem arcArc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
        (fun b _ hb => (hb (arcArc_eq b)).elim)
    have e2 : inflow Net.arc (fun _ => y) Net.arc.s = 0 := by
      unfold inflow
      apply Finset.sum_eq_zero
      intro b hb
      have h := (Finset.mem_filter.mp hb).2
      exact Bool.noConfusion h
    rw [e1, e2, sub_zero]
  · intro b
    cases b
    · show (0:ℝ) ≤ 1; norm_num
    · show 0 ≤ rhoArc Astar ν arcArc 1 y
      exact le_trans (div_nonneg hy (hν _).le) (div_le_rhoArc _ _ _ _ _)
  · intro w hw
    cases w
    · exact absurd rfl hw
    · refine ⟨⟨arcArc, rfl, rfl⟩, ?_⟩
      rintro r ⟨a, -, rfl⟩
      rw [arcArc_eq a]
      exact le_rfl
  · intro a _
    rw [arcArc_eq a]
    rfl

theorem arc_bp_finite (Astar : Finset Net.arc.A) (ν : Net.arc.A → ℝ) (hν : ∀ a, 0 < ν a)
    (ρ : ℝ → Net.arc.V → ℝ) (hρ : IsLabelFunction Net.arc Astar ν ρ) :
    (breakpoints ρ).Finite := by
  have hν0 := hν arcArc
  have hsub : breakpoints ρ ⊆ {ν arcArc} := by
    intro x hx
    by_contra hne
    have hne : x ≠ ν arcArc := hne
    have hx0 := hx.1
    by_cases hA : arcArc ∈ Astar
    · refine arc_not_bp ρ x x (1 / ν arcArc) 0 hx0 (fun y hy => ?_) hx
      have hy0 : 0 ≤ y := by have := hy.1; linarith
      obtain ⟨h1, h2⟩ := arc_label Astar ν ρ hρ y hy0
      refine ⟨h1, ?_⟩
      rw [h2]; unfold rhoArc; rw [if_pos hA]; ring
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
  exact (Set.finite_singleton _).subset hsub

/-- Existence of label functions together with finiteness of breakpoints and the bound. -/
def SPProp (G : Net) : Prop :=
  (∀ (Astar : Finset G.A) (ν : G.A → ℝ), (∀ a, 0 < ν a) →
    ∃ ρ : ℝ → G.V → ℝ, IsLabelFunction G Astar ν ρ) ∧
  (∀ (Astar : Finset G.A) (ν : G.A → ℝ), (∀ a, 0 < ν a) →
    ∀ ρ : ℝ → G.V → ℝ, IsLabelFunction G Astar ν ρ →
      (breakpoints ρ).Finite ∧
      (breakpoints ρ).ncard + Astar.card + Fintype.card G.V ≤ 2 * Fintype.card G.A + 1)

theorem spprop_series (G₁ G₂ : Net) (g₁ : SPGood G₁) (g₂ : SPGood G₂)
    (b₁ : SPProp G₁) (b₂ : SPProp G₂) : SPProp (G₁.series G₂) := by
  refine ⟨fun Astar ν hν => ?_, fun Astar ν hν ρ hρ => ?_⟩
  · obtain ⟨ρ₁, hρ₁⟩ := b₁.1 Astar.toLeft (fun a => ν (Sum.inl a)) (fun a => hν _)
    obtain ⟨ρ₂, hρ₂⟩ := b₂.1 Astar.toRight (fun a => ν (Sum.inr a)) (fun a => hν _)
    exact exists_label_series g₁.twoTerminal g₂.twoTerminal g₁.st g₂.st Astar ν hν ρ₁ ρ₂ hρ₁ hρ₂
  · obtain ⟨ρ₁, hρ₁⟩ := b₁.1 Astar.toLeft (fun a => ν (Sum.inl a)) (fun a => hν _)
    obtain ⟨ρ₂, hρ₂⟩ := b₂.1 Astar.toRight (fun a => ν (Sum.inr a)) (fun a => hν _)
    have h29 := lemma_29 G₁ G₂ g₁.twoTerminal g₂.twoTerminal Astar ν hν ρ ρ₁ ρ₂ hρ hρ₁ hρ₂
    obtain ⟨f₁, i₁⟩ := b₁.2 Astar.toLeft _ (fun a => hν _) ρ₁ hρ₁
    obtain ⟨f₂, i₂⟩ := b₂.2 Astar.toRight _ (fun a => hν _) ρ₂ hρ₂
    rw [← f₁.cast_ncard_eq, ← f₂.cast_ncard_eq] at h29
    have f : (breakpoints ρ).Finite := by
      apply Set.finite_of_encard_le_coe (k := (breakpoints ρ₁).ncard + (breakpoints ρ₂).ncard)
      exact_mod_cast h29
    rw [← f.cast_ncard_eq] at h29
    norm_cast at h29
    refine ⟨f, ?_⟩
    have cS : Astar.toLeft.card + Astar.toRight.card = @Finset.card (G₁.series G₂).A Astar :=
      Finset.card_toLeft_add_card_toRight
    have cV := card_series_V G₁ G₂
    have cA := card_series_A G₁ G₂
    omega

theorem spprop_par (G₁ G₂ : Net) (g₁ : SPGood G₁) (g₂ : SPGood G₂)
    (b₁ : SPProp G₁) (b₂ : SPProp G₂) : SPProp (G₁.par G₂) := by
  refine ⟨fun Astar ν hν => ?_, fun Astar ν hν ρ hρ => ?_⟩
  · obtain ⟨ρ₁, hρ₁⟩ := b₁.1 Astar.toLeft (fun a => ν (Sum.inl a)) (fun a => hν _)
    obtain ⟨ρ₂, hρ₂⟩ := b₂.1 Astar.toRight (fun a => ν (Sum.inr a)) (fun a => hν _)
    exact exists_label_par g₁.twoTerminal g₂.twoTerminal g₁.st g₂.st Astar ν hν ρ₁ ρ₂ hρ₁ hρ₂
  · obtain ⟨ρ₁, hρ₁⟩ := b₁.1 Astar.toLeft (fun a => ν (Sum.inl a)) (fun a => hν _)
    obtain ⟨ρ₂, hρ₂⟩ := b₂.1 Astar.toRight (fun a => ν (Sum.inr a)) (fun a => hν _)
    have h30 := lemma_30 G₁ G₂ g₁.twoTerminal g₂.twoTerminal Astar ν hν ρ ρ₁ ρ₂ hρ hρ₁ hρ₂
    obtain ⟨f₁, i₁⟩ := b₁.2 Astar.toLeft _ (fun a => hν _) ρ₁ hρ₁
    obtain ⟨f₂, i₂⟩ := b₂.2 Astar.toRight _ (fun a => hν _) ρ₂ hρ₂
    rw [← f₁.cast_ncard_eq, ← f₂.cast_ncard_eq] at h30
    have f : (breakpoints ρ).Finite := by
      apply Set.finite_of_encard_le_coe (k := (breakpoints ρ₁).ncard + (breakpoints ρ₂).ncard + 1)
      exact_mod_cast h30
    rw [← f.cast_ncard_eq] at h30
    norm_cast at h30
    refine ⟨f, ?_⟩
    have cS : Astar.toLeft.card + Astar.toRight.card = @Finset.card (G₁.par G₂).A Astar :=
      Finset.card_toLeft_add_card_toRight
    have cV := card_par_V G₁ G₂ g₂.st
    have cA := card_par_A G₁ G₂
    omega

theorem spprop_toNet : ∀ T : SPTerm, SPProp T.toNet
  | .arc => ⟨exists_label_arc, fun Astar ν hν ρ hρ =>
      ⟨arc_bp_finite Astar ν hν ρ hρ, arc_bound Astar ν hν ρ hρ⟩⟩
  | .series T₁ T₂ => spprop_series _ _ (spgood_toNet T₁) (spgood_toNet T₂)
      (spprop_toNet T₁) (spprop_toNet T₂)
  | .par T₁ T₂ => spprop_par _ _ (spgood_toNet T₁) (spgood_toNet T₂)
      (spprop_toNet T₁) (spprop_toNet T₂)

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
  have P := spprop_toNet T
  refine ⟨P.1 Astar ν hν, fun ρ hρ => ?_⟩
  obtain ⟨hf, hb⟩ := P.2 Astar ν hν ρ hρ
  refine ⟨label_continuousOn g.spg g.st hν hρ, hf, ?_⟩
  omega

