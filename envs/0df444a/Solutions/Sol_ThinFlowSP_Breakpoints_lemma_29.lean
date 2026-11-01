-- Prove2me | solution 1 for ThinFlowSP.Breakpoints.lemma_29
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T08:45:15.406432+00:00
-- url     : https://prove2.me/submissions/084ec523-5c18-4d94-8159-bec635191543

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Model
import Theorems.Thm_ThinFlowSP_Breakpoints_corollary_15
import Theorems.Thm_ThinFlowSP_Breakpoints_lemma_18


namespace ThinFlowSP.Breakpoints

open Filter Topology

/-- `f` is affine (in every component, jointly) on a neighbourhood of `x`. -/
def AffNear {ι : Type} (f : ℝ → ι → ℝ) (x : ℝ) : Prop :=
  ∃ m c : ι → ℝ, ∀ᶠ y in 𝓝 x, ∀ i, f y i = m i * y + c i

theorem mem_breakpoints_iff {ι : Type} (f : ℝ → ι → ℝ) (x : ℝ) :
    x ∈ breakpoints f ↔ 0 < x ∧ ¬ AffNear f x := by
  unfold breakpoints AffNear
  simp only [Set.mem_ofPred_eq]
  apply and_congr_right
  intro _
  apply not_congr
  constructor
  · rintro ⟨ε, hε, m, c, h⟩
    refine ⟨m, c, Metric.eventually_nhds_iff.mpr ⟨ε, hε, fun y hy => h y ?_⟩⟩
    rw [Real.dist_eq, abs_lt] at hy
    constructor <;> linarith
  · rintro ⟨m, c, h⟩
    obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp h
    refine ⟨ε, hε, m, c, fun y hy => h ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]

/-- Abstract form of the series-composition breakpoint count (Lemma 29). -/
theorem bp_series_abstract {ι₁ ι₂ κ : Type} (f₁ : ℝ → ι₁ → ℝ) (f₂ : ℝ → ι₂ → ℝ)
    (F : ℝ → ι₁ ⊕ κ → ℝ) (g : κ → ι₂) (r : ι₁)
    (hpos : ∀ y, 0 < y → 0 < f₁ y r)
    (hmono : MonotoneOn (fun y => y / f₁ y r) (Set.Ioi 0))
    (hF₁ : ∀ y, 0 < y → ∀ i, F y (Sum.inl i) = f₁ y i)
    (hF₂ : ∀ y, 0 < y → ∀ j, F y (Sum.inr j) = f₁ y r * f₂ (y / f₁ y r) (g j)) :
    (breakpoints F).encard ≤ (breakpoints f₁).encard + (breakpoints f₂).encard := by
  set c : ℝ → ℝ := fun y => f₁ y r with hc
  set h : ℝ → ℝ := fun y => y / c y with hh
  set S := breakpoints F \ breakpoints f₁ with hS
  -- if `f₁` is affine near `x > 0`, `F` is affine near `x` as soon as `f₂` is affine near `h x`
  have key : ∀ x, 0 < x → AffNear f₁ x → AffNear f₂ (h x) → AffNear F x := by
    intro x hx ⟨m₁, c₁, h₁⟩ ⟨m₂, c₂, h₂⟩
    have hcx : c x = m₁ r * x + c₁ r := (h₁.self_of_nhds) r
    have hden : m₁ r * x + c₁ r ≠ 0 := by rw [← hcx]; exact (hpos x hx).ne'
    have hcont : ContinuousAt h x := by
      have : ContinuousAt (fun y => y / (m₁ r * y + c₁ r)) x :=
        continuousAt_id.div (by fun_prop) hden
      refine this.congr ?_
      filter_upwards [h₁] with y hy
      simp only [hh, hc, hy r]
    have h₂' := hcont.eventually h₂
    refine ⟨Sum.elim m₁ (fun j => m₂ (g j) + c₂ (g j) * m₁ r),
      Sum.elim c₁ (fun j => c₂ (g j) * c₁ r), ?_⟩
    filter_upwards [h₁, h₂', Ioi_mem_nhds hx] with y hy1 hy2 hy0
    have hy0' : (0:ℝ) < y := hy0
    rintro (i | j)
    · rw [hF₁ y hy0' i, hy1 i]; rfl
    · rw [hF₂ y hy0' j]
      have e2 := hy2 (g j)
      simp only [hh, hc] at e2
      rw [e2]
      have hcy : f₁ y r ≠ 0 := (hpos y hy0').ne'
      simp only [Sum.elim_inr]
      rw [hy1 r] at hcy ⊢
      field_simp
      ring
  have hS_bp : ∀ x ∈ S, h x ∈ breakpoints f₂ := by
    intro x ⟨hxF, hx1⟩
    rw [mem_breakpoints_iff] at hxF hx1 ⊢
    have hx0 := hxF.1
    have aff1 : AffNear f₁ x := by
      by_contra hn; exact hx1 ⟨hx0, hn⟩
    refine ⟨div_pos hx0 (hpos x hx0), fun haff => hxF.2 (key x hx0 aff1 haff)⟩
  -- injectivity of `h` on `S`
  have inj_aux : ∀ x x', x ∈ S → 0 < x' → x < x' → h x = h x' → False := by
    intro x x' ⟨hxF, hx1⟩ hx'0 hlt heq
    rw [mem_breakpoints_iff] at hxF hx1
    have hx0 := hxF.1
    obtain ⟨m₁, c₁, h₁⟩ : AffNear f₁ x := by
      by_contra hn; exact hx1 ⟨hx0, hn⟩
    set p := h x with hp
    have hp0 : 0 < p := div_pos hx0 (hpos x hx0)
    -- on `[x, x']`, `h = p` and hence `c y = y / p`
    have hconst : ∀ y, x ≤ y → y ≤ x' → c y = y / p := by
      intro y hxy hyx'
      have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
      have e1 : h x ≤ h y := hmono hx0 hy0 hxy
      have e2 : h y ≤ h x' := hmono hy0 hx'0 hyx'
      have hyp : h y = p := le_antisymm (heq ▸ e2) e1
      have hcy := hpos y hy0
      simp only [hh] at hyp
      rw [← hyp]; field_simp
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h₁
    set η := min (ε / 2) (x' - x) with hη
    have hη0 : 0 < η := lt_min (by linarith) (by linarith)
    have hηε : η < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hηx : η ≤ x' - x := min_le_right _ _
    have a1 : c x = m₁ r * x + c₁ r := hball (by simp [hε]) r
    have a2 : c (x + η) = m₁ r * (x + η) + c₁ r :=
      hball (by rw [Real.dist_eq]; simp [abs_of_pos hη0, hηε]) r
    rw [hconst x le_rfl hlt.le] at a1
    rw [hconst (x + η) (by linarith) (by linarith)] at a2
    have hm : m₁ r = 1 / p := by
      have h1 : m₁ r * η = η / p := by
        have : (x + η) / p - x / p = η / p := by ring
        linarith
      rw [eq_div_iff hp0.ne'] at h1
      have h3 : m₁ r * p * η = 1 * η := by linear_combination h1
      have h4 := mul_right_cancel₀ hη0.ne' h3
      exact eq_div_of_mul_eq hp0.ne' h4
    have hc0 : c₁ r = 0 := by
      rw [hm] at a1
      have : 1 / p * x = x / p := by ring
      linarith
    apply hxF.2
    refine ⟨Sum.elim m₁ (fun j => f₂ p (g j) / p), Sum.elim c₁ (fun _ => 0), ?_⟩
    filter_upwards [h₁, Ioi_mem_nhds hx0] with y hy1 hy0
    have hy0' : (0:ℝ) < y := hy0
    rintro (i | j)
    · rw [hF₁ y hy0' i, hy1 i]; rfl
    · rw [hF₂ y hy0' j]
      have hcy : f₁ y r = y / p := by
        have := hy1 r; rw [hm, hc0] at this; rw [this]; ring
      rw [hcy]
      have : y / (y / p) = p := by field_simp
      rw [this]
      simp only [Sum.elim_inr]
      ring
  have hinj : Set.InjOn h S := by
    intro x hx x' hx' heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact inj_aux x x' hx ((mem_breakpoints_iff F x').mp hx'.1).1 hlt heq
    · exact inj_aux x' x hx' ((mem_breakpoints_iff F x).mp hx.1).1 hgt heq.symm
  calc (breakpoints F).encard ≤ (breakpoints f₁ ∪ S).encard := by
        apply Set.encard_le_encard
        intro x hx
        by_cases h1 : x ∈ breakpoints f₁
        · exact Or.inl h1
        · exact Or.inr ⟨hx, h1⟩
    _ ≤ (breakpoints f₁).encard + S.encard := Set.encard_union_le _ _
    _ ≤ (breakpoints f₁).encard + (breakpoints f₂).encard := by
        have : S.encard ≤ (breakpoints f₂).encard := by
          rw [← hinj.encard_image]
          exact Set.encard_le_encard (by rintro _ ⟨x, hx, rfl⟩; exact hS_bp x hx)
        exact add_le_add_right this _

end ThinFlowSP.Breakpoints


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

set_option allowUnsafeReducibility true in
attribute [local reducible] Net.series Net.par

theorem lem29 (G₁ G₂ : Net) (h₁ : IsTwoTerminalDAG G₁) (h₂ : IsTwoTerminalDAG G₂)
    (Astar : Finset (G₁.A ⊕ G₂.A)) (ν : G₁.A ⊕ G₂.A → ℝ) (hν : ∀ a, 0 < ν a)
    (ρ : ℝ → (G₁.series G₂).V → ℝ) (ρ₁ : ℝ → G₁.V → ℝ) (ρ₂ : ℝ → G₂.V → ℝ)
    (hρ : IsLabelFunction (G₁.series G₂) Astar ν ρ)
    (hρ₁ : IsLabelFunction G₁ Astar.toLeft (fun a => ν (Sum.inl a)) ρ₁)
    (hρ₂ : IsLabelFunction G₂ Astar.toRight (fun a => ν (Sum.inr a)) ρ₂) :
    (breakpoints ρ).encard ≤ (breakpoints ρ₁).encard + (breakpoints ρ₂).encard := by
  have hst₁ := st_of_label h₁ hρ₁
  have hst₂ := st_of_label h₂ hρ₂
  have hpos : ∀ y, 0 < y → 0 < ρ₁ y G₁.t := by
    intro y hy
    obtain ⟨-, x1, hx1, hl1⟩ := hρ₁ y hy.le
    exact label_t_pos hst₁ (fun a => hν _) hy hx1 hl1
  have hanti := ((lemma_18 G₁ Astar.toLeft (fun a => ν (Sum.inl a)) (tt_spg h₁) hst₁
    (fun a => hν _)).2 ρ₁ hρ₁ G₁.t).2
  have hmono : MonotoneOn (fun y => y / ρ₁ y G₁.t) (Set.Ioi 0) := by
    intro a ha b hb hab
    have ha0 : (0:ℝ) < a := ha
    have hb0 : (0:ℝ) < b := hb
    have h1 : ρ₁ b G₁.t / b ≤ ρ₁ a G₁.t / a := hanti ha hb hab
    have hpa := div_pos (hpos a ha0) ha0
    have hpb := div_pos (hpos b hb0) hb0
    have := one_div_le_one_div_of_le hpb h1
    simp only [one_div, inv_div] at this
    exact this
  exact bp_series_abstract (ι₁ := G₁.V) (κ := {v : G₂.V // v ≠ G₂.s}) ρ₁ ρ₂ ρ Subtype.val G₁.t
    hpos hmono
    (fun y hy i => series_formula₁ h₁ h₂ hst₁ hst₂ Astar ν hν ρ ρ₁ hρ hρ₁ y hy.le i)
    (fun y hy j => series_formula₂ h₁ h₂ hst₁ hst₂ Astar ν hν ρ ρ₁ ρ₂ hρ hρ₁ hρ₂ y hy j)

end ThinFlowSP.Breakpoints

open ThinFlowSP.Breakpoints in
theorem solution (G₁ G₂ : Net) (h₁ : IsTwoTerminalDAG G₁) (h₂ : IsTwoTerminalDAG G₂)
    (Astar : Finset (G₁.A ⊕ G₂.A)) (ν : G₁.A ⊕ G₂.A → ℝ) (hν : ∀ a, 0 < ν a)
    (ρ : ℝ → (G₁.series G₂).V → ℝ) (ρ₁ : ℝ → G₁.V → ℝ) (ρ₂ : ℝ → G₂.V → ℝ)
    (hρ : IsLabelFunction (G₁.series G₂) Astar ν ρ)
    (hρ₁ : IsLabelFunction G₁ Astar.toLeft (fun a => ν (Sum.inl a)) ρ₁)
    (hρ₂ : IsLabelFunction G₂ Astar.toRight (fun a => ν (Sum.inr a)) ρ₂) :
    (breakpoints ρ).encard ≤ (breakpoints ρ₁).encard + (breakpoints ρ₂).encard :=
  lem29 G₁ G₂ h₁ h₂ Astar ν hν ρ ρ₁ ρ₂ hρ hρ₁ hρ₂
