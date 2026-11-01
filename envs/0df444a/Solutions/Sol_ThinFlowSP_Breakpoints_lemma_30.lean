-- Prove2me | solution 1 for ThinFlowSP.Breakpoints.lemma_30
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T09:15:12.557703+00:00
-- url     : https://prove2.me/submissions/d7a1173f-4bef-414e-acff-89a9290fe2c2

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

open Filter Topology

namespace ParAbs

set_option linter.unusedSectionVars false

variable {ι₁ ι₂ κ : Type} [DecidableEq ι₁] (ρ₁ : ℝ → ι₁ → ℝ) (ρ₂ : ℝ → ι₂ → ℝ)
  (t₁ : ι₁) (t₂ : ι₂) (g : κ → ι₂)

/-- glued labels of a split `(y₁, y₂)` -/
def Φ (y₁ y₂ : ℝ) : ι₁ ⊕ κ → ℝ :=
  Sum.elim (fun v => if v = t₁ then min (ρ₁ y₁ t₁) (ρ₂ y₂ t₂) else ρ₁ y₁ v) (fun u => ρ₂ y₂ (g u))

/-- valid splits -/
def Valid (y₁ y₂ : ℝ) : Prop :=
  0 ≤ y₁ ∧ 0 ≤ y₂ ∧ (0 < y₁ → ρ₁ y₁ t₁ ≤ ρ₂ y₂ t₂) ∧ (0 < y₂ → ρ₂ y₂ t₂ ≤ ρ₁ y₁ t₁)

/-- admissible coordinates at level `lam` for a non-decreasing `f` -/
def Zf (f : ℝ → ℝ) (lam : ℝ) : Set ℝ := {z | 0 ≤ z ∧ (0 < z → f z = lam) ∧ (z = 0 → lam ≤ f 0)}

/-- admissible first coordinates at level `lam` -/
abbrev Z₁ (lam : ℝ) : Set ℝ := Zf (fun z => ρ₁ z t₁) lam

/-- admissible second coordinates at level `lam` -/
abbrev Z₂ (lam : ℝ) : Set ℝ := Zf (fun z => ρ₂ z t₂) lam

variable {ρ₁ ρ₂ t₁ t₂}

theorem valid_Z {y₁ y₂ : ℝ} (h : Valid ρ₁ ρ₂ t₁ t₂ y₁ y₂) :
    y₁ ∈ Z₁ ρ₁ t₁ (min (ρ₁ y₁ t₁) (ρ₂ y₂ t₂)) ∧ y₂ ∈ Z₂ ρ₂ t₂ (min (ρ₁ y₁ t₁) (ρ₂ y₂ t₂)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨⟨h1, fun hp => (min_eq_left (h3 hp)).symm, fun hz => ?_⟩,
    ⟨h2, fun hp => (min_eq_right (h4 hp)).symm, fun hz => ?_⟩⟩
  · subst hz; exact min_le_left _ _
  · subst hz; exact min_le_right _ _

theorem Z_valid {lam z₁ z₂ : ℝ} (h₁ : z₁ ∈ Z₁ ρ₁ t₁ lam) (h₂ : z₂ ∈ Z₂ ρ₂ t₂ lam) :
    Valid ρ₁ ρ₂ t₁ t₂ z₁ z₂ ∧ (0 < z₁ + z₂ → min (ρ₁ z₁ t₁) (ρ₂ z₂ t₂) = lam) := by
  obtain ⟨a1, a2, a3⟩ := h₁
  obtain ⟨b1, b2, b3⟩ := h₂
  simp only at a2 a3 b2 b3
  have ge1 : lam ≤ ρ₁ z₁ t₁ := by
    rcases a1.lt_or_eq with h | h
    · exact (a2 h).ge
    · subst h; exact a3 rfl
  have ge2 : lam ≤ ρ₂ z₂ t₂ := by
    rcases b1.lt_or_eq with h | h
    · exact (b2 h).ge
    · subst h; exact b3 rfl
  refine ⟨⟨a1, b1, fun h => by rw [a2 h]; exact ge2, fun h => by rw [b2 h]; exact ge1⟩, fun hs => ?_⟩
  rcases a1.lt_or_eq with h | h
  · rw [a2 h]; exact min_eq_left ge2
  · have : 0 < z₂ := by rw [← h] at hs; linarith
    rw [b2 this]; exact min_eq_right ge1

theorem Zf_ordConnected {f : ℝ → ℝ} (lam : ℝ) (hm : MonotoneOn f (Set.Ici 0)) {a b z : ℝ}
    (ha : a ∈ Zf f lam) (hb : b ∈ Zf f lam) (haz : a ≤ z) (hzb : z ≤ b) : z ∈ Zf f lam := by
  have hz0 : 0 ≤ z := le_trans ha.1 haz
  refine ⟨hz0, fun hz => ?_, fun hz => ?_⟩
  · have hb0 : 0 < b := lt_of_lt_of_le hz hzb
    have e1 : f z ≤ f b := hm (Set.mem_Ici.mpr hz0) (Set.mem_Ici.mpr hb0.le) hzb
    have e2 : lam ≤ f a := by
      rcases ha.1.lt_or_eq with h | h
      · exact (ha.2.1 h).ge
      · rw [← h]; exact ha.2.2 h.symm
    have e3 : f a ≤ f z := hm (Set.mem_Ici.mpr ha.1) (Set.mem_Ici.mpr hz0) haz
    rw [hb.2.1 hb0] at e1
    linarith
  · subst hz
    have : a = 0 := le_antisymm haz ha.1
    subst this
    exact ha.2.2 rfl

/-- An extreme point `z > 0` of a non-degenerate level set of the component `t` is a
breakpoint. -/
theorem extreme_bp {ι : Type} (ρ : ℝ → ι → ℝ) (t : ι) (lam z w : ℝ)
    (hm : MonotoneOn (fun z => ρ z t) (Set.Ici 0)) (hz : z ∈ Zf (fun z => ρ z t) lam)
    (hz0 : 0 < z) (hw : w ∈ Zf (fun z => ρ z t) lam) (hwz : w ≠ z)
    (hext : (∀ u ∈ Zf (fun z => ρ z t) lam, u ≤ z) ∨ (∀ u ∈ Zf (fun z => ρ z t) lam, z ≤ u)) :
    z ∈ breakpoints ρ := by
  rw [mem_breakpoints_iff]
  refine ⟨hz0, ?_⟩
  rintro ⟨m, c, h⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h
  set δ := min ε z / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδε : δ < ε := by have := min_le_left ε z; linarith
  have hδz : δ < z := by have := min_le_right ε z; linarith
  have hfz : ρ z t = lam := hz.2.1 hz0
  have inball : ∀ y, |y - z| < ε → ρ y t = m t * y + c t := fun y hy =>
    hball (by rw [Real.dist_eq]; exact hy) t
  rcases hext with hmax | hmin
  · have hwz' : w < z := lt_of_le_of_ne (hmax w hw) hwz
    set p := max w (z - δ) with hp
    have hpz : p < z := max_lt hwz' (by linarith)
    have hp0 : 0 < p := lt_of_lt_of_le (by linarith) (le_max_right w (z - δ))
    have hpZ : p ∈ Zf (fun z => ρ z t) lam := Zf_ordConnected lam hm hw hz (le_max_left _ _) hpz.le
    have e1 : ρ p t = lam := hpZ.2.1 hp0
    have e2 := inball p (by rw [abs_lt]; constructor <;> linarith [le_max_right w (z - δ)])
    have e3 := inball z (by simp [hε])
    have hm0 : m t = 0 := by
      have : m t * (z - p) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (by linarith)
    have e4 := inball (z + δ) (by rw [abs_lt]; constructor <;> linarith)
    have hq : z + δ ∈ Zf (fun z => ρ z t) lam :=
      ⟨by linarith, fun _ => by
        simp only; rw [e4, hm0, zero_mul, zero_add]; rw [hm0, zero_mul, zero_add] at e2; linarith,
        fun h => by linarith⟩
    have := hmax _ hq
    linarith
  · have hwz' : z < w := lt_of_le_of_ne (hmin w hw) (Ne.symm hwz)
    set p := min w (z + δ) with hp
    have hpz : z < p := lt_min hwz' (by linarith)
    have hpZ : p ∈ Zf (fun z => ρ z t) lam := Zf_ordConnected lam hm hz hw hpz.le (min_le_left _ _)
    have e1 : ρ p t = lam := hpZ.2.1 (by linarith)
    have e2 := inball p (by rw [abs_lt]; constructor <;> linarith [min_le_right w (z + δ)])
    have e3 := inball z (by simp [hε])
    have hm0 : m t = 0 := by
      have : m t * (p - z) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (by linarith)
    have e4 := inball (z - δ) (by rw [abs_lt]; constructor <;> linarith)
    have hq : z - δ ∈ Zf (fun z => ρ z t) lam :=
      ⟨by linarith, fun _ => by
        simp only; rw [e4, hm0, zero_mul, zero_add]; rw [hm0, zero_mul, zero_add] at e2; linarith,
        fun h => by linarith⟩
    have := hmin _ hq
    linarith

/-- Affine reparametrisation: `ρ ∘ Y` is affine near `x` if `Y` is affine and either constant or
`ρ` is affine near `Y x`. -/
theorem aff_comp {ι : Type} (ρ : ℝ → ι → ℝ) (x a b : ℝ) (h : a = 0 ∨ AffNear ρ (a * x + b)) :
    ∃ m c : ι → ℝ, ∀ᶠ y in 𝓝 x, ∀ j, ρ (a * y + b) j = m j * y + c j := by
  rcases h with h | ⟨m, c, h⟩
  · subst h
    exact ⟨0, ρ b, Filter.Eventually.of_forall fun y j => by simp⟩
  · refine ⟨fun j => m j * a, fun j => m j * b + c j, ?_⟩
    have hc : Tendsto (fun y => a * y + b) (𝓝 x) (𝓝 (a * x + b)) :=
      ((continuous_const.mul continuous_id).add continuous_const).tendsto x
    filter_upwards [hc.eventually h] with y hy j
    rw [hy j]; ring

variable (F : ℝ → ι₁ ⊕ κ → ℝ)

/-- Key local lemma: an affine valid split around `x` along which both parts are affine. -/
theorem KL (hall : ∀ y₁ y₂, Valid ρ₁ ρ₂ t₁ t₂ y₁ y₂ → F (y₁ + y₂) = Φ ρ₁ ρ₂ t₁ t₂ g y₁ y₂)
    (x a₁ b₁ a₂ b₂ : ℝ) (hsum : ∀ y, (a₁ * y + b₁) + (a₂ * y + b₂) = y)
    (hval : ∀ᶠ y in 𝓝 x, Valid ρ₁ ρ₂ t₁ t₂ (a₁ * y + b₁) (a₂ * y + b₂))
    (h₁ : a₁ = 0 ∨ AffNear ρ₁ (a₁ * x + b₁)) (h₂ : a₂ = 0 ∨ AffNear ρ₂ (a₂ * x + b₂))
    (hpos : 0 < a₁ * x + b₁ ∨ 0 < a₂ * x + b₂) : AffNear F x := by
  obtain ⟨m₁, c₁, e₁⟩ := aff_comp ρ₁ x a₁ b₁ h₁
  obtain ⟨m₂, c₂, e₂⟩ := aff_comp ρ₂ x a₂ b₂ h₂
  have hc₁ : Tendsto (fun y => a₁ * y + b₁) (𝓝 x) (𝓝 (a₁ * x + b₁)) :=
    ((continuous_const.mul continuous_id).add continuous_const).tendsto x
  have hc₂ : Tendsto (fun y => a₂ * y + b₂) (𝓝 x) (𝓝 (a₂ * x + b₂)) :=
    ((continuous_const.mul continuous_id).add continuous_const).tendsto x
  rcases hpos with hp | hp
  · have ev : ∀ᶠ y in 𝓝 x, 0 < a₁ * y + b₁ := hc₁.eventually (Ioi_mem_nhds hp)
    refine ⟨Sum.elim (fun v => if v = t₁ then m₁ t₁ else m₁ v) (fun u => m₂ (g u)),
      Sum.elim (fun v => if v = t₁ then c₁ t₁ else c₁ v) (fun u => c₂ (g u)), ?_⟩
    filter_upwards [hval, e₁, e₂, ev] with y hv hy1 hy2 hp'
    have hF := hall _ _ hv
    rw [hsum] at hF
    rintro (v | u)
    · rw [hF]
      simp only [Φ, Sum.elim_inl]
      split_ifs with hvt
      · subst hvt; rw [min_eq_left (hv.2.2.1 hp'), hy1]
      · exact hy1 v
    · rw [hF]; simp only [Φ, Sum.elim_inr]; exact hy2 (g u)
  · have ev : ∀ᶠ y in 𝓝 x, 0 < a₂ * y + b₂ := hc₂.eventually (Ioi_mem_nhds hp)
    refine ⟨Sum.elim (fun v => if v = t₁ then m₂ t₂ else m₁ v) (fun u => m₂ (g u)),
      Sum.elim (fun v => if v = t₁ then c₂ t₂ else c₁ v) (fun u => c₂ (g u)), ?_⟩
    filter_upwards [hval, e₁, e₂, ev] with y hv hy1 hy2 hp'
    have hF := hall _ _ hv
    rw [hsum] at hF
    rintro (v | u)
    · rw [hF]
      simp only [Φ, Sum.elim_inl]
      split_ifs with hvt
      · subst hvt; rw [min_eq_right (hv.2.2.2 hp'), hy2]
      · exact hy1 v
    · rw [hF]; simp only [Φ, Sum.elim_inr]; exact hy2 (g u)

/-- If two different families of valid splits (first coordinate fixed, resp. second coordinate
fixed) exist around `x`, then `F` is constant near `x`. -/
theorem const_near (hall : ∀ y₁ y₂, Valid ρ₁ ρ₂ t₁ t₂ y₁ y₂ → F (y₁ + y₂) = Φ ρ₁ ρ₂ t₁ t₂ g y₁ y₂)
    (x x₁ x₂ : ℝ) (hx : x₁ + x₂ = x) (hpos : 0 < x)
    (hv₁ : ∀ᶠ y in 𝓝 x, Valid ρ₁ ρ₂ t₁ t₂ x₁ (y - x₁))
    (hv₂ : ∀ᶠ y in 𝓝 x, Valid ρ₁ ρ₂ t₁ t₂ (y - x₂) x₂) : AffNear F x := by
  refine ⟨0, F x, ?_⟩
  have hx₀ : Valid ρ₁ ρ₂ t₁ t₂ x₁ x₂ := by
    have := hv₁.self_of_nhds; rwa [show x - x₁ = x₂ by linarith] at this
  have hFx := hall _ _ hx₀
  rw [hx] at hFx
  filter_upwards [hv₁, hv₂] with y h1 h2
  have e1 := hall _ _ h1
  have e2 := hall _ _ h2
  rw [show x₁ + (y - x₁) = y by ring] at e1
  rw [show y - x₂ + x₂ = y by ring] at e2
  rintro (v | u)
  · simp only [Pi.zero_apply, zero_mul, zero_add]
    by_cases hvt : v = t₁
    · subst hvt
      rcases hx₀.1.lt_or_eq with hp | hp
      · rw [e1, hFx]
        simp only [Φ, Sum.elim_inl, if_true]
        rw [min_eq_left (h1.2.2.1 hp), min_eq_left (hx₀.2.2.1 hp)]
      · have hp2 : 0 < x₂ := by rw [← hp] at hx; linarith
        rw [e2, hFx]
        simp only [Φ, Sum.elim_inl, if_true]
        rw [min_eq_right (h2.2.2.2 hp2), min_eq_right (hx₀.2.2.2 hp2)]
    · rw [e1, hFx]; simp [Φ, hvt]
  · simp only [Pi.zero_apply, zero_mul, zero_add]
    rw [e2, hFx]; simp [Φ]

theorem aff_of_not_bp {ι : Type} (ρ : ℝ → ι → ℝ) {z : ℝ} (hz : 0 < z) (h : z ∉ breakpoints ρ) :
    AffNear ρ z := by
  rw [mem_breakpoints_iff] at h
  by_contra h'
  exact h ⟨hz, h'⟩

theorem not_aff_of_bp {ι : Type} (ρ : ℝ → ι → ℝ) {z : ℝ} (h : z ∈ breakpoints ρ) :
    ¬ AffNear ρ z := ((mem_breakpoints_iff ρ z).mp h).2

theorem extreme_or_interior {f : ℝ → ℝ} (lam : ℝ) (hm : MonotoneOn f (Set.Ici 0)) {z : ℝ}
    (hz : z ∈ Zf f lam) :
    (∀ u ∈ Zf f lam, u ≤ z) ∨ (∀ u ∈ Zf f lam, z ≤ u) ∨
      (∃ a ∈ Zf f lam, ∃ b ∈ Zf f lam, a < z ∧ z < b) := by
  by_contra h
  push Not at h
  obtain ⟨⟨u, hu, hzu⟩, ⟨u', hu', hu'z⟩, hno⟩ := h
  exact absurd (hno u' hu' u hu hu'z) (not_le.mpr hzu)

/-- Level case: first level set non-degenerate, second a single point `c₂`. -/
theorem caseS2 (hm₁ : MonotoneOn (fun z => ρ₁ z t₁) (Set.Ici 0))
    (hm₂ : MonotoneOn (fun z => ρ₂ z t₂) (Set.Ici 0))
    (hall : ∀ y₁ y₂, Valid ρ₁ ρ₂ t₁ t₂ y₁ y₂ → F (y₁ + y₂) = Φ ρ₁ ρ₂ t₁ t₂ g y₁ y₂)
    (lam c₂ : ℝ) (hZ₂ : ∀ z ∈ Z₂ ρ₂ t₂ lam, z = c₂)
    (hND : ∃ p ∈ Z₁ ρ₁ t₁ lam, ∃ q ∈ Z₁ ρ₁ t₁ lam, p < q)
    (x : ℝ) (hx : x ∈ breakpoints F) (x₁ x₂ : ℝ) (hs : x₁ + x₂ = x)
    (h₁ : x₁ ∈ Z₁ ρ₁ t₁ lam) (h₂ : x₂ ∈ Z₂ ρ₂ t₂ lam) :
    (x - c₂ ∈ breakpoints ρ₁ ∧ x - c₂ ∈ Z₁ ρ₁ t₁ lam) ∨
      (x - c₂ = 0 ∧ lam = max (ρ₁ 0 t₁) (ρ₂ 0 t₂)) := by
  have hx2 : x₂ = c₂ := hZ₂ x₂ h₂
  have hz : x - c₂ = x₁ := by rw [← hx2]; linarith
  rw [hz]
  have hxpos : 0 < x := ((mem_breakpoints_iff F x).mp hx).1
  obtain ⟨p, hp, q, hq, hpq⟩ := hND
  rcases h₁.1.lt_or_eq with hx1 | hx1
  · left
    refine ⟨?_, h₁⟩
    by_contra hnb
    have haff := aff_of_not_bp ρ₁ hx1 hnb
    rcases extreme_or_interior lam hm₁ h₁ with hext | hext | ⟨a, ha, b, hb, hax, hxb⟩
    · have hw : ∃ w ∈ Z₁ ρ₁ t₁ lam, w ≠ x₁ := by
        by_cases e : p = x₁
        · exact ⟨q, hq, by rw [← e]; exact hpq.ne'⟩
        · exact ⟨p, hp, e⟩
      obtain ⟨w, hw, hwx⟩ := hw
      exact hnb (extreme_bp ρ₁ t₁ lam x₁ w hm₁ h₁ hx1 hw hwx (Or.inl hext))
    · have hw : ∃ w ∈ Z₁ ρ₁ t₁ lam, w ≠ x₁ := by
        by_cases e : p = x₁
        · exact ⟨q, hq, by rw [← e]; exact hpq.ne'⟩
        · exact ⟨p, hp, e⟩
      obtain ⟨w, hw, hwx⟩ := hw
      exact hnb (extreme_bp ρ₁ t₁ lam x₁ w hm₁ h₁ hx1 hw hwx (Or.inr hext))
    · apply not_aff_of_bp F hx
      refine KL g F hall x 1 (-c₂) 0 c₂ (fun y => by ring) ?_ (Or.inr ?_) (Or.inl rfl) (Or.inl ?_)
      · have hev : ∀ᶠ y in 𝓝 x, y ∈ Set.Ioo (a + c₂) (b + c₂) :=
          Ioo_mem_nhds (by linarith) (by linarith)
        filter_upwards [hev] with y hy
        have hyZ : 1 * y + -c₂ ∈ Z₁ ρ₁ t₁ lam :=
          Zf_ordConnected lam hm₁ ha hb (by linarith [hy.1]) (by linarith [hy.2])
        have hc2 : 0 * y + c₂ ∈ Z₂ ρ₂ t₂ lam := by rw [zero_mul, zero_add, ← hx2]; exact h₂
        exact (Z_valid hyZ hc2).1
      · rw [show 1 * x + -c₂ = x₁ by linarith]; exact haff
      · linarith
  · right
    refine ⟨hx1.symm, ?_⟩
    have hq0 : 0 < q := lt_of_le_of_lt hp.1 hpq
    have e1 : ρ₁ q t₁ = lam := hq.2.1 hq0
    have e2 : lam ≤ ρ₁ 0 t₁ := h₁.2.2 hx1.symm
    have e3 : ρ₁ 0 t₁ ≤ ρ₁ q t₁ := hm₁ (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hq0.le) hq0.le
    have hx2pos : 0 < x₂ := by rw [← hx1] at hs; linarith
    have e4 : ρ₂ x₂ t₂ = lam := h₂.2.1 hx2pos
    have e5 : ρ₂ 0 t₂ ≤ ρ₂ x₂ t₂ := hm₂ (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx2pos.le) hx2pos.le
    rw [max_eq_left (by linarith)]
    linarith

/-- Level case: first level set a single point `c₁`, second non-degenerate. -/
theorem caseS3 (hm₁ : MonotoneOn (fun z => ρ₁ z t₁) (Set.Ici 0))
    (hm₂ : MonotoneOn (fun z => ρ₂ z t₂) (Set.Ici 0))
    (hall : ∀ y₁ y₂, Valid ρ₁ ρ₂ t₁ t₂ y₁ y₂ → F (y₁ + y₂) = Φ ρ₁ ρ₂ t₁ t₂ g y₁ y₂)
    (lam c₁ : ℝ) (hZ₁ : ∀ z ∈ Z₁ ρ₁ t₁ lam, z = c₁)
    (hND : ∃ p ∈ Z₂ ρ₂ t₂ lam, ∃ q ∈ Z₂ ρ₂ t₂ lam, p < q)
    (x : ℝ) (hx : x ∈ breakpoints F) (x₁ x₂ : ℝ) (hs : x₁ + x₂ = x)
    (h₁ : x₁ ∈ Z₁ ρ₁ t₁ lam) (h₂ : x₂ ∈ Z₂ ρ₂ t₂ lam) :
    (x - c₁ ∈ breakpoints ρ₂ ∧ x - c₁ ∈ Z₂ ρ₂ t₂ lam) ∨
      (x - c₁ = 0 ∧ lam = max (ρ₁ 0 t₁) (ρ₂ 0 t₂)) := by
  have hx1 : x₁ = c₁ := hZ₁ x₁ h₁
  have hz : x - c₁ = x₂ := by rw [← hx1]; linarith
  rw [hz]
  have hxpos : 0 < x := ((mem_breakpoints_iff F x).mp hx).1
  obtain ⟨p, hp, q, hq, hpq⟩ := hND
  rcases h₂.1.lt_or_eq with hx2 | hx2
  · left
    refine ⟨?_, h₂⟩
    by_contra hnb
    have haff := aff_of_not_bp ρ₂ hx2 hnb
    rcases extreme_or_interior lam hm₂ h₂ with hext | hext | ⟨a, ha, b, hb, hax, hxb⟩
    · have hw : ∃ w ∈ Z₂ ρ₂ t₂ lam, w ≠ x₂ := by
        by_cases e : p = x₂
        · exact ⟨q, hq, by rw [← e]; exact hpq.ne'⟩
        · exact ⟨p, hp, e⟩
      obtain ⟨w, hw, hwx⟩ := hw
      exact hnb (extreme_bp ρ₂ t₂ lam x₂ w hm₂ h₂ hx2 hw hwx (Or.inl hext))
    · have hw : ∃ w ∈ Z₂ ρ₂ t₂ lam, w ≠ x₂ := by
        by_cases e : p = x₂
        · exact ⟨q, hq, by rw [← e]; exact hpq.ne'⟩
        · exact ⟨p, hp, e⟩
      obtain ⟨w, hw, hwx⟩ := hw
      exact hnb (extreme_bp ρ₂ t₂ lam x₂ w hm₂ h₂ hx2 hw hwx (Or.inr hext))
    · apply not_aff_of_bp F hx
      refine KL g F hall x 0 c₁ 1 (-c₁) (fun y => by ring) ?_ (Or.inl rfl) (Or.inr ?_) (Or.inr ?_)
      · have hev : ∀ᶠ y in 𝓝 x, y ∈ Set.Ioo (a + c₁) (b + c₁) :=
          Ioo_mem_nhds (by linarith) (by linarith)
        filter_upwards [hev] with y hy
        have hyZ : 1 * y + -c₁ ∈ Z₂ ρ₂ t₂ lam :=
          Zf_ordConnected lam hm₂ ha hb (by linarith [hy.1]) (by linarith [hy.2])
        have hc1 : 0 * y + c₁ ∈ Z₁ ρ₁ t₁ lam := by rw [zero_mul, zero_add, ← hx1]; exact h₁
        exact (Z_valid hc1 hyZ).1
      · rw [show 1 * x + -c₁ = x₂ by linarith]; exact haff
      · linarith
  · right
    refine ⟨hx2.symm, ?_⟩
    have hq0 : 0 < q := lt_of_le_of_lt hp.1 hpq
    have e1 : ρ₂ q t₂ = lam := hq.2.1 hq0
    have e2 : lam ≤ ρ₂ 0 t₂ := h₂.2.2 hx2.symm
    have e3 : ρ₂ 0 t₂ ≤ ρ₂ q t₂ := hm₂ (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hq0.le) hq0.le
    have hx1pos : 0 < x₁ := by rw [← hx2] at hs; linarith
    have e4 : ρ₁ x₁ t₁ = lam := h₁.2.1 hx1pos
    have e5 : ρ₁ 0 t₁ ≤ ρ₁ x₁ t₁ := hm₁ (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx1pos.le) hx1pos.le
    rw [max_eq_right (by linarith)]
    linarith

/-- At an isolated point of a level set, an affine monotone component has positive slope. -/
theorem slope_pos {ι : Type} (ρ : ℝ → ι → ℝ) (t : ι) (lam c : ℝ)
    (hm : MonotoneOn (fun z => ρ z t) (Set.Ici 0)) (hc : c ∈ Zf (fun z => ρ z t) lam)
    (hc0 : 0 < c) (hdeg : ∀ z ∈ Zf (fun z => ρ z t) lam, z = c) (haff : AffNear ρ c) :
    ∃ m d : ι → ℝ, (∀ᶠ y in 𝓝 c, ∀ j, ρ y j = m j * y + d j) ∧ 0 < m t := by
  obtain ⟨m, d, h⟩ := haff
  refine ⟨m, d, h, ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h
  have e0 := hball (show dist c c < ε by simp [hε]) t
  have e1 := hball (show dist (c + ε / 2) c < ε by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith) t
  have hmono : ρ c t ≤ ρ (c + ε / 2) t :=
    hm (Set.mem_Ici.mpr hc0.le) (Set.mem_Ici.mpr (by linarith)) (by linarith)
  have hge : 0 ≤ m t := by
    by_contra hneg; push Not at hneg; nlinarith
  rcases hge.lt_or_eq with hp | hz
  · exact hp
  · exfalso
    have hq : c + ε / 2 ∈ Zf (fun z => ρ z t) lam := by
      refine ⟨by linarith, fun _ => ?_, fun h => by linarith⟩
      simp only
      rw [e1, ← hz, zero_mul, zero_add, ← hc.2.1 hc0]
      simp only; rw [e0, ← hz, zero_mul, zero_add]
    have := hdeg _ hq
    linarith

/-- Level case: both level sets are single points. -/
theorem caseS4 (hm₁ : MonotoneOn (fun z => ρ₁ z t₁) (Set.Ici 0))
    (hm₂ : MonotoneOn (fun z => ρ₂ z t₂) (Set.Ici 0))
    (hc₁ : ContinuousOn (fun z => ρ₁ z t₁) (Set.Ici 0))
    (hc₂ : ContinuousOn (fun z => ρ₂ z t₂) (Set.Ici 0))
    (hall : ∀ y₁ y₂, Valid ρ₁ ρ₂ t₁ t₂ y₁ y₂ → F (y₁ + y₂) = Φ ρ₁ ρ₂ t₁ t₂ g y₁ y₂)
    (lam c₁ c₂ : ℝ) (hZ₁ : ∀ z ∈ Z₁ ρ₁ t₁ lam, z = c₁) (hZ₂ : ∀ z ∈ Z₂ ρ₂ t₂ lam, z = c₂)
    (x : ℝ) (hx : x ∈ breakpoints F) (x₁ x₂ : ℝ) (hs : x₁ + x₂ = x)
    (h₁ : x₁ ∈ Z₁ ρ₁ t₁ lam) (h₂ : x₂ ∈ Z₂ ρ₂ t₂ lam) :
    c₁ ∈ breakpoints ρ₁ ∨ c₂ ∈ breakpoints ρ₂ ∨ lam = max (ρ₁ 0 t₁) (ρ₂ 0 t₂) := by
  have e1 : x₁ = c₁ := hZ₁ x₁ h₁
  have e2 : x₂ = c₂ := hZ₂ x₂ h₂
  subst e1 e2
  have hxpos : 0 < x := ((mem_breakpoints_iff F x).mp hx).1
  by_contra H
  push Not at H
  obtain ⟨H1, H2, H3⟩ := H
  apply not_aff_of_bp F hx
  rcases h₁.1.lt_or_eq with p1 | p1 <;> rcases h₂.1.lt_or_eq with p2 | p2
  · -- both positive
    obtain ⟨m₁, d₁, e₁, hα₁⟩ := slope_pos ρ₁ t₁ lam x₁ hm₁ h₁ p1 hZ₁ (aff_of_not_bp ρ₁ p1 H1)
    obtain ⟨m₂, d₂, e₂, hα₂⟩ := slope_pos ρ₂ t₂ lam x₂ hm₂ h₂ p2 hZ₂ (aff_of_not_bp ρ₂ p2 H2)
    set α₁ := m₁ t₁
    set α₂ := m₂ t₂
    have hS : 0 < α₁ + α₂ := by linarith
    set a₁ := α₂ / (α₁ + α₂) with ha₁
    set a₂ := α₁ / (α₁ + α₂) with ha₂
    have hsum_a : a₁ + a₂ = 1 := by rw [ha₁, ha₂]; field_simp; ring
    have hY₁ : a₁ * x + (x₁ - a₁ * x) = x₁ := by ring
    have hY₂ : a₂ * x + (x₂ - a₂ * x) = x₂ := by ring
    have hf₁ : ρ₁ x₁ t₁ = lam := h₁.2.1 p1
    have hf₂ : ρ₂ x₂ t₂ = lam := h₂.2.1 p2
    have ex₁ : ρ₁ x₁ t₁ = α₁ * x₁ + d₁ t₁ := e₁.self_of_nhds t₁
    have ex₂ : ρ₂ x₂ t₂ = α₂ * x₂ + d₂ t₂ := e₂.self_of_nhds t₂
    have tc₁ : Tendsto (fun y => a₁ * y + (x₁ - a₁ * x)) (𝓝 x) (𝓝 x₁) := by
      have := (show Continuous (fun y => a₁ * y + (x₁ - a₁ * x)) by fun_prop).tendsto x
      rwa [hY₁] at this
    have tc₂ : Tendsto (fun y => a₂ * y + (x₂ - a₂ * x)) (𝓝 x) (𝓝 x₂) := by
      have := (show Continuous (fun y => a₂ * y + (x₂ - a₂ * x)) by fun_prop).tendsto x
      rwa [hY₂] at this
    refine KL g F hall x a₁ (x₁ - a₁ * x) a₂ (x₂ - a₂ * x) (fun y => by linear_combination (y - x) * hsum_a + hs) ?_
      (Or.inr (by rw [hY₁]; exact aff_of_not_bp ρ₁ p1 H1))
      (Or.inr (by rw [hY₂]; exact aff_of_not_bp ρ₂ p2 H2)) (Or.inl (by rw [hY₁]; exact p1))
    filter_upwards [tc₁.eventually e₁, tc₂.eventually e₂, tc₁.eventually (Ioi_mem_nhds p1),
      tc₂.eventually (Ioi_mem_nhds p2)] with y hy1 hy2 hp1 hp2
    have q1 := hy1 t₁
    have q2 := hy2 t₂
    have key : ρ₁ (a₁ * y + (x₁ - a₁ * x)) t₁ = ρ₂ (a₂ * y + (x₂ - a₂ * x)) t₂ := by
      rw [q1, q2]
      have h1 : d₁ t₁ = lam - α₁ * x₁ := by linarith
      have h2 : d₂ t₂ = lam - α₂ * x₂ := by linarith
      rw [h1, h2, ha₁, ha₂]
      field_simp
      ring
    exact ⟨le_of_lt hp1, le_of_lt hp2, fun _ => key.le, fun _ => key.ge⟩
  · -- x₂ = 0
    subst p2
    have hx1 : x₁ = x := by linarith
    have hlam : lam ≤ ρ₂ 0 t₂ := h₂.2.2 rfl
    have hf₁ : ρ₁ x₁ t₁ = lam := h₁.2.1 p1
    rcases hlam.lt_or_eq with hlt | heq
    · have hcont : ContinuousAt (fun z => ρ₁ z t₁) x :=
        hc₁.continuousAt (Ici_mem_nhds hxpos)
      have ev : ∀ᶠ y in 𝓝 x, ρ₁ y t₁ < ρ₂ 0 t₂ :=
        hcont.eventually (Iio_mem_nhds (by show ρ₁ x t₁ < ρ₂ 0 t₂; rw [← hx1, hf₁]; exact hlt))
      refine KL g F hall x 1 0 0 0 (fun y => by ring) ?_ (Or.inr ?_) (Or.inl rfl) (Or.inl ?_)
      · filter_upwards [ev, Ioi_mem_nhds hxpos] with y hy hy0
        have hy0' : (0:ℝ) < y := hy0
        refine ⟨by linarith, by simp, fun _ => ?_, fun h => by simp at h⟩
        simp only [one_mul, add_zero, zero_mul]; exact hy.le
      · rw [one_mul, add_zero, ← hx1]; exact aff_of_not_bp ρ₁ p1 H1
      · linarith
    · exfalso
      apply H3
      have e3 : ρ₁ 0 t₁ ≤ ρ₁ x₁ t₁ := hm₁ (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr p1.le) p1.le
      rw [max_eq_right (by linarith)]
      exact heq
  · -- x₁ = 0
    subst p1
    have hx2 : x₂ = x := by linarith
    have hlam : lam ≤ ρ₁ 0 t₁ := h₁.2.2 rfl
    have hf₂ : ρ₂ x₂ t₂ = lam := h₂.2.1 p2
    rcases hlam.lt_or_eq with hlt | heq
    · have hcont : ContinuousAt (fun z => ρ₂ z t₂) x :=
        hc₂.continuousAt (Ici_mem_nhds hxpos)
      have ev : ∀ᶠ y in 𝓝 x, ρ₂ y t₂ < ρ₁ 0 t₁ :=
        hcont.eventually (Iio_mem_nhds (by show ρ₂ x t₂ < ρ₁ 0 t₁; rw [← hx2, hf₂]; exact hlt))
      refine KL g F hall x 0 0 1 0 (fun y => by ring) ?_ (Or.inl rfl) (Or.inr ?_) (Or.inr ?_)
      · filter_upwards [ev, Ioi_mem_nhds hxpos] with y hy hy0
        have hy0' : (0:ℝ) < y := hy0
        refine ⟨by simp, by linarith, fun h => by simp at h, fun _ => ?_⟩
        simp only [one_mul, add_zero, zero_mul]; exact hy.le
      · rw [one_mul, add_zero, ← hx2]; exact aff_of_not_bp ρ₂ p2 H2
      · linarith
    · exfalso
      apply H3
      have e3 : ρ₂ 0 t₂ ≤ ρ₂ x₂ t₂ := hm₂ (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr p2.le) p2.le
      rw [max_eq_left (by linarith)]
      exact heq
  · exfalso; rw [← p1, ← p2] at hs; linarith

theorem min_mem_of {S : Set ℝ} {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) : min a b ∈ S := by
  rcases min_choice a b with h | h <;> rw [h] <;> assumption

theorem max_mem_of {S : Set ℝ} {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) : max a b ∈ S := by
  rcases max_choice a b with h | h <;> rw [h] <;> assumption

/-- Level case, both level sets non-degenerate: a breakpoint is extreme in `Z₁ + Z₂`. -/
theorem caseS1_extreme (hm₁ : MonotoneOn (fun z => ρ₁ z t₁) (Set.Ici 0))
    (hm₂ : MonotoneOn (fun z => ρ₂ z t₂) (Set.Ici 0))
    (hall : ∀ y₁ y₂, Valid ρ₁ ρ₂ t₁ t₂ y₁ y₂ → F (y₁ + y₂) = Φ ρ₁ ρ₂ t₁ t₂ g y₁ y₂)
    (lam : ℝ) (hND₁ : ∃ p ∈ Z₁ ρ₁ t₁ lam, ∃ q ∈ Z₁ ρ₁ t₁ lam, p < q)
    (hND₂ : ∃ p ∈ Z₂ ρ₂ t₂ lam, ∃ q ∈ Z₂ ρ₂ t₂ lam, p < q)
    (x : ℝ) (hx : x ∈ breakpoints F) :
    (∀ a₁ ∈ Z₁ ρ₁ t₁ lam, ∀ a₂ ∈ Z₂ ρ₂ t₂ lam, a₁ + a₂ ≤ x) ∨
      (∀ a₁ ∈ Z₁ ρ₁ t₁ lam, ∀ a₂ ∈ Z₂ ρ₂ t₂ lam, x ≤ a₁ + a₂) := by
  have hxpos : 0 < x := ((mem_breakpoints_iff F x).mp hx).1
  by_contra H
  push Not at H
  obtain ⟨⟨a₁, ha₁, a₂, ha₂, hA⟩, ⟨b₁, hb₁, b₂, hb₂, hB⟩⟩ := H
  obtain ⟨p₁, hp₁, q₁, hq₁, hpq₁⟩ := hND₁
  obtain ⟨p₂, hp₂, q₂, hq₂, hpq₂⟩ := hND₂
  set l₁ := min (min a₁ b₁) p₁
  set h₁ := max (max a₁ b₁) q₁
  set l₂ := min (min a₂ b₂) p₂
  set h₂ := max (max a₂ b₂) q₂
  have hl₁ : l₁ ∈ Z₁ ρ₁ t₁ lam := min_mem_of (min_mem_of ha₁ hb₁) hp₁
  have hh₁ : h₁ ∈ Z₁ ρ₁ t₁ lam := max_mem_of (max_mem_of ha₁ hb₁) hq₁
  have hl₂ : l₂ ∈ Z₂ ρ₂ t₂ lam := min_mem_of (min_mem_of ha₂ hb₂) hp₂
  have hh₂ : h₂ ∈ Z₂ ρ₂ t₂ lam := max_mem_of (max_mem_of ha₂ hb₂) hq₂
  have i1 : l₁ < h₁ := lt_of_le_of_lt (min_le_right _ _) (lt_of_lt_of_le hpq₁ (le_max_right _ _))
  have i2 : l₂ < h₂ := lt_of_le_of_lt (min_le_right _ _) (lt_of_lt_of_le hpq₂ (le_max_right _ _))
  have i3 : l₁ + l₂ < x := by
    have : l₁ ≤ b₁ := le_trans (min_le_left _ _) (min_le_right _ _)
    have : l₂ ≤ b₂ := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have i4 : x < h₁ + h₂ := by
    have : a₁ ≤ h₁ := le_trans (le_max_left _ _) (le_max_left _ _)
    have : a₂ ≤ h₂ := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  set lo := max l₁ (x - h₂) with hlo
  set hi := min h₁ (x - l₂) with hhi
  have hlohi : lo < hi := by
    apply max_lt <;> apply lt_min <;> linarith
  set x₁ := (lo + hi) / 2 with hx₁
  have j1 : l₁ < x₁ := by have := le_max_left l₁ (x - h₂); linarith
  have j2 : x₁ < h₁ := by have := min_le_left h₁ (x - l₂); linarith
  have j3 : l₂ < x - x₁ := by have := min_le_right h₁ (x - l₂); linarith
  have j4 : x - x₁ < h₂ := by have := le_max_right l₁ (x - h₂); linarith
  apply not_aff_of_bp F hx
  refine const_near g F hall x x₁ (x - x₁) (by ring) hxpos ?_ ?_
  · have hev : ∀ᶠ y in 𝓝 x, y ∈ Set.Ioo (x₁ + l₂) (x₁ + h₂) :=
      Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hev] with y hy
    have z1 : x₁ ∈ Z₁ ρ₁ t₁ lam := Zf_ordConnected lam hm₁ hl₁ hh₁ j1.le j2.le
    have z2 : y - x₁ ∈ Z₂ ρ₂ t₂ lam :=
      Zf_ordConnected lam hm₂ hl₂ hh₂ (by linarith [hy.1]) (by linarith [hy.2])
    exact (Z_valid z1 z2).1
  · have hev : ∀ᶠ y in 𝓝 x, y ∈ Set.Ioo (x - x₁ + l₁) (x - x₁ + h₁) :=
      Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hev] with y hy
    have z1 : y - (x - x₁) ∈ Z₁ ρ₁ t₁ lam :=
      Zf_ordConnected lam hm₁ hl₁ hh₁ (by linarith [hy.1]) (by linarith [hy.2])
    have z2 : x - x₁ ∈ Z₂ ρ₂ t₂ lam := Zf_ordConnected lam hm₂ hl₂ hh₂ j3.le j4.le
    exact (Z_valid z1 z2).1

/-- A maximal point of `Z₁ + Z₂` (both non-degenerate) yields breakpoints of both parts. -/
theorem caseS1_max (hm₁ : MonotoneOn (fun z => ρ₁ z t₁) (Set.Ici 0))
    (hm₂ : MonotoneOn (fun z => ρ₂ z t₂) (Set.Ici 0))
    (lam : ℝ) (hND₁ : ∃ p ∈ Z₁ ρ₁ t₁ lam, ∃ q ∈ Z₁ ρ₁ t₁ lam, p < q)
    (hND₂ : ∃ p ∈ Z₂ ρ₂ t₂ lam, ∃ q ∈ Z₂ ρ₂ t₂ lam, p < q)
    (x x₁ x₂ : ℝ) (hs : x₁ + x₂ = x) (h₁ : x₁ ∈ Z₁ ρ₁ t₁ lam) (h₂ : x₂ ∈ Z₂ ρ₂ t₂ lam)
    (hmax : ∀ a₁ ∈ Z₁ ρ₁ t₁ lam, ∀ a₂ ∈ Z₂ ρ₂ t₂ lam, a₁ + a₂ ≤ x) :
    x₁ ∈ breakpoints ρ₁ ∧ x₂ ∈ breakpoints ρ₂ := by
  obtain ⟨p₁, hp₁, q₁, hq₁, hpq₁⟩ := hND₁
  obtain ⟨p₂, hp₂, q₂, hq₂, hpq₂⟩ := hND₂
  have m1 : ∀ u ∈ Z₁ ρ₁ t₁ lam, u ≤ x₁ := fun u hu => by have := hmax u hu x₂ h₂; linarith
  have m2 : ∀ u ∈ Z₂ ρ₂ t₂ lam, u ≤ x₂ := fun u hu => by have := hmax x₁ h₁ u hu; linarith
  have q1 := m1 q₁ hq₁
  have q2 := m2 q₂ hq₂
  have pos1 : 0 < x₁ := lt_of_lt_of_le (lt_of_le_of_lt hp₁.1 hpq₁) q1
  have pos2 : 0 < x₂ := lt_of_lt_of_le (lt_of_le_of_lt hp₂.1 hpq₂) q2
  exact ⟨extreme_bp ρ₁ t₁ lam x₁ p₁ hm₁ h₁ pos1 hp₁ (by linarith) (Or.inl m1),
    extreme_bp ρ₂ t₂ lam x₂ p₂ hm₂ h₂ pos2 hp₂ (by linarith) (Or.inl m2)⟩

/-- A minimal point of `Z₁ + Z₂` (both non-degenerate) at positive height yields a breakpoint
of one part. -/
theorem caseS1_min (hm₁ : MonotoneOn (fun z => ρ₁ z t₁) (Set.Ici 0))
    (hm₂ : MonotoneOn (fun z => ρ₂ z t₂) (Set.Ici 0))
    (lam : ℝ) (hND₁ : ∃ p ∈ Z₁ ρ₁ t₁ lam, ∃ q ∈ Z₁ ρ₁ t₁ lam, p < q)
    (hND₂ : ∃ p ∈ Z₂ ρ₂ t₂ lam, ∃ q ∈ Z₂ ρ₂ t₂ lam, p < q)
    (x x₁ x₂ : ℝ) (hx : 0 < x) (hs : x₁ + x₂ = x) (h₁ : x₁ ∈ Z₁ ρ₁ t₁ lam)
    (h₂ : x₂ ∈ Z₂ ρ₂ t₂ lam)
    (hmin : ∀ a₁ ∈ Z₁ ρ₁ t₁ lam, ∀ a₂ ∈ Z₂ ρ₂ t₂ lam, x ≤ a₁ + a₂) :
    (x₁ ∈ breakpoints ρ₁ ∧ x₁ ∈ Z₁ ρ₁ t₁ lam) ∨ (x₂ ∈ breakpoints ρ₂ ∧ x₂ ∈ Z₂ ρ₂ t₂ lam) := by
  obtain ⟨p₁, hp₁, q₁, hq₁, hpq₁⟩ := hND₁
  obtain ⟨p₂, hp₂, q₂, hq₂, hpq₂⟩ := hND₂
  have m1 : ∀ u ∈ Z₁ ρ₁ t₁ lam, x₁ ≤ u := fun u hu => by have := hmin u hu x₂ h₂; linarith
  have m2 : ∀ u ∈ Z₂ ρ₂ t₂ lam, x₂ ≤ u := fun u hu => by have := hmin x₁ h₁ u hu; linarith
  have q1 := m1 p₁ hp₁
  have q2 := m2 p₂ hp₂
  rcases h₁.1.lt_or_eq with pos1 | z1
  · exact Or.inl ⟨extreme_bp ρ₁ t₁ lam x₁ q₁ hm₁ h₁ pos1 hq₁ (by linarith) (Or.inr m1), h₁⟩
  · have pos2 : 0 < x₂ := by rw [← z1] at hs; linarith
    exact Or.inr ⟨extreme_bp ρ₂ t₂ lam x₂ q₂ hm₂ h₂ pos2 hq₂ (by linarith) (Or.inr m2), h₂⟩

open Classical in
/-- Per-level bound. -/
theorem level_bound (hm₁ : MonotoneOn (fun z => ρ₁ z t₁) (Set.Ici 0))
    (hm₂ : MonotoneOn (fun z => ρ₂ z t₂) (Set.Ici 0))
    (hc₁ : ContinuousOn (fun z => ρ₁ z t₁) (Set.Ici 0))
    (hc₂ : ContinuousOn (fun z => ρ₂ z t₂) (Set.Ici 0))
    (hall : ∀ y₁ y₂, Valid ρ₁ ρ₂ t₁ t₂ y₁ y₂ → F (y₁ + y₂) = Φ ρ₁ ρ₂ t₁ t₂ g y₁ y₂)
    (lam : ℝ) (B₁ B₂ : Finset ℝ) (hB₁ : ∀ b ∈ breakpoints ρ₁, b ∈ B₁)
    (hB₂ : ∀ b ∈ breakpoints ρ₂, b ∈ B₂) (P : Finset ℝ)
    (hP : ∀ x ∈ P, x ∈ breakpoints F ∧
      ∃ x₁ x₂, x₁ + x₂ = x ∧ x₁ ∈ Z₁ ρ₁ t₁ lam ∧ x₂ ∈ Z₂ ρ₂ t₂ lam) :
    P.card ≤ (B₁.filter (· ∈ Z₁ ρ₁ t₁ lam)).card + (B₂.filter (· ∈ Z₂ ρ₂ t₂ lam)).card +
      (if lam = max (ρ₁ 0 t₁) (ρ₂ 0 t₂) then 1 else 0) := by
  rcases P.eq_empty_or_nonempty with he | ⟨x0, hx0⟩
  · simp [he]
  obtain ⟨hx0b, z1, z2, hz, hz1, hz2⟩ := hP x0 hx0
  set M := max (ρ₁ 0 t₁) (ρ₂ 0 t₂)
  set C₁ := B₁.filter (· ∈ Z₁ ρ₁ t₁ lam)
  set C₂ := B₂.filter (· ∈ Z₂ ρ₂ t₂ lam)
  have mC₁ : ∀ b, b ∈ breakpoints ρ₁ → b ∈ Z₁ ρ₁ t₁ lam → b ∈ C₁ := fun b h1 h2 =>
    Finset.mem_filter.mpr ⟨hB₁ b h1, h2⟩
  have mC₂ : ∀ b, b ∈ breakpoints ρ₂ → b ∈ Z₂ ρ₂ t₂ lam → b ∈ C₂ := fun b h1 h2 =>
    Finset.mem_filter.mpr ⟨hB₂ b h1, h2⟩
  have deg₁ : ¬ (∃ p ∈ Z₁ ρ₁ t₁ lam, ∃ q ∈ Z₁ ρ₁ t₁ lam, p < q) →
      ∀ z ∈ Z₁ ρ₁ t₁ lam, z = z1 := by
    intro hn z hz'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hn ⟨z, hz', z1, hz1, h⟩
    · exact hn ⟨z1, hz1, z, hz', h⟩
  have deg₂ : ¬ (∃ p ∈ Z₂ ρ₂ t₂ lam, ∃ q ∈ Z₂ ρ₂ t₂ lam, p < q) →
      ∀ z ∈ Z₂ ρ₂ t₂ lam, z = z2 := by
    intro hn z hz'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hn ⟨z, hz', z2, hz2, h⟩
    · exact hn ⟨z2, hz2, z, hz', h⟩
  by_cases ND₁ : ∃ p ∈ Z₁ ρ₁ t₁ lam, ∃ q ∈ Z₁ ρ₁ t₁ lam, p < q <;>
    by_cases ND₂ : ∃ p ∈ Z₂ ρ₂ t₂ lam, ∃ q ∈ Z₂ ρ₂ t₂ lam, p < q
  · -- both non-degenerate
    have hext := fun x hx => caseS1_extreme g F hm₁ hm₂ hall lam ND₁ ND₂ x (hP x hx).1
    have minle : (P.filter fun x => ∀ a₁ ∈ Z₁ ρ₁ t₁ lam, ∀ a₂ ∈ Z₂ ρ₂ t₂ lam, x ≤ a₁ + a₂).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      obtain ⟨haP, ha'⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbP, hb'⟩ := Finset.mem_filter.mp hb
      obtain ⟨-, a₁, a₂, hsa, ha₁, ha₂⟩ := hP a haP
      obtain ⟨-, b₁, b₂, hsb, hb₁, hb₂⟩ := hP b hbP
      have := ha' b₁ hb₁ b₂ hb₂
      have := hb' a₁ ha₁ a₂ ha₂
      linarith
    by_cases hmx : ∃ xm ∈ P, ∀ a₁ ∈ Z₁ ρ₁ t₁ lam, ∀ a₂ ∈ Z₂ ρ₂ t₂ lam, a₁ + a₂ ≤ xm
    · obtain ⟨xm, hxm, hmax⟩ := hmx
      obtain ⟨-, m₁, m₂, hsm, hm₁', hm₂'⟩ := hP xm hxm
      obtain ⟨b1, b2⟩ := caseS1_max hm₁ hm₂ lam ND₁ ND₂ xm m₁ m₂ hsm hm₁' hm₂' hmax
      have c1 : 1 ≤ C₁.card := Finset.card_pos.mpr ⟨m₁, mC₁ m₁ b1 hm₁'⟩
      have c2 : 1 ≤ C₂.card := Finset.card_pos.mpr ⟨m₂, mC₂ m₂ b2 hm₂'⟩
      have hsub : P ⊆ insert xm (P.filter fun x => ∀ a₁ ∈ Z₁ ρ₁ t₁ lam, ∀ a₂ ∈ Z₂ ρ₂ t₂ lam,
          x ≤ a₁ + a₂) := by
        intro x hx
        rcases hext x hx with h | h
        · have : x = xm := by
            obtain ⟨-, a₁, a₂, hsa, ha₁, ha₂⟩ := hP x hx
            have := h m₁ hm₁' m₂ hm₂'
            have := hmax a₁ ha₁ a₂ ha₂
            linarith
          rw [this]; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hx, h⟩)
      have := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      split_ifs <;> omega
    · push Not at hmx
      have hsub : P ⊆ P.filter fun x => ∀ a₁ ∈ Z₁ ρ₁ t₁ lam, ∀ a₂ ∈ Z₂ ρ₂ t₂ lam, x ≤ a₁ + a₂ := by
        intro x hx
        rcases hext x hx with h | h
        · exfalso
          obtain ⟨a₁, ha₁, a₂, ha₂, hlt⟩ := hmx x hx
          exact absurd (h a₁ ha₁ a₂ ha₂) (not_le.mpr hlt)
        · exact Finset.mem_filter.mpr ⟨hx, h⟩
      have hP1 := (Finset.card_le_card hsub).trans minle
      have hpos : 0 < x0 := ((mem_breakpoints_iff F x0).mp hx0b).1
      have h0 : x0 ∈ P.filter fun x => ∀ a₁ ∈ Z₁ ρ₁ t₁ lam, ∀ a₂ ∈ Z₂ ρ₂ t₂ lam, x ≤ a₁ + a₂ :=
        hsub hx0
      rcases caseS1_min hm₁ hm₂ lam ND₁ ND₂ x0 z1 z2 hpos hz hz1 hz2
        (Finset.mem_filter.mp h0).2 with ⟨b, bz⟩ | ⟨b, bz⟩
      · have : 1 ≤ C₁.card := Finset.card_pos.mpr ⟨z1, mC₁ z1 b bz⟩
        split_ifs <;> omega
      · have : 1 ≤ C₂.card := Finset.card_pos.mpr ⟨z2, mC₂ z2 b bz⟩
        split_ifs <;> omega
  · -- Z₂ a single point
    have hZ₂ := deg₂ ND₂
    have himg : P.image (fun x => x - z2) ⊆ C₁ ∪ (if lam = M then {0} else ∅) := by
      intro z hzimg
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hzimg
      obtain ⟨hxb, x₁, x₂, hs, h₁, h₂⟩ := hP x hx
      rcases caseS2 g F hm₁ hm₂ hall lam z2 hZ₂ ND₁ x hxb x₁ x₂ hs h₁ h₂ with ⟨b, bz⟩ | ⟨h0, hl⟩
      · exact Finset.mem_union_left _ (mC₁ _ b bz)
      · apply Finset.mem_union_right
        rw [if_pos hl, h0]; exact Finset.mem_singleton_self _
    have hinj : P.card = (P.image (fun x => x - z2)).card :=
      (Finset.card_image_of_injective _ (sub_left_injective)).symm
    have := (Finset.card_le_card himg).trans (Finset.card_union_le _ _)
    split_ifs at this ⊢ <;> simp at this <;> omega
  · -- Z₁ a single point
    have hZ₁ := deg₁ ND₁
    have himg : P.image (fun x => x - z1) ⊆ C₂ ∪ (if lam = M then {0} else ∅) := by
      intro z hzimg
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hzimg
      obtain ⟨hxb, x₁, x₂, hs, h₁, h₂⟩ := hP x hx
      rcases caseS3 g F hm₁ hm₂ hall lam z1 hZ₁ ND₂ x hxb x₁ x₂ hs h₁ h₂ with ⟨b, bz⟩ | ⟨h0, hl⟩
      · exact Finset.mem_union_left _ (mC₂ _ b bz)
      · apply Finset.mem_union_right
        rw [if_pos hl, h0]; exact Finset.mem_singleton_self _
    have hinj : P.card = (P.image (fun x => x - z1)).card :=
      (Finset.card_image_of_injective _ (sub_left_injective)).symm
    have := (Finset.card_le_card himg).trans (Finset.card_union_le _ _)
    split_ifs at this ⊢ <;> simp at this <;> omega
  · -- both single points
    have hZ₁ := deg₁ ND₁
    have hZ₂ := deg₂ ND₂
    have hsub : P ⊆ {z1 + z2} := by
      intro x hx
      obtain ⟨-, x₁, x₂, hs, h₁, h₂⟩ := hP x hx
      rw [hZ₁ x₁ h₁, hZ₂ x₂ h₂] at hs
      rw [← hs]; exact Finset.mem_singleton_self _
    have hP1 : P.card ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
    rcases caseS4 g F hm₁ hm₂ hc₁ hc₂ hall lam z1 z2 hZ₁ hZ₂ x0 hx0b z1 z2 hz hz1 hz2 with
      h | h | h
    · have : 1 ≤ C₁.card := Finset.card_pos.mpr ⟨z1, mC₁ z1 h hz1⟩
      split_ifs <;> omega
    · have : 1 ≤ C₂.card := Finset.card_pos.mpr ⟨z2, mC₂ z2 h hz2⟩
      split_ifs <;> omega
    · rw [if_pos h]; omega

open Classical in
/-- Abstract form of the parallel-composition breakpoint count (Lemma 30). -/
theorem abstract30 (hm₁ : MonotoneOn (fun z => ρ₁ z t₁) (Set.Ici 0))
    (hm₂ : MonotoneOn (fun z => ρ₂ z t₂) (Set.Ici 0))
    (hc₁ : ContinuousOn (fun z => ρ₁ z t₁) (Set.Ici 0))
    (hc₂ : ContinuousOn (fun z => ρ₂ z t₂) (Set.Ici 0))
    (hall : ∀ y₁ y₂, Valid ρ₁ ρ₂ t₁ t₂ y₁ y₂ → F (y₁ + y₂) = Φ ρ₁ ρ₂ t₁ t₂ g y₁ y₂)
    (hex : ∀ y, 0 ≤ y → ∃ y₁ y₂, Valid ρ₁ ρ₂ t₁ t₂ y₁ y₂ ∧ y₁ + y₂ = y)
    (hf₁ : (breakpoints ρ₁).Finite) (hf₂ : (breakpoints ρ₂).Finite) :
    (breakpoints F).encard ≤ (breakpoints ρ₁).encard + (breakpoints ρ₂).encard + 1 := by
  set B₁ := hf₁.toFinset
  set B₂ := hf₂.toFinset
  have hB₁ : ∀ b ∈ breakpoints ρ₁, b ∈ B₁ := fun b hb => hf₁.mem_toFinset.mpr hb
  have hB₂ : ∀ b ∈ breakpoints ρ₂, b ∈ B₂ := fun b hb => hf₂.mem_toFinset.mpr hb
  set M := max (ρ₁ 0 t₁) (ρ₂ 0 t₂)
  set Λ : ℝ → ℝ := fun x => F x (Sum.inl t₁)
  -- every breakpoint has a split at its own level
  have hsplit : ∀ x ∈ breakpoints F, ∃ x₁ x₂, x₁ + x₂ = x ∧ x₁ ∈ Z₁ ρ₁ t₁ (Λ x) ∧
      x₂ ∈ Z₂ ρ₂ t₂ (Λ x) := by
    intro x hx
    have hxpos : 0 < x := ((mem_breakpoints_iff F x).mp hx).1
    obtain ⟨x₁, x₂, hv, hs⟩ := hex x hxpos.le
    have hF := hall x₁ x₂ hv
    rw [hs] at hF
    have hl : Λ x = min (ρ₁ x₁ t₁) (ρ₂ x₂ t₂) := by
      simp only [Λ, hF, Φ, Sum.elim_inl, if_true]
    rw [hl]
    exact ⟨x₁, x₂, hs, valid_Z hv⟩
  have key : ∀ P : Finset ℝ, (↑P : Set ℝ) ⊆ breakpoints F → P.card ≤ B₁.card + B₂.card + 1 := by
    intro P hP
    rw [Finset.card_eq_sum_card_image Λ P]
    have step : ∀ lam ∈ P.image Λ, (P.filter fun x => Λ x = lam).card ≤
        (B₁.filter (· ∈ Z₁ ρ₁ t₁ lam)).card + (B₂.filter (· ∈ Z₂ ρ₂ t₂ lam)).card +
          (if lam = M then 1 else 0) := by
      intro lam _
      apply level_bound g F hm₁ hm₂ hc₁ hc₂ hall lam B₁ B₂ hB₁ hB₂
      intro x hx
      obtain ⟨hxP, hxl⟩ := Finset.mem_filter.mp hx
      have hxb := hP hxP
      refine ⟨hxb, ?_⟩
      rw [← hxl]
      exact hsplit x hxb
    refine (Finset.sum_le_sum step).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have d1 : ∑ lam ∈ P.image Λ, (B₁.filter (· ∈ Z₁ ρ₁ t₁ lam)).card ≤ B₁.card := by
      rw [← Finset.card_biUnion]
      · apply Finset.card_le_card
        intro b hb
        obtain ⟨_, _, hb'⟩ := Finset.mem_biUnion.mp hb
        exact (Finset.mem_filter.mp hb').1
      · intro l₁ _ l₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro b hb1 hb2
        obtain ⟨hbB, hbZ⟩ := Finset.mem_filter.mp hb1
        obtain ⟨-, hbZ'⟩ := Finset.mem_filter.mp hb2
        have hbpos : 0 < b := ((mem_breakpoints_iff ρ₁ b).mp (hf₁.mem_toFinset.mp hbB)).1
        exact hne ((hbZ.2.1 hbpos).symm.trans (hbZ'.2.1 hbpos))
    have d2 : ∑ lam ∈ P.image Λ, (B₂.filter (· ∈ Z₂ ρ₂ t₂ lam)).card ≤ B₂.card := by
      rw [← Finset.card_biUnion]
      · apply Finset.card_le_card
        intro b hb
        obtain ⟨_, _, hb'⟩ := Finset.mem_biUnion.mp hb
        exact (Finset.mem_filter.mp hb').1
      · intro l₁ _ l₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro b hb1 hb2
        obtain ⟨hbB, hbZ⟩ := Finset.mem_filter.mp hb1
        obtain ⟨-, hbZ'⟩ := Finset.mem_filter.mp hb2
        have hbpos : 0 < b := ((mem_breakpoints_iff ρ₂ b).mp (hf₂.mem_toFinset.mp hbB)).1
        exact hne ((hbZ.2.1 hbpos).symm.trans (hbZ'.2.1 hbpos))
    have d3 : ∑ lam ∈ P.image Λ, (if lam = M then 1 else 0) ≤ 1 := by
      rw [Finset.sum_ite_eq']
      split_ifs <;> omega
    omega
  rw [hf₁.encard_eq_coe_toFinset_card, hf₂.encard_eq_coe_toFinset_card]
  by_contra hcon
  push Not at hcon
  have hle : ((B₁.card + B₂.card + 1 + 1 : ℕ) : ℕ∞) ≤ (breakpoints F).encard := by
    have := Order.add_one_le_of_lt hcon
    exact_mod_cast this
  obtain ⟨T, hT, hTc⟩ := Set.exists_subset_encard_eq hle
  have hTf : T.Finite := Set.finite_of_encard_eq_coe hTc
  have := key hTf.toFinset (by simpa using hT)
  rw [hTf.encard_eq_coe_toFinset_card] at hTc
  norm_cast at hTc
  omega

end ParAbs

end ThinFlowSP.Breakpoints


namespace ThinFlowSP.Breakpoints

set_option allowUnsafeReducibility true in
attribute [local reducible] Net.series Net.par

theorem reaches_map' {G H : Net} (f : G.V → H.V) (g : G.A → H.A)
    (ht : ∀ a, H.tail (g a) = f (G.tail a)) (hh : ∀ a, H.head (g a) = f (G.head a))
    {u v : G.V} (huv : Reaches G u v) : Reaches H (f u) (f v) := by
  unfold Reaches at *
  refine huv.lift f ?_
  rintro x y ⟨a, rfl, rfl⟩
  exact ⟨g a, ht a, hh a⟩

/-- In a two-terminal DAG `t` is reachable from every vertex. -/
theorem tt_reach_t {G : Net} (h : IsTwoTerminalDAG G) : ∀ v, Reaches G v G.t := by
  have : IsTrans G.V (fun x y => Relation.TransGen (Adj G) y x) :=
    ⟨fun _ _ _ h1 h2 => Relation.TransGen.trans h2 h1⟩
  have : Std.Irrefl (fun x y : G.V => Relation.TransGen (Adj G) y x) := ⟨h.1⟩
  have wf := Finite.wellFounded_of_trans_of_irrefl (fun x y : G.V => Relation.TransGen (Adj G) y x)
  intro v
  induction v using wf.induction with
  | _ v ih =>
    by_cases hv : v = G.t
    · rw [hv]; exact Relation.ReflTransGen.refl
    · have : ¬ ∀ a, G.tail a ≠ v := fun h' => hv ((h.2.2 v).mp h')
      push Not at this
      obtain ⟨a, ha⟩ := this
      have hadj : Adj G v (G.head a) := ⟨a, ha, rfl⟩
      exact Relation.ReflTransGen.head hadj (ih (G.head a) (Relation.TransGen.single hadj))

/-- A normalised potential on a two-terminal DAG. -/
theorem tt_potential {G : Net} (h : IsTwoTerminalDAG G) (hst : G.s ≠ G.t) :
    ∃ p : G.V → ℝ, p G.s = 0 ∧ p G.t = 1 ∧ ∀ a, p (G.tail a) < p (G.head a) := by
  classical
  set q : G.V → ℕ := fun v => (Finset.univ.filter fun w => Relation.TransGen (Adj G) w v).card
    with hq
  have qlt : ∀ u v, Relation.TransGen (Adj G) u v → q u < q v := by
    intro u v huv
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨u, by simp [huv], by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h.1 u⟩
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact hw.trans huv
  have qs : q G.s = 0 := by
    simp only [hq, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
    intro w hw
    obtain ⟨c, -, ⟨a, -, ha⟩⟩ := Relation.TransGen.tail'_iff.mp hw
    exact ((h.2.1 G.s).mpr rfl) a ha
  have qt : 0 < q G.t := by
    have := qlt G.s G.t (by
      rcases Relation.ReflTransGen.cases_head (tt_reach_t h G.s) with e | ⟨c, hc, hct⟩
      · exact absurd e hst
      · exact Relation.TransGen.head' hc hct)
    omega
  refine ⟨fun v => (q v : ℝ) / q G.t, by simp [qs], by field_simp, fun a => ?_⟩
  have := qlt _ _ (Relation.TransGen.single ⟨a, rfl, rfl⟩)
  apply div_lt_div_of_pos_right _ (by exact_mod_cast qt)
  exact_mod_cast this

theorem par_spg {G₁ G₂ : Net} (h₁ : IsTwoTerminalDAG G₁) (h₂ : IsTwoTerminalDAG G₂)
    (hst₁ : G₁.s ≠ G₁.t) (hst₂ : G₂.s ≠ G₂.t) : IsShortestPathGraph (G₁.par G₂) := by
  obtain ⟨p₁, p₁s, p₁t, hp₁⟩ := tt_potential h₁ hst₁
  obtain ⟨p₂, p₂s, p₂t, hp₂⟩ := tt_potential h₂ hst₂
  set P : (G₁.par G₂).V → ℝ := Sum.elim p₁ (fun v => p₂ v.1) with hP
  have hemb : ∀ w, P (parEmb G₁ G₂ w) = p₂ w := by
    intro w
    unfold parEmb
    split_ifs with e1 e2
    · subst e1; simp [hP, p₁s, p₂s]
    · subst e2; simp [hP, p₁t, p₂t]
    · simp [hP]
  have hpot : ∀ a, P ((G₁.par G₂).tail a) < P ((G₁.par G₂).head a) := by
    rintro (a | a)
    · exact hp₁ a
    · show P (parEmb G₁ G₂ (G₂.tail a)) < P (parEmb G₁ G₂ (G₂.head a))
      rw [hemb, hemb]; exact hp₂ a
  refine ⟨?_, ?_⟩
  · have key : ∀ u v, Relation.TransGen (Adj (G₁.par G₂)) u v → P u < P v := by
      intro u v huv
      induction huv with
      | single hab => obtain ⟨a, rfl, rfl⟩ := hab; exact hpot a
      | tail _ hab ih => obtain ⟨a, ha, rfl⟩ := hab; subst ha; exact ih.trans (hpot a)
    intro v hv
    exact lt_irrefl _ (key v v hv)
  · rintro (v | ⟨v, hv⟩)
    · exact reaches_map' (G := G₁) (H := G₁.par G₂) Sum.inl Sum.inl (fun _ => rfl) (fun _ => rfl)
        (tt_reach h₁ v)
    · have := reaches_map' (G := G₂) (H := G₁.par G₂) (parEmb G₁ G₂) Sum.inr (fun _ => rfl)
        (fun _ => rfl) (tt_reach h₂ v)
      have e1 : parEmb G₁ G₂ G₂.s = Sum.inl G₁.s := parEmb_s
      have e2 : parEmb G₁ G₂ v = Sum.inr ⟨v, hv⟩ := (parEmb_eq_inr _ _).mpr rfl
      rw [e1, e2] at this
      exact this

theorem lem30 (G₁ G₂ : Net) (h₁ : IsTwoTerminalDAG G₁) (h₂ : IsTwoTerminalDAG G₂)
    (Astar : Finset (G₁.A ⊕ G₂.A)) (ν : G₁.A ⊕ G₂.A → ℝ) (hν : ∀ a, 0 < ν a)
    (ρ : ℝ → (G₁.par G₂).V → ℝ) (ρ₁ : ℝ → G₁.V → ℝ) (ρ₂ : ℝ → G₂.V → ℝ)
    (hρ : IsLabelFunction (G₁.par G₂) Astar ν ρ)
    (hρ₁ : IsLabelFunction G₁ Astar.toLeft (fun a => ν (Sum.inl a)) ρ₁)
    (hρ₂ : IsLabelFunction G₂ Astar.toRight (fun a => ν (Sum.inr a)) ρ₂) :
    (breakpoints ρ).encard ≤ (breakpoints ρ₁).encard + (breakpoints ρ₂).encard + 1 := by
  have hst₁ := st_of_label h₁ hρ₁
  have hst₂ := st_of_label h₂ hρ₂
  by_cases hf₁ : (breakpoints ρ₁).Finite
  swap
  · rw [Set.Infinite.encard_eq hf₁]; simp
  by_cases hf₂ : (breakpoints ρ₂).Finite
  swap
  · rw [Set.Infinite.encard_eq hf₂]; simp
  have hν₁ : ∀ a, 0 < ν (Sum.inl a) := fun a => hν _
  have hν₂ : ∀ a, 0 < ν (Sum.inr a) := fun a => hν _
  have hm₁ := ((lemma_18 G₁ Astar.toLeft _ (tt_spg h₁) hst₁ hν₁).2 ρ₁ hρ₁ G₁.t).1
  have hm₂ := ((lemma_18 G₂ Astar.toRight _ (tt_spg h₂) hst₂ hν₂).2 ρ₂ hρ₂ G₂.t).1
  have hc₁ : ContinuousOn (fun z => ρ₁ z G₁.t) (Set.Ici 0) :=
    (continuousOn_pi.mp (label_continuousOn (tt_spg h₁) hst₁ hν₁ hρ₁)) G₁.t
  have hc₂ : ContinuousOn (fun z => ρ₂ z G₂.t) (Set.Ici 0) :=
    (continuousOn_pi.mp (label_continuousOn (tt_spg h₂) hst₂ hν₂ hρ₂)) G₂.t
  have hall : ∀ y₁ y₂, ParAbs.Valid ρ₁ ρ₂ G₁.t G₂.t y₁ y₂ →
      ρ (y₁ + y₂) = ParAbs.Φ ρ₁ ρ₂ G₁.t G₂.t
        (Subtype.val : {v : G₂.V // v ≠ G₂.s ∧ v ≠ G₂.t} → G₂.V) y₁ y₂ := by
    intro y₁ y₂ hv
    obtain ⟨hy₁, hy₂, hv₁, hv₂⟩ := hv
    obtain ⟨hs1, x1, hx1, hl1⟩ := hρ₁ y₁ hy₁
    obtain ⟨hs2, x2, hx2, hl2⟩ := hρ₂ y₂ hy₂
    have hlam1 : 0 < y₁ → min (ρ₁ y₁ G₁.t) (ρ₂ y₂ G₂.t) = ρ₁ y₁ G₁.t :=
      fun h => min_eq_left (hv₁ h)
    have hlam2 : 0 < y₂ → min (ρ₁ y₁ G₁.t) (ρ₂ y₂ G₂.t) = ρ₂ y₂ G₂.t :=
      fun h => min_eq_right (hv₂ h)
    obtain ⟨g1, g2⟩ := par_glue h₁ h₂ hst₁ hst₂ hx1 hx2 hl1 hl2 (by rw [hs1, hs2]) rfl hlam1 hlam2
    obtain ⟨hs, x, hx, hl⟩ := hρ (y₁ + y₂) (by linarith)
    have := corollary_15 (G₁.par G₂) Astar ν (par_spg h₁ h₂ hst₁ hst₂)
      (fun e => hst₁ (Sum.inl.inj e)) hν x
      (Sum.elim x1 x2) (ρ (y₁ + y₂)) _ (y₁ + y₂) hx g1 hl g2 ?_
    · rw [this]; rfl
    · rw [hs]
      show (1:ℝ) = parLabels G₁ G₂ (ρ₁ y₁) (ρ₂ y₂) _ (Sum.inl G₁.s)
      simp [parLabels, hst₁, hs1]
  have hex : ∀ y, 0 ≤ y → ∃ y₁ y₂, ParAbs.Valid ρ₁ ρ₂ G₁.t G₂.t y₁ y₂ ∧ y₁ + y₂ = y := by
    intro y hy
    obtain ⟨y₁, y₂, lam, a1, a2, a3, a4, a5, a6⟩ := split_exists _ _ hc₁ hc₂ y hy
    refine ⟨y₁, y₂, ⟨a1, a2, fun h => ?_, fun h => ?_⟩, a3⟩
    · have := a5 h; rw [a4] at this; rw [← this]; exact min_le_right _ _
    · have := a6 h; rw [a4] at this; rw [← this]; exact min_le_left _ _
  exact ParAbs.abstract30 (ι₁ := G₁.V) (κ := {v : G₂.V // v ≠ G₂.s ∧ v ≠ G₂.t}) Subtype.val ρ
    hm₁ hm₂ hc₁ hc₂ hall hex hf₁ hf₂

end ThinFlowSP.Breakpoints

open ThinFlowSP.Breakpoints in
theorem solution (G₁ G₂ : Net) (h₁ : IsTwoTerminalDAG G₁) (h₂ : IsTwoTerminalDAG G₂)
    (Astar : Finset (G₁.A ⊕ G₂.A)) (ν : G₁.A ⊕ G₂.A → ℝ) (hν : ∀ a, 0 < ν a)
    (ρ : ℝ → (G₁.par G₂).V → ℝ) (ρ₁ : ℝ → G₁.V → ℝ) (ρ₂ : ℝ → G₂.V → ℝ)
    (hρ : IsLabelFunction (G₁.par G₂) Astar ν ρ)
    (hρ₁ : IsLabelFunction G₁ Astar.toLeft (fun a => ν (Sum.inl a)) ρ₁)
    (hρ₂ : IsLabelFunction G₂ Astar.toRight (fun a => ν (Sum.inr a)) ρ₂) :
    (breakpoints ρ).encard ≤ (breakpoints ρ₁).encard + (breakpoints ρ₂).encard + 1 :=
  lem30 G₁ G₂ h₁ h₂ Astar ν hν ρ ρ₁ ρ₂ hρ hρ₁ hρ₂
