-- Prove2me | solution 1 for PersPricingDist.UniformA.uu_retail_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T19:15:21.946887+00:00
-- url     : https://prove2.me/submissions/cc005ac3-c3bb-4263-b029-761047d2a865

import Mathlib
import Definitions.Def_PersPricingDist_UniformA_Setting

open PersPricingDist.UniformA MeasureTheory

namespace PPD1UU

lemma demand_nonneg (M : Model) (P : ℝ → Prop) : 0 ≤ M.demand P := ENNReal.toReal_nonneg

lemma demand_le (M : Model) (P : ℝ → Prop) (a b : ℝ)
    (h : ∀ x, 0 ≤ x → x ≤ M.X → P x → a ≤ x ∧ x ≤ b) : M.demand P ≤ max (b - a) 0 := by
  unfold Model.demand
  have hsub : {x : ℝ | x ∈ Set.Icc 0 M.X ∧ P x} ⊆ Set.Icc a b := by
    rintro x ⟨⟨h0, h1⟩, hP⟩
    exact h x h0 h1 hP
  calc (volume {x : ℝ | x ∈ Set.Icc 0 M.X ∧ P x}).toReal
      ≤ (volume (Set.Icc a b)).toReal :=
        ENNReal.toReal_mono (by simp [Real.volume_Icc]) (measure_mono hsub)
    _ = max (b - a) 0 := by rw [Real.volume_Icc, ENNReal.toReal_ofReal']

lemma demand_ge (M : Model) (P : ℝ → Prop) (a b : ℝ)
    (h : ∀ x, a < x → x < b → 0 ≤ x ∧ x ≤ M.X ∧ P x) : b - a ≤ M.demand P := by
  unfold Model.demand
  have hsup : Set.Ioo a b ⊆ {x : ℝ | x ∈ Set.Icc 0 M.X ∧ P x} := by
    rintro x ⟨ha, hb⟩
    obtain ⟨p1, p2, p3⟩ := h x ha hb
    exact ⟨⟨p1, p2⟩, p3⟩
  have hfin : volume {x : ℝ | x ∈ Set.Icc 0 M.X ∧ P x} ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := volume (Set.Icc 0 M.X))
    · simp [Real.volume_Icc]
    · exact measure_mono (fun x hx => hx.1)
  calc b - a ≤ max (b - a) 0 := le_max_left _ _
    _ = (volume (Set.Ioo a b)).toReal := by rw [Real.volume_Ioo, ENNReal.toReal_ofReal']
    _ ≤ _ := ENNReal.toReal_mono hfin (measure_mono hsup)

/-- union bound for demands -/
lemma demand_union_ge (M : Model) (P Q : ℝ → Prop) (a b : ℝ)
    (h : ∀ x, a < x → x < b → 0 ≤ x ∧ x ≤ M.X ∧ (P x ∨ Q x)) :
    b - a ≤ M.demand P + M.demand Q := by
  have h1 := demand_ge M (fun x => P x ∨ Q x) a b h
  refine h1.trans ?_
  unfold Model.demand
  have hfin : ∀ R : ℝ → Prop, volume {x : ℝ | x ∈ Set.Icc 0 M.X ∧ R x} ≠ ⊤ := by
    intro R
    apply ne_top_of_le_ne_top (b := volume (Set.Icc 0 M.X))
    · simp [Real.volume_Icc]
    · exact measure_mono (fun x hx => hx.1)
  rw [← ENNReal.toReal_add (hfin P) (hfin Q)]
  apply ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin P, hfin Q⟩)
  refine (measure_mono ?_).trans (measure_union_le _ _)
  rintro x ⟨hx, hPQ | hPQ⟩
  · exact Or.inl ⟨hx, hPQ⟩
  · exact Or.inr ⟨hx, hPQ⟩

lemma max_pos_eq {a : ℝ} (h : 0 < max a 0) : max a 0 = a := by
  rcases le_total a 0 with h' | h'
  · rw [max_eq_right h'] at h; exact absurd h (lt_irrefl 0)
  · exact max_eq_left h'

/-- The indifference point. -/
noncomputable def xi (M : Model) (a b : ℝ) : ℝ := (1 - M.v - a + b) / (1 - M.s)
/-- B's cutoff. -/
noncomputable def xb (M : Model) (b : ℝ) : ℝ := (M.v - b) / M.s

section
variable (M : Model) (hM : M.Standing)
include hM

lemma s_pos : 0 < M.s := hM.s_pos
lemma one_sub_s : 0 < 1 - M.s := by linarith [hM.s_lt_v, hM.v_lt_one]

lemma xi_mul (a b : ℝ) : (1 - M.s) * xi M a b = 1 - M.v - a + b := by
  unfold xi; have := one_sub_s M hM; field_simp

lemma xb_mul (b : ℝ) : M.s * xb M b = M.v - b := by
  unfold xb; have := s_pos M hM; field_simp

lemma one_le_X : 1 ≤ M.X := by
  have hs := hM.s_pos
  have := hM.market_large
  rw [div_le_iff₀ hs] at this
  have : M.s * 1 ≤ M.s * M.X := by nlinarith [hM.s_lt_v]
  exact le_of_mul_le_mul_left this hs

lemma xb_le_X (b : ℝ) (hb : 0 ≤ b) : xb M b ≤ M.X := by
  have hs := hM.s_pos
  have := hM.market_large
  rw [div_le_iff₀ hs] at this
  have h := xb_mul M hM b
  have : M.s * xb M b ≤ M.s * M.X := by nlinarith
  exact le_of_mul_le_mul_left this hs

/-- consumers served by B lie to the right of the indifference point and left of B's cutoff -/
lemma setB (a b x : ℝ) (hb : 0 < b) (hB : M.buysB_UU a b x) :
    xi M a b < x ∧ x ≤ xb M b := by
  have h1s := one_sub_s M hM
  simp only [Model.buysB_UU, Model.uA, Model.uB] at hB
  obtain ⟨hB1, hB2⟩ := hB
  have e := le_max_left (1 - x) 0
  have hpos : 0 < max (M.v - M.s * x) 0 := by linarith
  rw [max_pos_eq hpos] at hB1 hB2
  constructor
  · have : (1 - M.s) * xi M a b < (1 - M.s) * x := by rw [xi_mul M hM]; linarith
    exact lt_of_mul_lt_mul_left this h1s.le
  · have : M.s * x ≤ M.s * xb M b := by rw [xb_mul M hM]; linarith
    exact le_of_mul_le_mul_left this hM.s_pos

/-- consumers served by A (at a positive price) lie left of the indifference point -/
lemma setA (a b x : ℝ) (ha : 0 < a) (hA : M.buysA_UU a b x) :
    x ≤ 1 - a ∧ x ≤ xi M a b := by
  have h1s := one_sub_s M hM
  simp only [Model.buysA_UU, Model.uA, Model.uB] at hA
  obtain ⟨hA1, hA2⟩ := hA
  have hpos : 0 < max (1 - x) 0 := by linarith
  rw [max_pos_eq hpos] at hA1 hA2
  have e := le_max_left (M.v - M.s * x) 0
  refine ⟨by linarith, ?_⟩
  have : (1 - M.s) * x ≤ (1 - M.s) * xi M a b := by rw [xi_mul M hM]; linarith
  exact le_of_mul_le_mul_left this h1s

/-- lower bound on B's set -/
lemma setB_ge (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (h1 : xi M a b < x) (h2 : x < xb M b) :
    M.buysB_UU a b x := by
  have h1s := one_sub_s M hM
  have hs := hM.s_pos
  have k1 : (1 - M.s) * xi M a b < (1 - M.s) * x := mul_lt_mul_of_pos_left h1 h1s
  have k2 : M.s * x < M.s * xb M b := mul_lt_mul_of_pos_left h2 hs
  rw [xi_mul M hM] at k1
  rw [xb_mul M hM] at k2
  simp only [Model.buysB_UU, Model.uA, Model.uB]
  rw [max_eq_left (by linarith : (0:ℝ) ≤ M.v - M.s * x)]
  refine ⟨by linarith, ?_⟩
  rcases le_total (1 - x) 0 with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

/-- lower bound on A's set -/
lemma setA_ge (a b x : ℝ) (ha : 0 < a) (h1 : x < xi M a b) (h2 : x < 1 - a) :
    M.buysA_UU a b x := by
  have h1s := one_sub_s M hM
  have hsx : M.s * x < M.s * 1 := mul_lt_mul_of_pos_left (by linarith) hM.s_pos
  have hvx : 0 < M.v - M.s * x := by linarith [hM.s_lt_v]
  have k1 : (1 - M.s) * x < (1 - M.s) * xi M a b := mul_lt_mul_of_pos_left h1 h1s
  rw [xi_mul M hM] at k1
  simp only [Model.buysA_UU, Model.uA, Model.uB]
  rw [max_eq_left (by linarith : (0:ℝ) ≤ 1 - x)]
  refine ⟨by linarith, ?_⟩
  rw [max_eq_left hvx.le]; linarith

lemma xb_nonneg (b : ℝ) (hb : b ≤ M.v) : 0 ≤ xb M b := by
  unfold xb; exact div_nonneg (by linarith) hM.s_pos.le

lemma xi_le_iff (p b : ℝ) : xi M p b ≤ 1 - p ↔ 1 - p ≤ xb M b := by
  have h1s := one_sub_s M hM
  have hs := hM.s_pos
  have e1 := xi_mul M hM p b
  have e2 := xb_mul M hM b
  constructor
  · intro h
    have : (1 - M.s) * xi M p b ≤ (1 - M.s) * (1 - p) := mul_le_mul_of_nonneg_left h h1s.le
    have : M.s * (1 - p) ≤ M.s * xb M b := by linarith
    exact le_of_mul_le_mul_left this hs
  · intro h
    have : M.s * (1 - p) ≤ M.s * xb M b := mul_le_mul_of_nonneg_left h hs.le
    have : (1 - M.s) * xi M p b ≤ (1 - M.s) * (1 - p) := by linarith
    exact le_of_mul_le_mul_left this h1s

lemma DA_le (p b : ℝ) (hp : 0 < p) : M.DA_UU p b ≤ max (xi M p b) 0 := by
  have := demand_le M (M.buysA_UU p b) 0 (max (xi M p b) 0) (by
    intro x hx0 _ hA
    exact ⟨hx0, le_max_of_le_left (setA M hM p b x hp hA).2⟩)
  rwa [sub_zero, max_eq_left (le_max_right _ _)] at this

lemma DA_le' (p b : ℝ) (hp : 0 < p) : M.DA_UU p b ≤ max (1 - p) 0 := by
  have := demand_le M (M.buysA_UU p b) 0 (1 - p) (by
    intro x hx0 _ hA
    exact ⟨hx0, (setA M hM p b x hp hA).1⟩)
  rwa [sub_zero] at this

lemma DB_le (a b : ℝ) (hb : 0 < b) : M.DB_UU a b ≤ max (xb M b - max (xi M a b) 0) 0 :=
  demand_le M _ _ _ (by
    intro x hx0 _ hB
    obtain ⟨h1, h2⟩ := setB M hM a b x hb hB
    exact ⟨max_le h1.le hx0, h2⟩)

lemma DB_ge (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hbv : b ≤ M.v) :
    xb M b - max (xi M a b) 0 ≤ M.DB_UU a b :=
  demand_ge M _ _ _ (by
    intro x h1 h2
    refine ⟨(le_max_right _ _).trans h1.le, h2.le.trans (xb_le_X M hM b hb.le), ?_⟩
    exact setB_ge M hM a b x ha hb ((le_max_left _ _).trans_lt h1) h2)

lemma DA_ge (a b : ℝ) (ha : 0 < a) : min (xi M a b) (1 - a) ≤ M.DA_UU a b := by
  have := demand_ge M (M.buysA_UU a b) 0 (min (xi M a b) (1 - a)) (by
    intro x h1 h2
    have hX := one_le_X M hM
    refine ⟨h1.le, by linarith [min_le_right (xi M a b) (1 - a)], ?_⟩
    exact setA_ge M hM a b x ha (lt_of_lt_of_le h2 (min_le_left _ _))
      (lt_of_lt_of_le h2 (min_le_right _ _)))
  rwa [sub_zero] at this

/-- A undercut region: B sells nothing. -/
lemma DB_zero_left (p b : ℝ) (hb : 0 < b) (h : xb M b < 1 - p) : M.DB_UU p b = 0 := by
  have hx : ¬ (xi M p b ≤ 1 - p) := by
    rw [xi_le_iff M hM]; linarith
  push Not at hx
  have := DB_le M hM p b hb
  rw [max_eq_right (by linarith [le_max_left (xi M p b) 0])] at this
  exact le_antisymm this (demand_nonneg M _)

/-- A's profit, upper bound in the main regime. -/
lemma PA_up (w p b : ℝ) (hw : 0 ≤ w) (hb : 0 < b) (hbv : b ≤ M.v) (hp : 0 < p)
    (hpb : 1 - p ≤ xb M b) :
    M.profA_UU w p b ≤ p * max (xi M p b) 0 + w * (xb M b - max (xi M p b) 0) := by
  have hc : max (xi M p b) 0 ≤ xb M b := by
    have := (xi_le_iff M hM p b).2 hpb
    have := xb_nonneg M hM b hbv
    apply max_le <;> linarith
  have h1 := mul_le_mul_of_nonneg_left (DA_le M hM p b hp) hp.le
  have h2 := DB_le M hM p b hb
  rw [max_eq_left (by linarith)] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 hw
  unfold Model.profA_UU
  linarith

lemma PA_left (w p b : ℝ) (hb : 0 < b) (hp : 0 < p) (hp1 : p ≤ 1) (hpb : xb M b < 1 - p) :
    M.profA_UU w p b = p * (1 - p) := by
  have hDB := DB_zero_left M hM p b hb hpb
  have hx : ¬ (xi M p b ≤ 1 - p) := by
    rw [xi_le_iff M hM]; linarith
  push Not at hx
  have h1 := DA_le' M hM p b hp
  have h2 := DA_ge M hM p b hp
  rw [min_eq_right hx.le] at h2
  rw [max_eq_left (by linarith)] at h1
  unfold Model.profA_UU Model.DB_UU at *
  rw [hDB, le_antisymm h1 h2]
  ring

lemma PA_exact (w p b : ℝ) (hb : 0 < b) (hbv : b ≤ M.v) (hp : 0 < p) (hpb : 1 - p ≤ xb M b)
    (hxi : 0 ≤ xi M p b) :
    M.profA_UU w p b = p * xi M p b + w * (xb M b - xi M p b) := by
  have h1 := DA_le M hM p b hp
  have h2 := DA_ge M hM p b hp
  have hle := (xi_le_iff M hM p b).2 hpb
  rw [max_eq_left hxi] at h1
  rw [min_eq_left hle] at h2
  have h3 := DB_le M hM p b hb
  have h4 := DB_ge M hM p b hp hb hbv
  rw [max_eq_left hxi] at h3 h4
  rw [max_eq_left (by linarith)] at h3
  unfold Model.profA_UU
  rw [le_antisymm h1 h2, le_antisymm h3 h4]

lemma PB_up (w a q : ℝ) (hq : 0 < q) (hqw : w < q) :
    M.profB_UU w a q ≤ (q - w) * max (xb M q - max (xi M a q) 0) 0 := by
  unfold Model.profB_UU
  exact mul_le_mul_of_nonneg_left (DB_le M hM a q hq) (by linarith)

lemma PB_ge (w a q : ℝ) (ha : 0 < a) (hq : 0 < q) (hqv : q ≤ M.v) (hqw : w ≤ q) :
    (q - w) * (xb M q - max (xi M a q) 0) ≤ M.profB_UU w a q := by
  unfold Model.profB_UU
  exact mul_le_mul_of_nonneg_left (DB_ge M hM a q ha hq hqv) (by linarith)

/-- coverage at A's price `w`: A gets `w` on every unit sold. -/
lemma PA_cover (w b c : ℝ) (hw : 0 ≤ w) (hc : c ≤ M.X)
    (h : ∀ x, 0 < x → x < c → 0 ≤ M.uA x - w ∨ 0 < M.uB x - b) :
    w * c ≤ M.profA_UU w w b := by
  have := demand_union_ge M (M.buysA_UU w b) (M.buysB_UU w b) 0 c (by
    intro x h1 h2
    refine ⟨h1.le, by linarith, ?_⟩
    by_cases hB : M.buysB_UU w b x
    · exact Or.inr hB
    · left
      simp only [Model.buysB_UU, not_and, not_lt] at hB
      rcases h x h1 h2 with h' | h'
      · by_cases h0 : 0 ≤ M.uB x - b
        · exact ⟨h', hB h0⟩
        · push Not at h0; exact ⟨h', by linarith⟩
      · exact ⟨by linarith [hB h'.le], hB h'.le⟩)
  unfold Model.profA_UU Model.DA_UU Model.DB_UU
  nlinarith

lemma QA_eq (w b p : ℝ) : p * xi M p b + w * (xb M b - xi M p b) =
    w * xb M b + (1 - M.v + b - w) ^ 2 / (4 * (1 - M.s)) -
      (p - (1 - M.v + b + w) / 2) ^ 2 / (1 - M.s) := by
  have h1s := one_sub_s M hM
  unfold xi; field_simp; ring

lemma xb_sub_xi (a q : ℝ) :
    xb M q - xi M a q = (M.v - M.s + M.s * a - q) / (M.s * (1 - M.s)) := by
  have h1s := one_sub_s M hM
  have hs := hM.s_pos
  unfold xi xb; field_simp; ring

lemma RB_eq (w a q : ℝ) : (q - w) * (xb M q - xi M a q) =
    (M.v - M.s + M.s * a - w) ^ 2 / (4 * (M.s * (1 - M.s))) -
      (q - (w + M.v - M.s + M.s * a) / 2) ^ 2 / (M.s * (1 - M.s)) := by
  have h1s := one_sub_s M hM
  have hs := hM.s_pos
  rw [xb_sub_xi M hM]; field_simp; ring

lemma X_gt_one : 1 < M.X := by
  have hs := hM.s_pos
  have := hM.market_large
  rw [div_le_iff₀ hs] at this
  have : M.s * 1 < M.s * M.X := by nlinarith [hM.s_lt_v]
  exact lt_of_mul_lt_mul_left this hs.le

/-- With a nonpositive price, B serves every consumer beyond `x = 1`. -/
lemma DB_ge_nonpos (a b : ℝ) (ha : 0 < a) (hb : b ≤ 0) : M.X - 1 ≤ M.DB_UU a b :=
  demand_ge M _ _ _ (by
    intro x h1 h2
    refine ⟨by linarith, h2.le, ?_⟩
    simp only [Model.buysB_UU, Model.uA, Model.uB]
    rw [max_eq_right (by linarith : 1 - x ≤ 0)]
    have := le_max_right (M.v - M.s * x) 0
    constructor <;> linarith)

/-- Uniqueness of the downstream equilibrium: any equilibrium satisfies both first-order
conditions. -/
lemma nash_foc (w a b : ℝ) (hw0 : 0 < w) (hw1 : w < 1) (hwv : w < M.v)
    (hw2 : M.s < 2 * (M.v - w)) (hw3 : (2 - M.s) * (w - M.v + M.s) < M.s * (1 - M.s + w))
    (hN : M.IsNashUU w a b) :
    a = (1 - M.v + b + w) / 2 ∧ b = (w + M.v - M.s + M.s * a) / 2 := by
  obtain ⟨hA, hB⟩ := hN
  have hs := hM.s_pos
  have hsv := hM.s_lt_v
  have hv1 := hM.v_lt_one
  have h1s := one_sub_s M hM
  have hss : 0 < M.s * (1 - M.s) := mul_pos hs h1s
  have hB0 : 0 ≤ M.profB_UU w a b := by
    have := hB w; unfold Model.profB_UU at this ⊢; simpa using this
  have hcov1 : w * (1 - w) ≤ M.profA_UU w a b := by
    refine le_trans ?_ (hA w)
    apply PA_cover M hM w b (1 - w) hw0.le (by linarith [one_le_X M hM])
    intro x hx0 hx1; left; simp only [Model.uA]; rw [max_eq_left (by linarith)]; linarith
  have hcov2 : 0 < b → b ≤ M.v → w * xb M b ≤ M.profA_UU w a b := by
    intro hb hbv
    refine le_trans ?_ (hA w)
    apply PA_cover M hM w b (xb M b) hw0.le (xb_le_X M hM b hb.le)
    intro x hx0 hx1; right
    have : M.s * x < M.s * xb M b := mul_lt_mul_of_pos_left hx1 hs
    rw [xb_mul M hM] at this
    simp only [Model.uB]; rw [max_eq_left (by linarith)]; linarith
  have hDAnn := demand_nonneg M (M.buysA_UU a b)
  have hDBnn := demand_nonneg M (M.buysB_UU a b)
  have hww : 0 < w * (1 - w) := mul_pos hw0 (by linarith)
  have hDB_neg : b < w → M.DB_UU a b = 0 := by
    intro hbw
    unfold Model.profB_UU at hB0
    have : M.DB_UU a b ≤ 0 := by nlinarith
    exact le_antisymm this hDBnn
  -- Step 1: a > 0
  have ha0 : 0 < a := by
    by_contra ha
    push Not at ha
    have hπ : M.profA_UU w a b ≤ w * M.DB_UU a b := by
      unfold Model.profA_UU
      have : a * M.DA_UU a b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha (demand_nonneg _ _)
      linarith
    rcases lt_or_ge b w with hbw | hbw
    · rw [hDB_neg hbw] at hπ; linarith
    · have hb : 0 < b := by linarith
      have hD := DB_le M hM a b hb
      have hxi : 0 < xi M a b := by unfold xi; apply div_pos _ h1s; linarith
      rw [max_eq_left hxi.le] at hD
      rcases le_total (xb M b - xi M a b) 0 with h | h
      · rw [max_eq_right h] at hD
        have : M.DB_UU a b = 0 := le_antisymm hD hDBnn
        rw [this] at hπ; linarith
      · rw [max_eq_left h] at hD
        have hbv : b ≤ M.v := by
          have := xb_mul M hM b
          have : 0 ≤ xb M b := by linarith
          have := mul_nonneg hs.le this
          linarith
        have := hcov2 hb hbv
        have : w * M.DB_UU a b < w * xb M b :=
          mul_lt_mul_of_pos_left (by linarith) hw0
        linarith
  by_cases hact : w < b ∧ 0 < M.DB_UU a b
  · -- Case II: B is active
    obtain ⟨hbw, hDBpos⟩ := hact
    have hb : 0 < b := by linarith
    have hbv : b < M.v := by
      by_contra h; push Not at h
      have hD := DB_le M hM a b hb
      have : xb M b ≤ 0 := by
        have := xb_mul M hM b
        by_contra h'; push Not at h'
        have : 0 < M.s * xb M b := mul_pos hs h'
        linarith
      rw [max_eq_right (by linarith [le_max_right (xi M a b) 0])] at hD
      linarith
    have hxbpos : 0 < xb M b := by unfold xb; exact div_pos (by linarith) hs
    have hII1 : 1 - a ≤ xb M b := by
      by_contra h; push Not at h
      have := DB_zero_left M hM a b hb h
      linarith
    have hII2 : xi M a b < xb M b := by
      by_contra h; push Not at h
      have hD := DB_le M hM a b hb
      rw [max_eq_right (by linarith [le_max_left (xi M a b) 0])] at hD
      linarith
    have hxbm := xb_mul M hM b
    -- A-step
    have hA_eq : a = (1 - M.v + b + w) / 2 := by
      set pv := (1 - M.v + b + w) / 2 with hpv
      set pd := max pv (1 - xb M b) with hpd
      have hpd0 : 0 < pd := lt_of_lt_of_le (by rw [hpv]; linarith) (le_max_left _ _)
      have hpdb : 1 - pd ≤ xb M b := by linarith [le_max_right pv (1 - xb M b)]
      have hpdu : pd < 1 - M.v + b := by
        apply max_lt
        · rw [hpv]; linarith
        · have : (1 - M.s) * xb M b > 0 := mul_pos h1s hxbpos
          linarith
      have hxipd : 0 < xi M pd b := by unfold xi; exact div_pos (by linarith) h1s
      have hex := PA_exact M hM w pd b hb hbv.le hpd0 hpdb hxipd.le
      have hdev := hA pd
      rw [hex] at hdev
      have hup := PA_up M hM w a b hw0.le hb hbv.le ha0 hII1
      have hQpd := QA_eq M hM w b pd
      rcases le_total (xi M a b) 0 with hxa | hxa
      · exfalso
        rw [max_eq_right hxa] at hup
        have hpw : w < pd := lt_of_lt_of_le (by rw [hpv]; linarith) (le_max_left _ _)
        have : 0 < (pd - w) * xi M pd b := mul_pos (by linarith) hxipd
        have e : pd * xi M pd b + w * (xb M b - xi M pd b) = w * xb M b + (pd - w) * xi M pd b := by
          ring
        linarith
      · rw [max_eq_left hxa] at hup
        have hQa := QA_eq M hM w b a
        have key : (a - pv) ^ 2 ≤ (pd - pv) ^ 2 := by
          have : (a - pv) ^ 2 / (1 - M.s) ≤ (pd - pv) ^ 2 / (1 - M.s) := by linarith
          exact (div_le_div_iff_of_pos_right h1s).1 this
        rcases le_total (1 - xb M b) pv with hc | hc
        · rw [max_eq_left hc] at hpd
          rw [hpd, sub_self] at key
          have : (a - pv) ^ 2 = 0 := le_antisymm (by simpa using key) (sq_nonneg _)
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
          linarith
        · exfalso
          rw [max_eq_right hc] at hpd
          rw [hpd] at key
          have h1 : 0 ≤ (1 - xb M b) - pv := by linarith
          have h2 : (1 - xb M b) - pv ≤ a - pv := by linarith
          have h3 := (sq_le_sq₀ (by linarith) h1).1 key
          have : a - pv = (1 - xb M b) - pv := by linarith
          have ha' : a = 1 - xb M b := by linarith
          have : xi M a b = xb M b := by
            have e := xi_mul M hM a b
            have : (1 - M.s) * xi M a b = (1 - M.s) * xb M b := by rw [e, ha']; linarith
            exact mul_left_cancel₀ h1s.ne' this
          linarith
    refine ⟨hA_eq, ?_⟩
    -- B-step
    have hxia : 0 < xi M a b := by
      unfold xi; apply div_pos _ h1s; rw [hA_eq]; linarith
    have hsub := xb_sub_xi M hM a b
    have hm : b < M.v - M.s + M.s * a := by
      have : 0 < xb M b - xi M a b := by linarith
      rw [hsub] at this
      have := (div_pos_iff_of_pos_right hss).1 this
      linarith
    have ha1 : a < 1 := by rw [hA_eq]; linarith
    set qv := (w + M.v - M.s + M.s * a) / 2 with hqv
    set qd := max qv (a - 1 + M.v) with hqd
    have hqvw : w < qv := by rw [hqv]; linarith
    have hqdw : w < qd := lt_of_lt_of_le hqvw (le_max_left _ _)
    have hqdv : qd ≤ M.v := by
      apply max_le
      · have : M.s * a ≤ M.s * 1 := mul_le_mul_of_nonneg_left ha1.le hs.le
        rw [hqv]; linarith
      · linarith
    have hxiqd : 0 ≤ xi M a qd := by
      unfold xi; apply div_nonneg _ h1s.le; linarith [le_max_right qv (a - 1 + M.v)]
    have hlow := PB_ge M hM w a qd ha0 (by linarith) hqdv hqdw.le
    rw [max_eq_left hxiqd] at hlow
    have hupb := PB_up M hM w a b hb hbw
    rw [max_eq_left hxia.le, max_eq_left (by linarith)] at hupb
    have hdev := hB qd
    have hR1 := RB_eq M hM w a qd
    have hR2 := RB_eq M hM w a b
    have key : (b - qv) ^ 2 ≤ (qd - qv) ^ 2 := by
      have : (b - qv) ^ 2 / (M.s * (1 - M.s)) ≤ (qd - qv) ^ 2 / (M.s * (1 - M.s)) := by
        linarith
      exact (div_le_div_iff_of_pos_right hss).1 this
    rcases le_total (a - 1 + M.v) qv with hc | hc
    · rw [max_eq_left hc] at hqd
      rw [hqd, sub_self] at key
      have : (b - qv) ^ 2 = 0 := le_antisymm (by simpa using key) (sq_nonneg _)
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      linarith
    · exfalso
      rw [max_eq_right hc] at hqd
      rw [hqd] at key
      have hbq : a - 1 + M.v < b := by
        have e := xi_mul M hM a b
        have : 0 < (1 - M.s) * xi M a b := mul_pos h1s hxia
        linarith
      have h1 : 0 ≤ (a - 1 + M.v) - qv := by linarith
      have h3 := (sq_le_sq₀ (by linarith) h1).1 key
      linarith
  · -- Case I: B is inactive
    exfalso
    have hBle : M.profB_UU w a b ≤ 0 := by
      unfold Model.profB_UU
      by_cases hbw : w < b
      · have : M.DB_UU a b ≤ 0 := by
          by_contra h; push Not at h; exact hact ⟨hbw, h⟩
        have : M.DB_UU a b = 0 := le_antisymm this hDBnn
        rw [this]; simp
      · push Not at hbw
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hDBnn
    have hBall : ∀ q, M.profB_UU w a q ≤ 0 := fun q => (hB q).trans hBle
    -- I.1
    have hI1 : M.v - M.s + M.s * a ≤ w := by
      by_contra h; push Not at h
      set m := min M.v (M.v - M.s + M.s * a) with hm
      have hwm : w < m := lt_min hwv h
      have hm1 : m ≤ M.v := min_le_left _ _
      have hm2 : m ≤ M.v - M.s + M.s * a := min_le_right _ _
      set q := (w + m) / 2 with hq
      have hq0 : 0 < q := by rw [hq]; linarith
      have hlow := PB_ge M hM w a q ha0 hq0 (by rw [hq]; linarith) (by rw [hq]; linarith)
      have hxbq : 0 < xb M q := by unfold xb; apply div_pos _ hs; rw [hq]; linarith
      have hd : 0 < xb M q - xi M a q := by
        rw [xb_sub_xi M hM]; apply div_pos _ hss; rw [hq]; linarith
      have : 0 < xb M q - max (xi M a q) 0 := by
        rcases le_total (xi M a q) 0 with h' | h'
        · rw [max_eq_right h']; linarith
        · rw [max_eq_left h']; linarith
      have : 0 < (q - w) * (xb M q - max (xi M a q) 0) := mul_pos (by rw [hq]; linarith) this
      linarith [hBall q]
    have ha_half : a < 1 / 2 := by
      have : M.s * a < M.s * (1 / 2) := by linarith
      exact lt_of_mul_lt_mul_left this hs.le
    -- I.2: B sells nothing
    have hDB0 : M.DB_UU a b = 0 := by
      rcases lt_or_ge b w with hbw | hbw
      · exact hDB_neg hbw
      · have hb : 0 < b := by linarith
        have hD := DB_le M hM a b hb
        have : xb M b - xi M a b ≤ 0 := by
          rw [xb_sub_xi M hM]; apply div_nonpos_of_nonpos_of_nonneg _ hss.le; linarith
        rw [max_eq_right (by linarith [le_max_left (xi M a b) 0])] at hD
        exact le_antisymm hD hDBnn
    have hπa : M.profA_UU w a b ≤ a * (1 - a) := by
      unfold Model.profA_UU
      rw [hDB0]
      have := DA_le' M hM a b ha0
      rw [max_eq_left (by linarith)] at this
      have := mul_le_mul_of_nonneg_left this ha0.le
      linarith
    -- I.3: b > 0
    have hb : 0 < b := by
      by_contra h; push Not at h
      have := DB_ge_nonpos M hM a b ha0 h
      linarith [X_gt_one M hM]
    have hxbm := xb_mul M hM b
    -- I.4: a ≤ 1 - xb b
    have hI4 : a ≤ 1 - xb M b := by
      by_contra h; push Not at h
      have hxbp : 0 < xb M b := by linarith
      have hbv : b ≤ M.v := by
        by_contra h'; push Not at h'
        have : M.s * xb M b > 0 := mul_pos hs hxbp
        linarith
      have hgt : xi M a b < xb M b := by
        have : 0 < xb M b - xi M a b := by
          rw [xb_sub_xi M hM]; apply div_pos _ hss
          have : M.s * (1 - a) < M.s * xb M b := mul_lt_mul_of_pos_left (by linarith) hs
          linarith
        linarith
      have := DB_ge M hM a b ha0 hb hbv
      have : 0 < xb M b - max (xi M a b) 0 := by
        rcases le_total (xi M a b) 0 with h' | h'
        · rw [max_eq_right h']; linarith
        · rw [max_eq_left h']; linarith
      linarith
    rcases lt_or_eq_of_le hI4 with hlt | heq
    · -- A raises its price toward the monopoly price
      set t := min (1 - xb M b) (1 / 2) with ht
      have hat : a < t := lt_min hlt ha_half
      set p := (a + t) / 2 with hp
      have hp0 : 0 < p := by rw [hp]; linarith
      have hpt : p < t := by rw [hp]; linarith
      have hp1 : p ≤ 1 / 2 := by linarith [min_le_right (1 - xb M b) (1 / 2)]
      have hpb : xb M b < 1 - p := by linarith [min_le_left (1 - xb M b) (1 / 2)]
      have hex := PA_left M hM w p b hb hp0 (by linarith) hpb
      have hdev := hA p
      rw [hex] at hdev
      have : 0 < (p - a) * (1 - p - a) := mul_pos (by rw [hp]; linarith) (by linarith)
      have e : p * (1 - p) - a * (1 - a) = (p - a) * (1 - p - a) := by ring
      linarith
    · -- A sits at the limit price; raising it slightly is profitable
      have hxa : xi M a b = 1 - a := by
        have e := xi_mul M hM a b
        have : (1 - M.s) * xi M a b = (1 - M.s) * (1 - a) := by
          rw [e, heq]; linarith
        exact mul_left_cancel₀ h1s.ne' this
      have hbv : b ≤ M.v := by
        have : 0 ≤ xb M b := by linarith
        have := mul_nonneg hs.le this
        linarith
      have hbval : b = M.v - M.s + M.s * a := by
        have : M.s * (1 - a) = M.v - b := by rw [heq]; linarith
        linarith
      set pv := (1 - M.v + b + w) / 2 with hpv
      have hapv : a < pv := by
        have h1 : M.s * a ≤ w - M.v + M.s := by linarith
        have h2 : (2 - M.s) * (M.s * a) ≤ (2 - M.s) * (w - M.v + M.s) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
        have e : M.s * ((2 - M.s) * a) = (2 - M.s) * (M.s * a) := by ring
        have h3 : M.s * ((2 - M.s) * a) < M.s * (1 - M.s + w) := by linarith
        have h4 := lt_of_mul_lt_mul_left h3 hs.le
        rw [hpv, hbval]; linarith
      have hau : a < 1 - M.v + b := by
        have e := xi_mul M hM a b
        rw [hxa] at e
        have : 0 < (1 - M.s) * (1 - a) := mul_pos h1s (by linarith)
        linarith
      set r := min pv (1 - M.v + b) with hr
      have har : a < r := lt_min hapv hau
      set p := (a + r) / 2 with hp
      have hpa : a < p := by rw [hp]; linarith
      have hpr : p < r := by rw [hp]; linarith
      have hp0 : 0 < p := by linarith
      have hpb : 1 - p ≤ xb M b := by linarith
      have hxip : 0 ≤ xi M p b := by
        unfold xi; apply div_nonneg _ h1s.le; linarith [min_le_right pv (1 - M.v + b)]
      have hex := PA_exact M hM w p b hb hbv hp0 hpb hxip
      have hdev := hA p
      rw [hex, QA_eq M hM] at hdev
      have hQa := QA_eq M hM w b a
      rw [hxa] at hQa
      have hlt2 : (p - pv) ^ 2 < (a - pv) ^ 2 := by
        have : p ≤ pv := by linarith [min_le_left pv (1 - M.v + b)]
        have := pow_lt_pow_left₀ (show pv - p < pv - a by linarith) (by linarith) (two_ne_zero)
        have e1 : (p - pv) ^ 2 = (pv - p) ^ 2 := by ring
        have e2 : (a - pv) ^ 2 = (pv - a) ^ 2 := by ring
        rw [e1, e2]; exact this
      have : (p - pv) ^ 2 / (1 - M.s) < (a - pv) ^ 2 / (1 - M.s) :=
        div_lt_div_of_pos_right hlt2 h1s
      have e3 : a * (1 - a) + w * (xb M b - (1 - a)) = a * (1 - a) := by rw [heq]; ring
      rw [e3] at hQa
      linarith

/-- The candidate is an equilibrium whenever it satisfies the two first-order conditions
and lies in the interior regime. -/
lemma nash_exists (w a b : ℝ) (hw0 : 0 < w)
    (hfa : a = (1 - M.v + b + w) / 2) (hfb : b = (w + M.v - M.s + M.s * a) / 2)
    (ha0 : 0 < a) (hb0 : 0 < b) (hbv : b < M.v) (h1 : M.s * (1 - a) ≤ M.v - b)
    (h2 : a ≤ 1 - M.v + b) (hbw : w ≤ b) (hxb : M.s ≤ 2 * (M.v - b)) :
    M.IsNashUU w a b := by
  have hs := hM.s_pos
  have h1s := one_sub_s M hM
  have hss : 0 < M.s * (1 - M.s) := mul_pos hs h1s
  have hxbm := xb_mul M hM b
  have hxbpos : 0 < xb M b := by unfold xb; exact div_pos (by linarith) hs
  have hab : 1 - a ≤ xb M b := by
    have : M.s * (1 - a) ≤ M.s * xb M b := by linarith
    exact le_of_mul_le_mul_left this hs
  have hxb2 : 1 / 2 ≤ xb M b := by
    have : M.s * (1 / 2) ≤ M.s * xb M b := by linarith
    exact le_of_mul_le_mul_left this hs
  have hxi0 : 0 ≤ xi M a b := by unfold xi; exact div_nonneg (by linarith) h1s.le
  have hxi1 := (xi_le_iff M hM a b).2 hab
  have hexA := PA_exact M hM w a b hb0 hbv.le ha0 hab hxi0
  have hQa := QA_eq M hM w b a
  have hpv : a - (1 - M.v + b + w) / 2 = 0 := by rw [hfa]; ring
  rw [hpv] at hQa
  -- B's exact demand
  have hDB : M.DB_UU a b = xb M b - xi M a b := by
    have h3 := DB_le M hM a b hb0
    have h4 := DB_ge M hM a b ha0 hb0 hbv.le
    rw [max_eq_left hxi0] at h3 h4
    rw [max_eq_left (by linarith)] at h3
    exact le_antisymm h3 h4
  have hR := RB_eq M hM w a b
  have hqv : b - (w + M.v - M.s + M.s * a) / 2 = 0 := by rw [hfb]; ring
  rw [hqv] at hR
  constructor
  · intro p
    rw [hexA, hQa]
    have hW : 0 ≤ (1 - M.v + b - w) ^ 2 / (4 * (1 - M.s)) := by positivity
    rcases le_or_gt p 0 with hp | hp
    · have hD := DB_le M hM p b hb0
      have hD' : M.DB_UU p b ≤ xb M b := by
        refine hD.trans (max_le ?_ hxbpos.le)
        linarith [le_max_right (xi M p b) 0]
      unfold Model.profA_UU
      have : p * M.DA_UU p b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hp (demand_nonneg _ _)
      have := mul_le_mul_of_nonneg_left hD' hw0.le
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero]
      linarith
    · rcases lt_or_ge (xb M b) (1 - p) with hc | hc
      · rw [PA_left M hM w p b hb0 hp (by linarith) hc]
        have hq := QA_eq M hM w b (1 - xb M b)
        have hxi' : xi M (1 - xb M b) b = xb M b := by
          have e := xi_mul M hM (1 - xb M b) b
          have : (1 - M.s) * xi M (1 - xb M b) b = (1 - M.s) * xb M b := by rw [e]; linarith
          exact mul_left_cancel₀ h1s.ne' this
        rw [hxi'] at hq
        have hsq : 0 ≤ (1 - xb M b - (1 - M.v + b + w) / 2) ^ 2 / (1 - M.s) := by positivity
        have : 0 ≤ (xb M b - p) * (1 - xb M b - p) := mul_nonneg (by linarith) (by linarith)
        have e : (1 - xb M b) * xb M b + w * (xb M b - xb M b) - p * (1 - p)
            = (xb M b - p) * (1 - xb M b - p) := by ring
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero]
        linarith
      · have hup := PA_up M hM w p b hw0.le hb0 hbv.le hp hc
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero]
        rcases le_total (xi M p b) 0 with hx | hx
        · rw [max_eq_right hx] at hup; linarith
        · rw [max_eq_left hx] at hup
          have hq := QA_eq M hM w b p
          have hsq : 0 ≤ (p - (1 - M.v + b + w) / 2) ^ 2 / (1 - M.s) := by positivity
          linarith
  · intro q
    have hBb : M.profB_UU w a b = (b - w) * (xb M b - xi M a b) := by
      unfold Model.profB_UU; rw [hDB]
    rw [hBb, hR]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero]
    have hRm : 0 ≤ (M.v - M.s + M.s * a - w) ^ 2 / (4 * (M.s * (1 - M.s))) := by positivity
    rcases le_or_gt q w with hq | hq
    · unfold Model.profB_UU
      have := mul_nonpos_of_nonpos_of_nonneg (by linarith : q - w ≤ 0) (demand_nonneg M (M.buysB_UU a q))
      unfold Model.DB_UU; linarith
    · have hup := PB_up M hM w a q (by linarith) hq
      rcases le_total (xb M q - max (xi M a q) 0) 0 with h | h
      · rw [max_eq_right h] at hup; linarith
      · rw [max_eq_left h] at hup
        have : (q - w) * (xb M q - max (xi M a q) 0) ≤ (q - w) * (xb M q - xi M a q) :=
          mul_le_mul_of_nonneg_left (by linarith [le_max_left (xi M a q) 0]) (by linarith)
        have hq2 := RB_eq M hM w a q
        have hsq : 0 ≤ (q - (w + M.v - M.s + M.s * a) / 2) ^ 2 / (M.s * (1 - M.s)) := by
          positivity
        linarith

end
end PPD1UU

open PPD1UU in
theorem solution (M : Model) (hM : M.Standing) :
    M.IsNashUU M.wUU (M.pA_UU M.wUU) (M.pB_UU M.wUU) ∧
    (∀ pA pB : ℝ, M.IsNashUU M.wUU pA pB →
      pA = M.pA_UU M.wUU ∧ pB = M.pB_UU M.wUU) := by
  have hs := hM.s_pos
  have hsv := hM.s_lt_v
  have hv1 := hM.v_lt_one
  have hD : 0 < 2 * (5 * M.s + 4) := by linarith
  have hD' : 2 * (5 * M.s + 4) ≠ 0 := hD.ne'
  have h4s : (4 : ℝ) - M.s ≠ 0 := by linarith
  have hw : M.wUU = M.s * (M.s + 4 * M.v + 4) / (2 * (5 * M.s + 4)) := by
    unfold Model.wUU; field_simp; ring
  have ha : M.pA_UU M.wUU = (7 * M.s - 2 * M.v + 4) / (2 * (5 * M.s + 4)) := by
    unfold Model.pA_UU; rw [hw]; field_simp; ring
  have hb : M.pB_UU M.wUU = (4 * M.v + 6 * M.s * M.v - M.s ^ 2) / (2 * (5 * M.s + 4)) := by
    unfold Model.pB_UU; rw [hw]; field_simp; ring
  set w := M.wUU
  -- positivity facts, each a polynomial over the common denominator
  have pos : ∀ P : ℝ, 0 < P → 0 < P / (2 * (5 * M.s + 4)) := fun P hP => div_pos hP hD
  have hw0 : 0 < w := by rw [hw]; apply pos; nlinarith
  have hw1 : w < 1 := by
    have : 1 - w = (-M.s ^ 2 - 4 * M.s * M.v + 6 * M.s + 8) / (2 * (5 * M.s + 4)) := by
      rw [hw]; field_simp; ring
    have : 0 < 1 - w := by rw [this]; apply pos; nlinarith
    linarith
  have hwv : w < M.v := by
    have : M.v - w = (-M.s ^ 2 + 6 * M.s * M.v - 4 * M.s + 8 * M.v) / (2 * (5 * M.s + 4)) := by
      rw [hw]; field_simp; ring
    have : 0 < M.v - w := by rw [this]; apply pos; nlinarith
    linarith
  have hw2 : M.s < 2 * (M.v - w) := by
    have : 2 * (M.v - w) - M.s = (4 * (M.v - M.s) * (3 * M.s + 4)) / (2 * (5 * M.s + 4)) := by
      rw [hw]; field_simp; ring
    have : 0 < 2 * (M.v - w) - M.s := by rw [this]; apply pos; nlinarith
    linarith
  have hw3 : (2 - M.s) * (w - M.v + M.s) < M.s * (1 - M.s + w) := by
    have : M.s * (1 - M.s + w) - (2 - M.s) * (w - M.v + M.s) =
        (2 * (4 - M.s) * (M.s + 2) * (M.v - M.s)) / (2 * (5 * M.s + 4)) := by
      rw [hw]; field_simp; ring
    have : 0 < M.s * (1 - M.s + w) - (2 - M.s) * (w - M.v + M.s) := by
      rw [this]; apply pos
      have : 0 < 4 - M.s := by linarith
      have : 0 < M.v - M.s := by linarith
      positivity
    linarith
  set a := M.pA_UU w with ha_def
  set b := M.pB_UU w with hb_def
  have hfa : a = (1 - M.v + b + w) / 2 := by rw [ha, hb, hw]; field_simp; ring
  have hfb : b = (w + M.v - M.s + M.s * a) / 2 := by rw [ha, hb, hw]; field_simp; ring
  refine ⟨?_, ?_⟩
  · apply nash_exists M hM w a b hw0 hfa hfb
    · rw [ha]; apply pos; linarith
    · rw [hb]; apply pos; nlinarith
    · have : M.v - b = (M.s ^ 2 + 4 * M.s * M.v + 4 * M.v) / (2 * (5 * M.s + 4)) := by
        rw [hb]; field_simp; ring
      have : 0 < M.v - b := by
        rw [this]; apply pos
        have : 0 < M.v := by linarith
        positivity
      linarith
    · have : M.v - b - M.s * (1 - a) = (2 * (M.s + 2) * (M.v - M.s)) / (2 * (5 * M.s + 4)) := by
        rw [ha, hb]; field_simp; ring
      have : 0 < M.v - b - M.s * (1 - a) := by
        rw [this]; apply pos; have : 0 < M.v - M.s := by linarith
        positivity
      linarith
    · have : 1 - M.v + b - a =
          (-M.s ^ 2 - 4 * M.s * M.v + 3 * M.s - 2 * M.v + 4) / (2 * (5 * M.s + 4)) := by
        rw [ha, hb]; field_simp; ring
      have : 0 < 1 - M.v + b - a := by rw [this]; apply pos; nlinarith
      linarith
    · have : b - w = (2 * (M.s + 2) * (M.v - M.s)) / (2 * (5 * M.s + 4)) := by
        rw [hb, hw]; field_simp; ring
      have : 0 < b - w := by
        rw [this]; apply pos; have : 0 < M.v - M.s := by linarith
        positivity
      linarith
    · have : 2 * (M.v - b) - M.s = (8 * (M.s + 1) * (M.v - M.s)) / (2 * (5 * M.s + 4)) := by
        rw [hb]; field_simp; ring
      have : 0 < 2 * (M.v - b) - M.s := by
        rw [this]; apply pos; have : 0 < M.v - M.s := by linarith
        positivity
      linarith
  · intro pA pB hN
    obtain ⟨e1, e2⟩ := nash_foc M hM w pA pB hw0 hw1 hwv hw2 hw3 hN
    have h4 : 0 < 4 - M.s := by linarith
    have hpa : pA = a := by
      have : pA * (4 - M.s) = a * (4 - M.s) := by
        have : a * (4 - M.s) = 2 - M.s + 3 * w - M.v := by
          rw [ha_def]; unfold Model.pA_UU; field_simp
        rw [this]
        rw [e2] at e1
        linarith
      exact mul_right_cancel₀ h4.ne' this
    refine ⟨hpa, ?_⟩
    rw [e2, hpa, hfb]
