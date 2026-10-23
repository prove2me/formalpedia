-- Prove2me | solution 1 for PersPricingDist.UniformA.uu_profit_12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T19:17:06.299712+00:00
-- url     : https://prove2.me/submissions/2f51549c-691b-4f4a-a2d9-66ed2ec640fa

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

end
end PPD1UU

open PPD1UU in
lemma ppd1_uu_exact (M : Model) (hM : M.Standing) :
    M.DA_UU (M.pA_UU M.wUU) (M.pB_UU M.wUU) =
      (2 * (2 - M.v) + M.s * (3 - 4 * M.v - M.s)) / (2 * (4 + 5 * M.s) * (1 - M.s)) ∧
    M.DB_UU (M.pA_UU M.wUU) (M.pB_UU M.wUU) =
      ((2 + M.s) * (M.v - M.s)) / (M.s * (4 + 5 * M.s) * (1 - M.s)) ∧
    M.pA_UU M.wUU = (7 * M.s - 2 * M.v + 4) / (2 * (5 * M.s + 4)) ∧
    M.pB_UU M.wUU = (4 * M.v + 6 * M.s * M.v - M.s ^ 2) / (2 * (5 * M.s + 4)) := by
  have hs := hM.s_pos
  have hsv := hM.s_lt_v
  have hv1 := hM.v_lt_one
  have hD : 0 < 2 * (5 * M.s + 4) := by linarith
  have hD' : 2 * (5 * M.s + 4) ≠ 0 := hD.ne'
  have h4s : (4 : ℝ) - M.s ≠ 0 := by linarith
  have h1s : (1 : ℝ) - M.s ≠ 0 := by linarith
  have hw : M.wUU = M.s * (M.s + 4 * M.v + 4) / (2 * (5 * M.s + 4)) := by
    unfold Model.wUU; field_simp; ring
  have ha : M.pA_UU M.wUU = (7 * M.s - 2 * M.v + 4) / (2 * (5 * M.s + 4)) := by
    unfold Model.pA_UU; rw [hw]; field_simp; ring
  have hb : M.pB_UU M.wUU = (4 * M.v + 6 * M.s * M.v - M.s ^ 2) / (2 * (5 * M.s + 4)) := by
    unfold Model.pB_UU; rw [hw]; field_simp; ring
  set a := M.pA_UU M.wUU
  set b := M.pB_UU M.wUU
  have pos : ∀ P : ℝ, 0 < P → 0 < P / (2 * (5 * M.s + 4)) := fun P hP => div_pos hP hD
  have ha0 : 0 < a := by rw [ha]; apply pos; linarith
  have hb0 : 0 < b := by rw [hb]; apply pos; nlinarith
  have hbv : b < M.v := by
    have : M.v - b = (M.s ^ 2 + 4 * M.s * M.v + 4 * M.v) / (2 * (5 * M.s + 4)) := by
      rw [hb]; field_simp; ring
    have : 0 < M.v - b := by
      rw [this]; apply pos
      have : 0 < M.v := by linarith
      positivity
    linarith
  have h1 : M.s * (1 - a) ≤ M.v - b := by
    have : M.v - b - M.s * (1 - a) = (2 * (M.s + 2) * (M.v - M.s)) / (2 * (5 * M.s + 4)) := by
      rw [ha, hb]; field_simp; ring
    have : 0 < M.v - b - M.s * (1 - a) := by
      rw [this]; apply pos; have : 0 < M.v - M.s := by linarith
      positivity
    linarith
  have h2 : a ≤ 1 - M.v + b := by
    have : 1 - M.v + b - a =
        (-M.s ^ 2 - 4 * M.s * M.v + 3 * M.s - 2 * M.v + 4) / (2 * (5 * M.s + 4)) := by
      rw [ha, hb]; field_simp; ring
    have : 0 < 1 - M.v + b - a := by rw [this]; apply pos; nlinarith
    linarith
  have hab : 1 - a ≤ xb M b := by
    have := xb_mul M hM b
    have : M.s * (1 - a) ≤ M.s * xb M b := by linarith
    exact le_of_mul_le_mul_left this hs
  have hxi0 : 0 ≤ xi M a b := by
    unfold xi; exact div_nonneg (by linarith) (by linarith)
  have hxi1 := (xi_le_iff M hM a b).2 hab
  have hDA : M.DA_UU a b = xi M a b := by
    have h3 := DA_le M hM a b ha0
    have h4 := DA_ge M hM a b ha0
    rw [max_eq_left hxi0] at h3
    rw [min_eq_left hxi1] at h4
    exact le_antisymm h3 h4
  have hDB : M.DB_UU a b = xb M b - xi M a b := by
    have h3 := DB_le M hM a b hb0
    have h4 := DB_ge M hM a b ha0 hb0 hbv.le
    rw [max_eq_left hxi0] at h3 h4
    rw [max_eq_left (by linarith)] at h3
    exact le_antisymm h3 h4
  refine ⟨?_, ?_, ha, hb⟩
  · rw [hDA]; unfold xi; rw [ha, hb]; field_simp; ring
  · rw [hDB]; unfold xi xb; rw [ha, hb]; field_simp; ring

theorem solution (M : Model) (hM : M.Standing) :
    M.indUU (M.pA_UU M.wUU) (M.pB_UU M.wUU) =
      (M.s * (5 * M.s + 4 - M.s ^ 2) +
        4 * M.v * (1 + M.s) * (M.v - 2 * M.s)) /
        (4 * M.s * (1 - M.s) * (4 + 5 * M.s)) ∧
    M.indUU (M.pA_UU M.wUU) (M.pB_UU M.wUU) - (1 : ℝ) / 4 =
      ((1 + M.s) * (M.v - M.s) ^ 2) /
        (M.s * (4 + 5 * M.s) * (1 - M.s)) ∧
    0 < M.indUU (M.pA_UU M.wUU) (M.pB_UU M.wUU) - (1 : ℝ) / 4 := by
  obtain ⟨h1, h2, ha, hb⟩ := ppd1_uu_exact M hM
  have hs := hM.s_pos
  have hsv := hM.s_lt_v
  have hv1 := hM.v_lt_one
  have h1s : (1 : ℝ) - M.s ≠ 0 := by linarith
  have h45 : (4 : ℝ) + 5 * M.s ≠ 0 := by linarith
  have h54 : (5 : ℝ) * M.s + 4 ≠ 0 := by linarith
  have hs0 : M.s ≠ 0 := hs.ne'
  have e : M.indUU (M.pA_UU M.wUU) (M.pB_UU M.wUU) =
      (M.s * (5 * M.s + 4 - M.s ^ 2) +
        4 * M.v * (1 + M.s) * (M.v - 2 * M.s)) /
        (4 * M.s * (1 - M.s) * (4 + 5 * M.s)) := by
    unfold Model.indUU
    rw [h1, h2, ha, hb]
    field_simp; ring
  have e2 : M.indUU (M.pA_UU M.wUU) (M.pB_UU M.wUU) - (1 : ℝ) / 4 =
      ((1 + M.s) * (M.v - M.s) ^ 2) / (M.s * (4 + 5 * M.s) * (1 - M.s)) := by
    rw [e]; field_simp; ring
  refine ⟨e, e2, ?_⟩
  rw [e2]
  have : 0 < 1 - M.s := by linarith
  have : M.v - M.s ≠ 0 := by linarith
  positivity
