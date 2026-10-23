-- Prove2me | solution 1 for PersPricingDist.UniformA.up_leader_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T18:53:41.902159+00:00
-- url     : https://prove2.me/submissions/1ea43ae2-3719-4ddd-b866-48004213fb78

import Mathlib
import Definitions.Def_PersPricingDist_UniformA_Setting

open PersPricingDist.UniformA MeasureTheory

namespace PPD1UPL

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

lemma demand_eq (M : Model) (P : ℝ → Prop) (a b : ℝ) (hab : a ≤ b)
    (h1 : ∀ x, 0 ≤ x → x ≤ M.X → P x → a ≤ x ∧ x ≤ b)
    (h2 : ∀ x, a < x → x < b → 0 ≤ x ∧ x ≤ M.X ∧ P x) : M.demand P = b - a := by
  unfold Model.demand
  have hsub : {x : ℝ | x ∈ Set.Icc 0 M.X ∧ P x} ⊆ Set.Icc a b := by
    rintro x ⟨⟨h0, h1'⟩, hP⟩
    exact h1 x h0 h1' hP
  have hsup : Set.Ioo a b ⊆ {x : ℝ | x ∈ Set.Icc 0 M.X ∧ P x} := by
    rintro x ⟨ha, hb⟩
    obtain ⟨p1, p2, p3⟩ := h2 x ha hb
    exact ⟨⟨p1, p2⟩, p3⟩
  have e1 := measure_mono (μ := volume) hsub
  have e2 := measure_mono (μ := volume) hsup
  rw [Real.volume_Icc] at e1
  rw [Real.volume_Ioo] at e2
  rw [le_antisymm e1 e2, ENNReal.toReal_ofReal (by linarith)]

lemma max_pos_eq {a : ℝ} (h : 0 < max a 0) : max a 0 = a := by
  rcases le_total a 0 with h' | h'
  · rw [max_eq_right h'] at h; exact absurd h (lt_irrefl 0)
  · exact max_eq_left h'

/-- Generic analysis of A's leader problem at a wholesale price `w`. -/
lemma leader_generic (M : Model) (hM : M.Standing) (w : ℝ) (hw : 0 < w)
    (hw1 : M.s * (1 - (w + (1 - M.v) / 2)) ≤ M.v - w) (hw2 : M.s ≤ 2 * (M.v - w)) :
    let a := w + (1 - M.v) / 2
    let xB := (M.v - w) / M.s
    let Pi := (1 - M.v) ^ 2 / (4 * (1 - M.s)) + w * xB
    M.profA_UP w a = Pi ∧ ∀ p, p ≠ a → M.profA_UP w p < Pi := by
  intro a xB Pi
  have hs := hM.s_pos
  have hsv := hM.s_lt_v
  have hv1 := hM.v_lt_one
  have h1s : 0 < 1 - M.s := by linarith
  have hX : M.v ≤ M.s * M.X := by
    have := hM.market_large
    rw [div_le_iff₀ hs] at this; linarith
  have hX1 : 1 ≤ M.X := by
    have : M.s * 1 ≤ M.s * M.X := by linarith
    exact le_of_mul_le_mul_left this hs
  have hxB : M.s * xB = M.v - w := by
    simp only [xB]; field_simp
  have hxBX : xB ≤ M.X := by
    have : M.s * xB ≤ M.s * M.X := by linarith
    exact le_of_mul_le_mul_left this hs
  have hxBh : 1 / 2 ≤ xB := by
    have : M.s * (1 / 2) ≤ M.s * xB := by linarith
    exact le_of_mul_le_mul_left this hs
  -- B's set
  have hBset : ∀ p x, M.buysB_UP w p x →
      1 - M.v - p + w < (1 - M.s) * x ∧ M.s * x < M.v - w := by
    intro p x hB
    simp only [Model.buysB_UP, Model.uA, Model.uB] at hB
    rw [max_lt_iff] at hB
    obtain ⟨hB1, hB2⟩ := hB
    have hpos : 0 < max (M.v - M.s * x) 0 := by linarith
    rw [max_pos_eq hpos] at hB1 hB2
    have := le_max_left (1 - x) 0
    constructor <;> linarith
  have hBx : ∀ p x, M.buysB_UP w p x → x < xB := by
    intro p x hB
    have := (hBset p x hB).2
    rw [← hxB] at this
    exact lt_of_mul_lt_mul_left this hs.le
  -- A's set (for p > 0)
  have hAset : ∀ p x, 0 < p → M.buysA_UP w p x →
      x ≤ 1 - p ∧ (1 - M.s) * x ≤ 1 - M.v - p + w := by
    intro p x hp hA
    simp only [Model.buysA_UP, Model.buysB_UP, Model.uA, Model.uB, not_lt] at hA
    obtain ⟨hA1, hA2⟩ := hA
    have hpos : 0 < max (1 - x) 0 := by linarith
    rw [max_pos_eq hpos] at hA1 hA2
    rw [max_eq_left (by linarith : (0:ℝ) ≤ 1 - x - p)] at hA1
    have := le_max_left (M.v - M.s * x) 0
    constructor <;> linarith
  have hPi : ∀ p, (p - w) * (1 - M.v - p + w) / (1 - M.s) + w * xB
      = Pi - (p - a) ^ 2 / (1 - M.s) := by
    intro p; simp only [Pi, a]; field_simp; ring
  have hgap : 0 < (1 - M.v) ^ 2 / (4 * (1 - M.s)) := by
    have : 0 < 1 - M.v := by linarith
    positivity
  constructor
  · -- exact value
    have hxc : 0 ≤ (1 - M.v - a + w) / (1 - M.s) := by
      apply div_nonneg _ h1s.le; simp only [a]; linarith
    set xc := (1 - M.v - a + w) / (1 - M.s) with hxc_def
    have hxc' : (1 - M.s) * xc = 1 - M.v - a + w := by
      rw [hxc_def]; field_simp
    have ha0 : 0 < a := by simp only [a]; linarith
    have hxc1 : xc ≤ 1 - a := by
      have : (1 - M.s) * xc ≤ (1 - M.s) * (1 - a) := by
        rw [hxc']; simp only [a] at hw1 ⊢; linarith
      exact le_of_mul_le_mul_left this h1s
    have hxcB : xc ≤ xB := by
      have : M.s * (1 - a) ≤ M.s * xB := by rw [hxB]; simpa [a] using hw1
      have := le_of_mul_le_mul_left this hs
      linarith
    have hDA : M.DA_UP w a = xc - 0 := by
      apply demand_eq M _ 0 xc hxc
      · intro x hx0 _ hA
        obtain ⟨_, h2⟩ := hAset a x ha0 hA
        refine ⟨hx0, ?_⟩
        rw [← hxc'] at h2
        exact le_of_mul_le_mul_left h2 h1s
      · intro x hx0 hx1
        refine ⟨hx0.le, by linarith, ?_⟩
        simp only [Model.buysA_UP, Model.buysB_UP, Model.uA, Model.uB, not_lt]
        have e1 : max (1 - x) 0 = 1 - x := max_eq_left (by linarith)
        rw [e1, max_eq_left (by linarith : (0:ℝ) ≤ 1 - x - a)]
        refine ⟨?_, by linarith⟩
        have hsx : M.s * x ≤ M.s * 1 := mul_le_mul_of_nonneg_left (by linarith) hs.le
        have hvx : 0 ≤ M.v - M.s * x := by linarith
        rw [max_eq_left hvx]
        have : (1 - M.s) * x ≤ (1 - M.s) * xc := mul_le_mul_of_nonneg_left hx1.le h1s.le
        linarith
    have hDB : M.DB_UP w a = xB - xc := by
      apply demand_eq M _ xc xB hxcB
      · intro x _ _ hB
        obtain ⟨h1, _⟩ := hBset a x hB
        refine ⟨?_, (hBx a x hB).le⟩
        rw [← hxc'] at h1
        exact (lt_of_mul_lt_mul_left h1 h1s.le).le
      · intro x hx0 hx1
        refine ⟨by linarith, by linarith, ?_⟩
        simp only [Model.buysB_UP, Model.uA, Model.uB]
        have hsx : M.s * x < M.s * xB := mul_lt_mul_of_pos_left hx1 hs
        have hvx : 0 ≤ M.v - M.s * x := by linarith
        have hcx : (1 - M.s) * xc < (1 - M.s) * x := mul_lt_mul_of_pos_left hx0 h1s
        rw [max_eq_left hvx, max_lt_iff]
        constructor
        · rcases le_total (1 - x) 0 with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h]; linarith
        · linarith
    unfold Model.profA_UP
    rw [hDA, hDB]
    have := hPi a
    have e : (a - w) * (1 - M.v - a + w) / (1 - M.s) = (a - w) * xc := by
      rw [hxc_def]; ring
    have e2 : (a - a) ^ 2 / (1 - M.s) = 0 := by simp
    rw [e, e2] at this
    linarith
  · intro p hp
    have hDAnn := demand_nonneg M (M.buysA_UP w p)
    have hDBnn := demand_nonneg M (M.buysB_UP w p)
    unfold Model.profA_UP
    unfold Model.DA_UP Model.DB_UP
    rcases le_or_gt p 0 with hp0 | hp0
    · -- nonpositive price
      have hDB : M.demand (M.buysB_UP w p) ≤ max (xB - 0) 0 := by
        apply demand_le
        intro x hx0 _ hB
        exact ⟨hx0, (hBx p x hB).le⟩
      rw [sub_zero, max_eq_left (by linarith)] at hDB
      have h1 : p * M.demand (M.buysA_UP w p) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hp0 hDAnn
      have h2 : w * M.demand (M.buysB_UP w p) ≤ w * xB := mul_le_mul_of_nonneg_left hDB hw.le
      linarith
    · rcases lt_or_ge (M.v - w) (M.s * (1 - p)) with hc | hc
      · -- A takes everyone up to 1 - p, B sells nothing
        have hp1 : p < 1 - xB := by
          have : M.s * xB < M.s * (1 - p) := by rw [hxB]; exact hc
          have := lt_of_mul_lt_mul_left this hs.le
          linarith
        have hDA : M.demand (M.buysA_UP w p) ≤ max (1 - p - 0) 0 := by
          apply demand_le
          intro x hx0 _ hA
          exact ⟨hx0, (hAset p x hp0 hA).1⟩
        have hDB : M.demand (M.buysB_UP w p) ≤ max (0 - 1) 0 := by
          apply demand_le
          intro x _ _ hB
          obtain ⟨h1, _⟩ := hBset p x hB
          exfalso
          have hx : x < 1 - p := by linarith [hBx p x hB]
          have := mul_lt_mul_of_pos_left hx h1s
          linarith
        rw [max_eq_right (by linarith)] at hDB
        rw [sub_zero, max_eq_left (by linarith)] at hDA
        have hq := hPi (1 - xB)
        have hsq : 0 ≤ (1 - xB - a) ^ 2 / (1 - M.s) := by positivity
        have e : (1 - xB - w) * (1 - M.v - (1 - xB) + w) / (1 - M.s) + w * xB
            = (1 - xB) * xB := by
          have : 1 - M.v - (1 - xB) + w = (1 - M.s) * xB := by linarith
          rw [this]; field_simp; ring
        rw [e] at hq
        have hDB0 : M.demand (M.buysB_UP w p) = 0 := le_antisymm hDB hDBnn
        rw [hDB0]
        have h1 : p * M.demand (M.buysA_UP w p) ≤ p * (1 - p) :=
          mul_le_mul_of_nonneg_left hDA hp0.le
        have h2 : 0 < (xB - p) * (1 - xB - p) := mul_pos (by linarith) (by linarith)
        nlinarith
      · -- interior regime
        set xc := (1 - M.v - p + w) / (1 - M.s) with hxc_def
        have hxc' : (1 - M.s) * xc = 1 - M.v - p + w := by
          rw [hxc_def]; field_simp
        have hxc1 : xc ≤ 1 - p := by
          have : (1 - M.s) * xc ≤ (1 - M.s) * (1 - p) := by rw [hxc']; linarith
          exact le_of_mul_le_mul_left this h1s
        have hxcB : max xc 0 ≤ xB := by
          have : M.s * (1 - p) ≤ M.s * xB := by rw [hxB]; exact hc
          have := le_of_mul_le_mul_left this hs
          apply max_le <;> linarith
        have hDA : M.demand (M.buysA_UP w p) ≤ max (max xc 0 - 0) 0 := by
          apply demand_le
          intro x hx0 _ hA
          obtain ⟨_, h2⟩ := hAset p x hp0 hA
          refine ⟨hx0, ?_⟩
          rw [← hxc'] at h2
          exact le_max_of_le_left (le_of_mul_le_mul_left h2 h1s)
        have hDB : M.demand (M.buysB_UP w p) ≤ max (xB - max xc 0) 0 := by
          apply demand_le
          intro x hx0 _ hB
          obtain ⟨h1, _⟩ := hBset p x hB
          rw [← hxc'] at h1
          exact ⟨max_le (lt_of_mul_lt_mul_left h1 h1s.le).le hx0, (hBx p x hB).le⟩
        rw [sub_zero, max_eq_left (le_max_right _ _)] at hDA
        rw [max_eq_left (by linarith)] at hDB
        have hq := hPi p
        have hsq : 0 < (p - a) ^ 2 / (1 - M.s) := by
          have : p - a ≠ 0 := sub_ne_zero.mpr hp
          positivity
        have h1 := mul_le_mul_of_nonneg_left hDA hp0.le
        have h2 := mul_le_mul_of_nonneg_left hDB hw.le
        rcases le_total xc 0 with hx | hx
        · rw [max_eq_right hx] at h1 h2
          linarith
        · rw [max_eq_left hx] at h1 h2
          have e : (p - w) * (1 - M.v - p + w) / (1 - M.s) = (p - w) * xc := by
            rw [hxc_def]; ring
          rw [e] at hq
          linarith

end PPD1UPL

open PPD1UPL in
theorem solution (M : Model) (hM : M.Standing) :
    M.IsLeaderOptUP M.wUP (M.pA_UP M.wUP) ∧
    (∀ pA : ℝ, M.IsLeaderOptUP M.wUP pA → pA = M.pA_UP M.wUP) := by
  have hs := hM.s_pos
  have hsv := hM.s_lt_v
  have hv1 := hM.v_lt_one
  have hw : 0 < M.wUP := by
    unfold Model.wUP
    have : 0 < 1 + M.v := by linarith
    positivity
  have hw' : M.wUP * (2 * (1 + M.s)) = M.s * (1 + M.v) := by
    unfold Model.wUP; field_simp
  have hw1 : M.s * (1 - (M.wUP + (1 - M.v) / 2)) ≤ M.v - M.wUP := by nlinarith
  have hw2 : M.s ≤ 2 * (M.v - M.wUP) := by nlinarith
  obtain ⟨hex, hlt⟩ := leader_generic M hM M.wUP hw hw1 hw2
  have ha : M.pA_UP M.wUP = M.wUP + (1 - M.v) / 2 := rfl
  refine ⟨?_, ?_⟩
  · intro p
    rw [ha, hex]
    by_cases hp : p = M.wUP + (1 - M.v) / 2
    · rw [hp, hex]
    · exact (hlt p hp).le
  · intro pA hopt
    by_contra hne
    rw [ha] at hne
    have h1 := hlt pA hne
    have h2 := hopt (M.wUP + (1 - M.v) / 2)
    rw [hex] at h2
    linarith
