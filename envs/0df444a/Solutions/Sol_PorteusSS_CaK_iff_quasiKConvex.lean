-- Prove2me | solution 1 for PorteusSS.CaK_iff_quasiKConvex
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:59:02.831965+00:00
-- url     : https://prove2.me/submissions/7b7cfe74-a027-4080-b2e3-76a7020c4b34

import Mathlib
import Definitions.Def_PorteusSS_Functions

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-- Quasi-`K`-convexity in "betweenness" form: `x ≤ z ≤ y → f z ≤ max (f x) (f y + K)`. -/
theorem aux_cak_qkc_between {f : ℝ → ℝ} {K : ℝ} (h : QuasiKConvexOn f K univ)
    {x z y : ℝ} (hxz : x ≤ z) (hzy : z ≤ y) : f z ≤ max (f x) (f y + K) := by
  rcases eq_or_lt_of_le (hxz.trans hzy) with hxy | hxy
  · have hzx : z = x := le_antisymm (by rw [hxy]; exact hzy) hxz
    rw [hzx]
    exact le_max_left _ _
  · have hpos : 0 < y - x := sub_pos.mpr hxy
    have hne : y - x ≠ 0 := hpos.ne'
    have key := h.2 x (mem_univ _) y (mem_univ _) (hxz.trans hzy) ((y - z) / (y - x))
      (div_nonneg (sub_nonneg.mpr hzy) hpos.le)
      ((div_le_one hpos).mpr (by linarith))
    have heq : (y - z) / (y - x) * x + (1 - (y - z) / (y - x)) * y = z := by
      field_simp
      ring
    rw [heq] at key
    exact key

theorem aux_cak_forward {K : ℝ} {f : ℝ → ℝ} {a : ℝ} (h : CaK a K f) :
    QuasiKConvexOn f K univ := by
  obtain ⟨_, I, hI, _, _, hanti, hnk, _⟩ := h
  have hdown : ∀ x z : ℝ, x ≤ z → z ∈ I → x ∈ I := by
    rcases hI with rfl | rfl
    · intro x z hxz hz
      exact lt_of_le_of_lt hxz hz
    · intro x z hxz hz
      exact le_trans hxz hz
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy l hl0 hl1
  have hxz : x ≤ l * x + (1 - l) * y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl1) (sub_nonneg.mpr hxy)]
  have hzy : l * x + (1 - l) * y ≤ y := by
    nlinarith [mul_nonneg hl0 (sub_nonneg.mpr hxy)]
  by_cases hzI : l * x + (1 - l) * y ∈ I
  · exact le_trans (hanti (hdown x _ hxz hzI) hzI hxz) (le_max_left _ _)
  · have hyI : y ∉ I := fun hy => hzI (hdown _ y hzy hy)
    exact le_trans (hnk _ hzI y hyI hzy) (le_max_right _ _)

theorem aux_cak_backward {K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ} (hq : QuasiKConvexOn f K univ)
    (hpc : PiecewiseContinuousOn f univ) (hpf : PFIntegrable f)
    (ht : Tendsto f (cocompact ℝ) atTop) : ∃ a : ℝ, CaK a K f := by
  have hev1 : ∀ᶠ x in atBot, f 0 + K < f x :=
    (ht.mono_left atBot_le_cocompact).eventually_gt_atTop _
  have hev2 : ∀ᶠ x in atTop, f 0 < f x :=
    (ht.mono_left atTop_le_cocompact).eventually_gt_atTop _
  obtain ⟨T, hT⟩ := eventually_atBot.mp hev1
  obtain ⟨T', hT'⟩ := eventually_atTop.mp hev2
  set B : Set ℝ := {x | ∃ y, x ≤ y ∧ f y + K < f x} with hBdef
  have hB : ∀ x ∈ B, ∀ w, w ≤ x → f x ≤ f w := by
    rintro x ⟨y, hxy, hlt⟩ w hwx
    have hm := aux_cak_qkc_between hq hwx hxy
    rcases le_max_iff.mp hm with h | h
    · exact h
    · exact absurd h (not_le.mpr hlt)
  have hne : B.Nonempty := ⟨min T 0, 0, min_le_right _ _, hT _ (min_le_left _ _)⟩
  have hbdd : BddAbove B := by
    refine ⟨max T' 0, ?_⟩
    intro x hx
    by_contra hcon0
    have hcon := not_le.mp hcon0
    have h1 : T' ≤ x := le_trans (le_max_left _ _) hcon.le
    have h2 : (0:ℝ) ≤ x := le_trans (le_max_right _ _) hcon.le
    have h3 := hB x hx 0 h2
    have h4 := hT' x h1
    linarith
  have hanti : AntitoneOn f (Iio (sSup B)) := by
    intro w _ z hz hwz
    obtain ⟨x, hxB, hzx⟩ := exists_lt_of_lt_csSup hne hz
    obtain ⟨y, hxy, hlt⟩ := hxB
    by_cases hc : f y + K < f z
    · exact hB z ⟨y, hzx.le.trans hxy, hc⟩ w hwz
    · have hc := not_lt.mp hc
      have := hB x ⟨y, hxy, hlt⟩ w (hwz.trans hzx.le)
      linarith
  by_cases hbB : sSup B ∈ B
  · refine ⟨sSup B, hK, Iic (sSup B), Or.inr rfl, hpc, hpf, ?_, ?_, ht⟩
    · intro w _ z hz hwz
      rcases eq_or_lt_of_le (show z ≤ sSup B from hz) with hzb | hzb
      · rw [hzb]
        exact hB _ hbB w (hwz.trans hzb.le)
      · exact hanti (show w < sSup B from lt_of_le_of_lt hwz hzb) hzb hwz
    · intro x hx y _ hxy
      by_contra hcon0
      have hcon := not_le.mp hcon0
      exact hx (le_csSup hbdd ⟨y, hxy, hcon⟩)
  · refine ⟨sSup B, hK, Iio (sSup B), Or.inl rfl, hpc, hpf, hanti, ?_, ht⟩
    intro x hx y _ hxy
    by_contra hcon0
    have hcon := not_le.mp hcon0
    have hxB : x ∈ B := ⟨y, hxy, hcon⟩
    have h1 : x ≤ sSup B := le_csSup hbdd hxB
    have h2 : sSup B ≤ x := not_lt.mp hx
    have h3 : x = sSup B := le_antisymm h1 h2
    rw [h3] at hxB
    exact hbB hxB

end PorteusSS

open PorteusSS
open MeasureTheory Filter Topology Set

theorem solution (K : ℝ) (hK : 0 ≤ K) (f : ℝ → ℝ) :
    (∀ a : ℝ, CaK a K f →
      QuasiKConvexOn f K univ ∧ PiecewiseContinuousOn f univ ∧ PFIntegrable f ∧
        Tendsto f (cocompact ℝ) atTop) ∧
    (QuasiKConvexOn f K univ ∧ PiecewiseContinuousOn f univ ∧ PFIntegrable f ∧
        Tendsto f (cocompact ℝ) atTop → ∃ a : ℝ, CaK a K f) := by
  refine ⟨?_, ?_⟩
  · intro a h
    have hq := aux_cak_forward h
    obtain ⟨_, I, _, hpc, hpf, _, _, ht⟩ := h
    exact ⟨hq, hpc, hpf, ht⟩
  · rintro ⟨hq, hpc, hpf, ht⟩
    exact aux_cak_backward hK hq hpc hpf ht
