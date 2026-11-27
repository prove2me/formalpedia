-- Prove2me | solution 1 for ThinFlowSP.Breakpoints.Supplement.lemma_23
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:24:20.921794+00:00
-- url     : https://prove2.me/submissions/afd2dc91-07bc-4a4b-b897-f03581504677

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Supplement_RightMonotone

open MeasureTheory

open ThinFlowSP
open ThinFlowSP.Breakpoints
open ThinFlowSP.Breakpoints.Supplement

theorem solution (g : ℝ → ℝ) (hg : LocallyIntegrable g) (hrm : RightMonotone g)
    (hG : ∀ δ > 0, ∃ ξ ∈ Set.Ioo (0 : ℝ) δ, 0 < ∫ x in (0 : ℝ)..ξ, g x) :
    ∃ ε > 0, (∀ᵐ x, x ∈ Set.Ioo (0 : ℝ) ε → 0 < g x) ∧
      ∀ ξ ∈ Set.Ioo (0 : ℝ) ε, 0 < ∫ x in (0 : ℝ)..ξ, g x := by
        have hII : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
          (hg.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
        -- nonpositivity
        have hnp : ∀ (Z : Set ℝ), volume Z = 0 → ∀ ξ : ℝ, 0 < ξ →
            (∀ y ∈ Set.Ioc (0:ℝ) ξ, y ∉ Z → g y ≤ 0) → ∫ x in (0:ℝ)..ξ, g x ≤ 0 := by
          intro Z hZ ξ hξ h
          rw [intervalIntegral.integral_of_le hξ.le]
          apply integral_nonpos_of_ae
          rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
          filter_upwards [measure_eq_zero_iff_ae_notMem.mp hZ] with y hy hyI
          exact h y hyI hy
        -- positivity
        have hpos : ∀ (Z : Set ℝ), volume Z = 0 → ∀ ε : ℝ, 0 < ε →
            (∀ y ∈ Set.Ioo (0:ℝ) ε, y ∉ Z → 0 < g y) →
            (∀ᵐ x, x ∈ Set.Ioo (0 : ℝ) ε → 0 < g x) ∧
            ∀ ξ ∈ Set.Ioo (0 : ℝ) ε, 0 < ∫ x in (0 : ℝ)..ξ, g x := by
          intro Z hZ ε hε h
          refine ⟨?_, ?_⟩
          · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hZ] with y hy hyI
            exact h y hyI hy
          · intro ξ hξ
            rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' _ (hII 0 ξ)]
            · refine ⟨hξ.1, ?_⟩
              have hsub : Set.Ioo (0:ℝ) ξ \ Z ⊆ Function.support g ∩ Set.Ioc 0 ξ := by
                intro y hy
                exact ⟨(h y ⟨hy.1.1, hy.1.2.trans hξ.2⟩ hy.2).ne', hy.1.1, hy.1.2.le⟩
              refine lt_of_lt_of_le ?_ (measure_mono hsub)
              rw [measure_diff_null hZ, Real.volume_Ioo]
              simpa using hξ.1
            · rw [Set.uIoc_of_le hξ.1.le, Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
              filter_upwards [measure_eq_zero_iff_ae_notMem.mp hZ] with y hy hyI
              exact (h y ⟨hyI.1, lt_of_le_of_lt hyI.2 hξ.2⟩ hy).le
        obtain ⟨ε0, hε0, hmono⟩ := hrm 0
        rw [zero_add] at hmono
        rcases hmono with ⟨Z, hZ, hZm⟩ | ⟨Z, hZ, hZm⟩
        · -- nondecreasing
          refine ⟨ε0, hε0, hpos Z hZ ε0 hε0 ?_⟩
          intro a ha haZ
          by_contra hneg
          push_neg at hneg
          obtain ⟨ξ, hξ, hint⟩ := hG a ha.1
          have := hnp Z hZ ξ hξ.1 (fun y hy hyZ =>
            (hZm y ⟨⟨hy.1.le, hy.2.trans (hξ.2.le.trans ha.2.le)⟩, hyZ⟩
              a ⟨⟨ha.1.le, ha.2.le⟩, haZ⟩ (hy.2.trans hξ.2.le)).trans hneg)
          linarith
        · -- nonincreasing
          obtain ⟨ξ0, hξ0, hint⟩ := hG ε0 hε0
          have : ∃ x ∈ Set.Ioc (0:ℝ) ξ0, x ∉ Z ∧ 0 < g x := by
            by_contra hc
            push_neg at hc
            have := hnp Z hZ ξ0 hξ0.1 hc
            linarith
          obtain ⟨x, hx, hxZ, hgx⟩ := this
          refine ⟨x, hx.1, hpos Z hZ x hx.1 ?_⟩
          intro y hy hyZ
          exact lt_of_lt_of_le hgx (hZm y ⟨⟨hy.1.le, hy.2.le.trans (hx.2.trans hξ0.2.le)⟩, hyZ⟩
            x ⟨⟨hx.1.le, hx.2.trans hξ0.2.le⟩, hxZ⟩ hy.2.le)
