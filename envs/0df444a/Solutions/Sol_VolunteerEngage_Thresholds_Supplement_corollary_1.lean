-- Prove2me | solution 1 for VolunteerEngage.Thresholds.Supplement.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:09:05.051102+00:00
-- url     : https://prove2.me/submissions/5f184f8c-82d0-4c9d-bcae-7a20edb00bcc

import Mathlib
import Definitions.Def_VolunteerEngage_Thresholds_Supplement_RelativeValue
import Definitions.Def_VolunteerEngage_Thresholds_Supplement_BellmanF

open VolunteerEngage
open VolunteerEngage.Thresholds
open VolunteerEngage.Thresholds.Supplement

/-- Corollary 1, p. 22: all of (59)–(60), including an attained minimum. -/
theorem solution (M : Model) (hM : M.Standing) (β : ℝ) (v v' : ℝ → ℝ)
    (hv : IsBellmanSol M β v v') :
    IsFBellmanSol M β (relativeValue M v) (fun z => v z - M.p) v' := by
      obtain ⟨hβ, hcont', hder, hbell, hv0, hmono, hlim⟩ := hv
      obtain ⟨hL, hθ0, hη, -, -, -, -, -, -⟩ := hM
      have hvc : ContinuousOn v (Set.Ici 0) := fun x hx => (hder x hx).continuousWithinAt
      set vh : ℝ → ℝ := fun s => v (max s 0) with hvh
      have hvhc : Continuous vh := by
        refine hvc.comp_continuous (continuous_id.max continuous_const) ?_
        intro x; exact le_max_right x 0
      have hθle : M.θ0 ≤ M.θ M.L := by
        unfold Model.θ
        have : 0 ≤ ∑ i ∈ Finset.Icc 1 M.L, M.η i :=
          Finset.sum_nonneg (fun i hi => (hη i hi).le)
        linarith
      have hcostc : Continuous (cost M) := by
        unfold cost
        fun_prop
      have hphi : ∀ y : ℝ, (∃ x0 ∈ Set.Icc M.θ0 (M.θ M.L), y * x0 - cost M x0 = phi M y) ∧
          ∀ x ∈ Set.Icc M.θ0 (M.θ M.L), y * x - cost M x ≤ phi M y := by
        intro y
        have hK : IsCompact ((fun x => y * x - cost M x) '' Set.Icc M.θ0 (M.θ M.L)) :=
          (isCompact_Icc).image (by fun_prop)
        have hne : ((fun x => y * x - cost M x) '' Set.Icc M.θ0 (M.θ M.L)).Nonempty :=
          (Set.nonempty_Icc.mpr hθle).image _
        refine ⟨?_, ?_⟩
        · obtain ⟨x0, hx0, h⟩ := hK.sSup_mem hne
          exact ⟨x0, hx0, h⟩
        · intro x hx
          exact le_csSup hK.bddAbove (Set.mem_image_of_mem _ hx)
      refine ⟨hβ, hcont', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro w hw
        have hw' : (0:ℝ) ≤ w := hw
        have h1 : HasDerivAt (fun u => ∫ s in (0:ℝ)..u, vh s) (vh w) w :=
          intervalIntegral.integral_hasDerivAt_right (hvhc.intervalIntegrable _ _)
            hvhc.aestronglyMeasurable.stronglyMeasurableAtFilter hvhc.continuousAt
        have h2 : HasDerivAt (fun u => (∫ s in (0:ℝ)..u, vh s) - M.p * u) (vh w - M.p) w := by
          have := h1.sub ((hasDerivAt_id w).const_mul M.p)
          have h4 := this.const_mul (1:ℝ)
          simp only [one_mul, mul_one] at h4
          exact h4
        have h3 : vh w = v w := by simp [hvh, max_eq_left hw']
        show HasDerivWithinAt (relativeValue M v) (v w - M.p) (Set.Ici 0) w
        rw [← h3]
        refine h2.hasDerivWithinAt.congr ?_ ?_
        · intro z hz
          have hz' : (0:ℝ) ≤ z := hz
          simp only [relativeValue]
          congr 1
          refine intervalIntegral.integral_congr ?_
          intro s hs
          rw [Set.uIcc_of_le hz'] at hs
          simp [hvh, max_eq_left hs.1]
        · simp only [relativeValue]
          congr 1
          refine intervalIntegral.integral_congr ?_
          intro s hs
          rw [Set.uIcc_of_le hw'] at hs
          simp [hvh, max_eq_left hs.1]
      · intro w hw
        exact (hder w hw).sub_const _
      · intro w hw
        obtain ⟨⟨x0, hx0, hx0e⟩, hle⟩ := hphi (M.p - v w)
        have hb := hbell w hw
        refine ⟨⟨x0, hx0, ?_⟩, ?_⟩
        · simp only
          rw [hb, ← hx0e]; ring
        · rintro _ ⟨x, hx, rfl⟩
          have := hle x hx
          simp only
          rw [hb]; nlinarith
      · simp [hv0]
      · intro a ha b hb hab
        have := hmono ha hb hab
        simp only; linarith
      · have := hlim.sub_const M.p
        simpa using this
