-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.molli_submean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:49:23.116258+00:00
-- url     : https://prove2.me/submissions/7ecd4f52-73e1-40bf-9ffd-55d29ac8eb9b

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Theorems.Thm_ReciprocityTheory_AnForm_A_circle_fubini
import Theorems.Thm_ReciprocityTheory_AnForm_A_phiC
import Theorems.Thm_ReciprocityTheory_AnForm_A_molli_eq_C
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrable_kC
import Theorems.Thm_ReciprocityTheory_AnForm_A_norm_lt_of_scaled_ne_zero
import Theorems.Thm_ReciprocityTheory_AnForm_A_scaled_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_scaled_hasCompactSupport
import Theorems.Thm_ReciprocityTheory_AnForm_A_scaled_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set Real
open scoped ContDiff
noncomputable section
variable {D : ℕ}
variable (ρ : Mollifier D) {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (hU : IsOpen U) (hφ : IsPsh U φ) {ε : ℝ} (hε : 0 < ε)
    {z w : Fin D → ℂ} (hd : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ shrink U ε) :
    molli ρ ε φ z ≤ circleAverage (fun ζ : ℂ => molli ρ ε φ (z + ζ • w)) 0 1 := by
  set C : Set (Fin D → ℂ) :=
    (fun q : ℂ × (Fin D → ℂ) => z + q.1 • w + q.2) '' (closedBall 0 1 ×ˢ closedBall 0 ε) with hCdef
  have hC : IsCompact C :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image (by fun_prop)
  have hball : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → closedBall (z + ζ • w) ε ⊆ C := by
    intro ζ hζ x hx
    refine ⟨(ζ, x - (z + ζ • w)), ⟨by simpa using hζ, ?_⟩, by simp⟩
    rw [mem_closedBall, dist_eq_norm, sub_zero, ← dist_eq_norm]
    exact hx
  have hCU : C ⊆ U := by
    rintro _ ⟨⟨ζ, v⟩, ⟨hζ, hv⟩, rfl⟩
    refine hd ζ (by simpa using hζ) ?_
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    simpa using hv
  obtain ⟨hm, hi⟩ := phiC hU hφ hC hCU
  have hP : Continuous (Function.uncurry fun (ζ : ℂ) (y : Fin D → ℂ) => z + ζ • w - y) :=
    (continuous_const.add (continuous_fst.smul continuous_const)).sub continuous_snd
  have hPm : ∀ ζ : ℂ, ‖ζ‖ = 1 → MeasurePreserving (fun y : Fin D → ℂ => z + ζ • w - y) ∧
      MeasurableEmbedding (fun y : Fin D → ℂ => z + ζ • w - y) := fun ζ _ =>
    ⟨Measure.measurePreserving_sub_left volume _, (Homeomorph.subLeft _).measurableEmbedding⟩
  obtain ⟨hFint, hF⟩ := circle_fubini hm hi (scaled_contDiff ρ ε).continuous
    (scaled_hasCompactSupport ρ hε) hP hPm
  have hcirc : ∀ ζ ∈ sphere (0 : ℂ) |1|,
      (∫ y, ρ.scaled ε y * C.indicator φ (z + ζ • w - y)) = molli ρ ε φ (z + ζ • w) := by
    intro ζ hζ
    have hζ' : ‖ζ‖ ≤ 1 := by simp at hζ; linarith
    rw [molli_eq_C ρ hε (hball ζ hζ')]
  rw [circleAverage_congr_sphere hcirc] at hF
  have h0 : closedBall z ε ⊆ C := by simpa using hball 0 (by simp)
  rw [← hF, molli_eq_C ρ hε h0]
  refine integral_mono (integrable_kC ρ hε hi z) hFint fun y => ?_
  by_cases hy : ρ.scaled ε y = 0
  · simp [hy]
  refine mul_le_mul_of_nonneg_left ?_ (scaled_nonneg ρ hε y)
  have hyε := (norm_lt_of_scaled_ne_zero ρ hε hy).le
  have hin : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z - y + ζ • w ∈ C := by
    intro ζ hζ
    refine hball ζ hζ ?_
    rw [mem_closedBall, dist_eq_norm, show z - y + ζ • w - (z + ζ • w) = -y by abel, norm_neg]
    exact hyε
  obtain ⟨-, hmean⟩ := hφ.2 (z - y) w (fun ζ hζ => hCU (hin ζ hζ))
  have h00 : z - y ∈ C := by simpa using hin 0 (by simp)
  rw [indicator_of_mem h00]
  refine hmean.trans (le_of_eq (circleAverage_congr_sphere fun ζ hζ => ?_))
  have hζ' : ‖ζ‖ ≤ 1 := by simp at hζ; linarith
  show φ (z - y + ζ • w) = C.indicator φ (z + ζ • w - y)
  rw [show z + ζ • w - y = z - y + ζ • w by abel, indicator_of_mem (hin ζ hζ')]
end ReciprocityTheory.AnForm.A
