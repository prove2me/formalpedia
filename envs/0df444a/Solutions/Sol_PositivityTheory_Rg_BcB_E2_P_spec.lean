-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:20:09.41442+00:00
-- url     : https://prove2.me/submissions/69c731d1-ec05-4304-ad7c-08fafb91ed53

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_AeZero
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Spec_ae_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P
open PositivityTheory.Rg.BcB.E2.P.Spec
namespace PositivityTheory.Rg.BcB.E2.P
theorem _root_.solution : Gelf → Point → SpecMeas → SpecIso → Spec := by
  classical
  intro hG hP hM hI K _ _ _ B _ _ _ _ R p C₀ ε hp hε
  obtain ⟨S, _, _, _, π, e, hπ, he⟩ := hG K B R
  have hne : ∀ b, ‖e b‖ = ‖R b‖ := fun b => by rw [← hπ, he]
  obtain ⟨s₀, hs₀⟩ := hP B S e p fun b => (hp b).trans (hne b).ge
  let _ : MeasurableSpace S := borel S
  have : BorelSpace S := ⟨rfl⟩

  let gr : S → ℝ := fun s => max 0 (1 - (2 / ε) * ∑ c ∈ C₀, ‖e c s - p c‖)
  have hgr : Continuous gr := by
    refine continuous_const.max (continuous_const.sub (continuous_const.mul ?_))
    exact continuous_finsetSum _ fun c _ => continuous_norm.comp ((e c).continuous.sub continuous_const)
  let g : C(S, ℂ) := ⟨fun s => (gr s : ℂ), Complex.continuous_ofReal.comp hgr⟩
  have hg0 : g s₀ = 1 := by
    simp [g, gr, hs₀]
  have hgne : π g ≠ 0 := by
    intro h
    have h1 : ‖g‖ = 0 := by rw [← hπ, h, norm_zero]
    have h2 := ContinuousMap.norm_coe_le_norm g s₀
    rw [hg0, h1] at h2
    norm_num at h2
  obtain ⟨v, hv⟩ : ∃ v, π g v ≠ 0 := by
    by_contra h
    push Not at h
    exact hgne (ContinuousLinearMap.ext h)
  set w := π g v with hw
  obtain ⟨ν, hνf, hνr, hν⟩ := hM K S π w
  obtain ⟨V, hViso, hVmul⟩ := hI K S π w ν hν
  let χ : S → (B →⋆ₐ[ℂ] ℂ) := fun s => (ContinuousMap.evalStarAlgHom ℂ ℂ s).comp e
  have hχ : ∀ s b, χ s b = e b s := fun s b => rfl
  refine ⟨S, borel S, ν, hνf, χ, V, ⟨?_, ?_, ?_, hViso, ?_⟩, ?_⟩
  · intro h0
    have h1 := hν 1
    rw [h0, integral_zero_measure, map_one, ContinuousLinearMap.one_apply] at h1
    exact hv (inner_self_eq_zero.1 h1.symm)
  · intro b
    simp only [hχ]
    exact (e b).continuous.measurable
  · intro b s
    rw [hχ, ← hne]
    exact ContinuousMap.norm_coe_le_norm _ _
  · intro b h h' hh
    rw [← he]
    exact hVmul (e b) h h' (by simpa only [hχ] using hh)
  · rw [Filter.eventually_all_finset]
    intro c hc
    let tr : S → ℝ := fun s => max 0 (‖e c s - p c‖ - ε)
    have htr : Continuous tr :=
      continuous_const.max ((continuous_norm.comp ((e c).continuous.sub continuous_const)).sub continuous_const)
    let t : C(S, ℂ) := ⟨fun s => (tr s : ℂ), Complex.continuous_ofReal.comp htr⟩
    have htg : t * g = 0 := by
      ext s
      simp only [ContinuousMap.mul_apply, ContinuousMap.zero_apply, t, g, ContinuousMap.coe_mk]
      rcases le_or_gt (‖e c s - p c‖) ε with h | h
      · have : tr s = 0 := max_eq_left (by linarith)
        simp [this]
      · have hs : ‖e c s - p c‖ ≤ ∑ c ∈ C₀, ‖e c s - p c‖ :=
          Finset.single_le_sum (f := fun c => ‖e c s - p c‖) (fun _ _ => norm_nonneg _) hc
        have h2 : 2 < (2 / ε) * ∑ c ∈ C₀, ‖e c s - p c‖ := by
          rw [div_mul_eq_mul_div, lt_div_iff₀ hε]
          nlinarith
        have : gr s = 0 := max_eq_left (by linarith)
        simp [this]
    have hint : ∫ s, (tr s : ℂ) ∂ν = 0 := by
      have h1 := hν t
      have h2 : π t w = 0 := by
        rw [hw, ← ContinuousLinearMap.mul_apply, ← map_mul, htg, map_zero, ContinuousLinearMap.zero_apply]
      rw [h2, inner_zero_right] at h1
      exact h1
    filter_upwards [ae_zero ν tr htr (fun s => le_max_left _ _) hint] with s hs
    rw [hχ]
    have : ‖e c s - p c‖ - ε ≤ 0 := max_eq_left_iff.1 hs
    linarith
end PositivityTheory.Rg.BcB.E2.P
