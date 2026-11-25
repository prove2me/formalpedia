-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RatPosPartLocal_ratPosDens_eq_86bec30a717e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:48:02.024336+00:00
-- url     : https://prove2.me/submissions/c5711711-860b-4070-90f9-adb38c2d1a15

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatPosPartLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_maDens_congr_of_eventuallyEq_290b4083a720


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.RatPosPartLocal
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.RatPosPartLocal
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} {U : Set (Fin d → ℂ)} {W E : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hsd : DifferentiableOn ℂ s U)
    (hsec : ∀ y ∈ U, s y ∈ zeroSet J ∧ eval (s y) q ≠ 0 ∧ RatChart.ratMap p q (s y) = y)
    (hW : IsOpen W)
    (hWs : ∀ x' ∈ zeroSet J ∩ W, eval x' q ≠ 0 ∧ RatChart.ratMap p q x' ∈ U ∧ s (RatChart.ratMap p q x') = x')
    (hEW : E ⊆ W) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    RatChart.ratPosDens J p q (E.indicator f) φ y = (U ∩ s ⁻¹' E).indicator
      (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y := by
  classical
  unfold RatChart.ratPosDens RatChart.ratSheetSum
  by_cases hy : y ∈ U ∩ s ⁻¹' E
  · rw [Set.indicator_of_mem hy]
    obtain ⟨hZ, hq, hR⟩ := hsec y hy.1
    have hfib : s y ∈ RatChart.ratFibre J p q y := ⟨hZ, hq, hR⟩
    have hsh : RatChart.IsRatSheetAt J p q (s y) s :=
      ⟨U, hU, by rw [hR]; exact hy.1, hsd, by rw [hR], hsec, W,
        hW.mem_nhds (hEW hy.2), fun x' hx' _ _ => (hWs x' hx').2.2.symm⟩
    have hex : ∃ s', RatChart.IsRatSheetAt J p q (s y) s' := ⟨s, hsh⟩
    rw [finsum_eq_single _ (s y) ?_, finsum_eq_if, if_pos hfib, dif_pos hex]
    · have hev : hex.choose =ᶠ[𝓝 y] s := by
        obtain ⟨U₁, hU₁, hxU₁, hsd₁, hsx₁, hsec₁, -⟩ := hex.choose_spec
        rw [hR] at hxU₁ hsx₁
        have hcont : ContinuousAt hex.choose y :=
          hsd₁.continuousOn.continuousAt (hU₁.mem_nhds hxU₁)
        have h1 : ∀ᶠ w in 𝓝 y, hex.choose w ∈ W :=
          hcont.preimage_mem_nhds (by rw [hsx₁]; exact hW.mem_nhds (hEW hy.2))
        filter_upwards [h1, hU₁.mem_nhds hxU₁] with w hwW hwU₁
        have h := (hWs _ ⟨(hsec₁ w hwU₁).1, hwW⟩).2.2
        rw [(hsec₁ w hwU₁).2.2] at h
        exact h.symm
      dsimp only
      rw [IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k => hev.fun_comp (φ k),
        Set.indicator_of_mem (show s y ∈ E from hy.2)]
    · intro x hne
      rw [finsum_eq_if]
      split_ifs with hx h
      · have hxE : x ∉ E := fun hxE => hne (by
          have h' := (hWs x ⟨hx.1, hEW hxE⟩).2.2
          rw [hx.2.2] at h'
          exact h'.symm)
        dsimp only
        rw [Set.indicator_of_notMem hxE, zero_mul, max_self]
      · rfl
      · rfl
  · rw [Set.indicator_of_notMem hy]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
    split_ifs with h
    · have hxE : x ∉ E := fun hxE => hy (by
        obtain ⟨-, h1, h2⟩ := hWs x ⟨hx.1, hEW hxE⟩
        rw [hx.2.2] at h1 h2
        exact ⟨h1, by rw [Set.mem_preimage, h2]; exact hxE⟩)
      dsimp only
      rw [Set.indicator_of_notMem hxE, zero_mul, max_self]
    · rfl
end GroundTheory.Heights₂.Heights.RatPosPartLocal
