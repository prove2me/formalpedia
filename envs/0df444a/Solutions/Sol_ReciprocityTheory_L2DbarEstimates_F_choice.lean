-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.choice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:54:34.40814+00:00
-- url     : https://prove2.me/submissions/775b6d15-2126-4bdd-8603-13cbe115defa

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Choice
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_smoothReal_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_sSup_image_le_max
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_ckR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_levi_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hChi : ChiStatement) (hPsi : PsiStatement n M)
    (hShell : ShellStatement n M) (hLZ : LeviNormSqStatement n M) (hChain : ChainStatement n M) :
    ChoiceStatement n M := by
  intro X ph v C ε hph hv hC hε
  have hz := X.isLocalHomeomorph

  have hE : SmoothR n X.z (fun y => X.e y + ‖X.z y‖ ^ 2) :=
    SmoothR.add n X.z _ _ X.smooth_e (hLZ X.z hz).1
  have hEc : Continuous (fun y => X.e y + ‖X.z y‖ ^ 2) := smoothReal_continuous n X.z hz _ hE
  have hExh : ∀ b : ℝ, IsCompact {x | X.e x + ‖X.z x‖ ^ 2 ≤ b} := by
    intro b
    refine (X.isCompact_le b).of_isClosed_subset (isClosed_le hEc continuous_const) ?_
    intro x hx
    simp only [mem_ofPred_eq] at hx ⊢
    nlinarith [sq_nonneg ‖X.z x‖]
  have hLeviE : ∀ x ξ, (∑ j, ‖ξ j‖ ^ 2) ≤ (Levi n X.z (fun y => X.e y + ‖X.z y‖ ^ 2) x ξ).re := by
    intro x ξ
    rw [levi_add n X.z X.e (fun y => ‖X.z y‖ ^ 2) (SmoothR.ckR n X.z 2 _ X.smooth_e)
      (SmoothR.ckR n X.z 2 _ (hLZ X.z hz).1) x ξ, (hLZ X.z hz).2 x ξ, Complex.add_re,
      Complex.ofReal_re]
    linarith [X.levi_e x ξ]

  obtain ⟨b0, hb0⟩ := hC.bddAbove_image hEc.continuousOn
  set a : ℝ := b0 + 1 with ha
  have hCa : ∀ x ∈ C, X.e x + ‖X.z x‖ ^ 2 < a := by
    intro x hx
    have := hb0 ⟨x, hx, rfl⟩
    linarith

  obtain ⟨ψ, hψ, hψ0, hcut⟩ := hPsi X.z hz (fun y => X.e y + ‖X.z y‖ ^ 2) a hE hExh
  have hψc : Continuous ψ := smoothReal_continuous n X.z hz _ hψ
  have hdc : Continuous (fun x => dSqR n X.z ψ x) := by
    unfold dSqR
    refine continuous_finsetSum _ (fun j _ => ?_)
    exact ((Smooth.continuous n X.z hz _ (Smooth.d n X.z j _ hψ)).norm).pow 2

  obtain ⟨R1, hR1, hR1χ⟩ := hShell X.z hz (fun y => X.e y + ‖X.z y‖ ^ 2) ph ψ v a hEc hExh
    (smoothReal_continuous n X.z hz _ hph) hψc hv
  set g : M → ℝ := fun x => max (2 * ψ x) ((1 + 1 / ε) * dSqR n X.z ψ x) with hg
  have hgc : Continuous g := (continuous_const.mul hψc).max (continuous_const.mul hdc)
  set R : ℝ → ℝ := fun t => max (R1 t) (sSup (g '' {x | X.e x + ‖X.z x‖ ^ 2 ≤ t})) with hR
  have hRb : ∀ b : ℝ, BddAbove (R '' Iic b) := by
    intro b
    obtain ⟨B1, hB1⟩ := hR1 b
    obtain ⟨B, hB⟩ := (hExh b).bddAbove_image hgc.continuousOn
    refine ⟨max B1 (max B 0), ?_⟩
    rintro y ⟨t, ht, rfl⟩
    refine max_le_max (hB1 ⟨t, ht, rfl⟩) (sSup_image_le_max g _ B ?_)
    intro x hx
    exact hB ⟨x, (show X.e x + ‖X.z x‖ ^ 2 ≤ b from le_trans hx ht), rfl⟩
  have hgR : ∀ x, g x ≤ R (X.e x + ‖X.z x‖ ^ 2) := by
    intro x
    refine le_max_of_le_right (le_csSup ((hExh _).bddAbove_image hgc.continuousOn) ⟨x, ?_, rfl⟩)
    exact (le_refl (X.e x + ‖X.z x‖ ^ 2))

  obtain ⟨χ, hχ, hχa, hχ0, hχ1, hχ2, hχR⟩ := hChi a R hRb
  have hχs : SmoothR n X.z (fun y => χ (X.e y + ‖X.z y‖ ^ 2)) := SmoothR.comp n X.z χ hχ _ hE
  refine ⟨fun x => ph x + χ (X.e x + ‖X.z x‖ ^ 2), ψ, fun y => X.e y + ‖X.z y‖ ^ 2,
    {x | X.e x + ‖X.z x‖ ^ 2 < a}, SmoothR.add n X.z _ _ hph hχs, hψ, hEc, hcut,
    isOpen_lt hEc continuous_const, hCa, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [mem_ofPred_eq] at hx
    refine ⟨?_, (hψ0 x (by linarith)).1⟩
    show ph x + χ (X.e x + ‖X.z x‖ ^ 2) = ph x
    rw [hχa _ hx.le, add_zero]
  · intro x
    have : 2 * ψ x ≤ χ (X.e x + ‖X.z x‖ ^ 2) := by
      by_cases h : X.e x + ‖X.z x‖ ^ 2 ≤ a + 1
      · rw [(hψ0 x h).1, mul_zero]; exact hχ0 _
      · push Not at h
        exact ((le_max_left _ _).trans (hgR x)).trans (hχR _ h.le).1
    linarith
  · intro x ξ
    have hχ2' : ContDiff ℝ 2 χ := hχ.of_le (by norm_cast)
    rw [levi_add n X.z ph (fun y => χ (X.e y + ‖X.z y‖ ^ 2)) (SmoothR.ckR n X.z 2 _ hph)
      (SmoothR.ckR n X.z 2 _ hχs) x ξ, Complex.add_re,
      hChain X.z hz χ (fun y => X.e y + ‖X.z y‖ ^ 2) hχ2' hE x ξ, Complex.add_re,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.ofReal_re]
    have hs : 0 ≤ ∑ j, ‖ξ j‖ ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have h1 : (1 + 1 / ε) * dSqR n X.z ψ x * ∑ j, ‖ξ j‖ ^ 2 ≤
        deriv χ (X.e x + ‖X.z x‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 := by
      by_cases h : X.e x + ‖X.z x‖ ^ 2 ≤ a + 1
      · rw [(hψ0 x h).2, mul_zero, zero_mul]
        exact mul_nonneg (hχ1 _) hs
      · push Not at h
        exact mul_le_mul_of_nonneg_right
          (((le_max_right _ _).trans (hgR x)).trans (hχR _ h.le).2) hs
    have h2 : deriv χ (X.e x + ‖X.z x‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 ≤
        deriv χ (X.e x + ‖X.z x‖ ^ 2) *
          (Levi n X.z (fun y => X.e y + ‖X.z y‖ ^ 2) x ξ).re :=
      mul_le_mul_of_nonneg_left (hLeviE x ξ) (hχ1 _)
    have h3 : 0 ≤ deriv (deriv χ) (X.e x + ‖X.z x‖ ^ 2) *
        ‖dDot n X.z (fun y => ((X.e y + ‖X.z y‖ ^ 2 : ℝ) : ℂ)) x ξ‖ ^ 2 :=
      mul_nonneg (hχ2 _) (sq_nonneg _)
    linarith
  · refine ⟨hv.aestronglyMeasurable, ?_⟩
    exact hR1χ χ hχ0 (fun t ht => (hχR t ht).1.trans' (le_max_left _ _))
end ReciprocityTheory.L2DbarEstimates.F
