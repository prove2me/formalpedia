-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.Specmeas.im_ofR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:29:07.605814+00:00
-- url     : https://prove2.me/submissions/5bef78ce-8a5b-4c56-872d-47ae9fed72c6

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Specmeas
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Specmeas_ofR_sub
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Specmeas_nonneg_ofR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ComplexConjugate ComplexOrder CompactlySupported
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P PositivityTheory.Rg.BcB.E2.P.Specmeas
variable {X : Type} [TopologicalSpace X]
variable (Λ : C(X, ℂ) →ₗ[ℂ] ℂ) (hΛ : ∀ f : C(X, ℂ), 0 ≤ Λ (star f * f))
include hΛ
namespace PositivityTheory.Rg.BcB.E2.P.Specmeas
theorem _root_.solution (g : C(X, ℝ)) : (Λ (ofR g)).im = 0 := by
  let p : C(X, ℝ) := ⟨fun x => max (g x) 0, by fun_prop⟩
  let n : C(X, ℝ) := ⟨fun x => max (-g x) 0, by fun_prop⟩
  have hg : g = p - n := by
    ext x
    simp only [p, n, ContinuousMap.sub_apply, ContinuousMap.coe_mk]
    rcases le_total 0 (g x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hp := nonneg_ofR Λ hΛ (g := p) (fun x => le_max_right _ _)
  have hn := nonneg_ofR Λ hΛ (g := n) (fun x => le_max_right _ _)
  rw [Complex.le_def] at hp hn
  rw [hg, ofR_sub, map_sub, Complex.sub_im, ← hp.2, ← hn.2]; simp
end PositivityTheory.Rg.BcB.E2.P.Specmeas
