-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.weakae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:20:50.716742+00:00
-- url     : https://prove2.me/submissions/1217ef83-30fb-46d7-9176-b5a5ca1f3628

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Weakae
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Weakae_integrable_k
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Weakae_inner_ind

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal ComplexConjugate
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P
open Weakae
namespace PositivityTheory.Rg.BcB.E2.P
theorem _root_.solution : WeakAE := by
  intro Y S ι _ _ _ m _ ν _ F f c q hf hc hint hq hw
  classical
  have hki : ∀ j, Integrable (fun p : Y × S => c j p.1 * conj (f j p.1 p.2)) (m.prod ν) := fun j =>
    integrable_k m ν (F j) (f j) (c j) (hf j) (hc j) (hint j)
  have hGj : ∀ j, Integrable (fun s => ∫ y, c j y * conj (f j y s) ∂m) ν := fun j =>
    (hki j).integral_prod_right
  have hG : Integrable (fun s => ∑ j, ∫ y, c j y * conj (f j y s) ∂m) ν :=
    integrable_finsetSum _ fun j _ => hGj j
  have hq' : Integrable q ν := hq.integrable (by norm_num)
  refine Integrable.ae_eq_of_forall_setIntegral_eq _ _ hG hq' fun A hA hνA => ?_
  have hR : ∫ s, q s * (indicatorConstLp 2 hA hνA.ne (1 : ℂ)) s ∂ν = ∫ s in A, q s ∂ν := by
    rw [← integral_indicator hA]
    refine integral_congr_ae ?_
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hνA.ne) (c := (1 : ℂ))] with s hs
    rw [hs]
    by_cases h : s ∈ A <;> simp [h]
  rw [← hR, ← hw, integral_finsetSum _ fun j _ => (hGj j).integrableOn]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hres : m.prod (ν.restrict A) = (m.prod ν).restrict (Set.univ ×ˢ A) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hkA : Integrable (Function.uncurry fun y s => c j y * conj (f j y s)) (m.prod (ν.restrict A)) := by
    rw [hres]; exact (hki j).restrict
  symm
  calc ∫ y, c j y * inner ℂ (F j y) (indicatorConstLp 2 hA hνA.ne (1 : ℂ)) ∂m
      = ∫ y, ∫ s in A, c j y * conj (f j y s) ∂ν ∂m := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        rw [inner_ind ν (F j y) (f j y) ((hf j).2 y) A hA hνA.ne, integral_const_mul]
    _ = ∫ s in A, ∫ y, c j y * conj (f j y s) ∂m ∂ν := integral_integral_swap hkA
end PositivityTheory.Rg.BcB.E2.P
