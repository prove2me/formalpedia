-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.tonelli
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:20:42.253583+00:00
-- url     : https://prove2.me/submissions/ff2ee9f3-53a1-4c7c-8997-229f6967b02c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Tonelli
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Tonelli_enorm_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P
namespace PositivityTheory.Rg.BcB.E2.P
theorem _root_.solution : Tonelli := by
  intro Y S _ _ m _ ν _ F f W hf hW hfin
  have hmeas : Measurable (Function.uncurry fun y s => W y * ‖f y s‖ₑ ^ 2) :=
    (hW.comp measurable_fst).mul (hf.1.enorm.pow_const 2)
  refine ae_lt_top hmeas.lintegral_prod_left' ?_
  rw [← lintegral_lintegral_swap hmeas.aemeasurable]
  refine ne_of_eq_of_ne (lintegral_congr fun y => ?_) hfin
  have hy : Measurable fun s => f y s := hf.1.comp measurable_prodMk_left
  rw [lintegral_const_mul _ (hy.enorm.pow_const 2), Tonelli.enorm_sq]
  congr 1
  exact lintegral_congr_ae ((hf.2 y).mono fun s hs => by simp only [hs])
end PositivityTheory.Rg.BcB.E2.P
