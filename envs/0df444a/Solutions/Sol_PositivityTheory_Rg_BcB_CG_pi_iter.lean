-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.pi_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:19:38.337799+00:00
-- url     : https://prove2.me/submissions/26c9320f-4478-4e78-a40b-f05316e820bc

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_HeckeFubiniCompatibility_PActPi
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_pi_iterated_integral_continuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.CG
variable {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
variable [One X]
namespace PositivityTheory.Rg.BcB.CG
theorem _root_.solution (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Idx : ι → Type) [∀ v, Fintype (Idx v)] [∀ v, DecidableEq (Idx v)]
    (e : ∀ v, X → Idx v → Idx v → ℂ) (val : ι → ℂ) (u : (∀ v, Idx v) → (ι → X) → ℂ) (I : ∀ v, Idx v)
    (he : ∀ v a b, Continuous (fun t => e v t a b) ∧ HasCompactSupport (fun t => e v t a b))
    (hu : ∀ J, Continuous (u J))
    (hloc : ∀ v J y, ∑ j, ∫ t, e v t (J v) j * u (Function.update J v j) (Function.update y v t) ∂μ =
      val v * u J (Function.update y v 1)) :
    ∫ y, ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y ∂(Measure.pi fun _ => μ) = (∏ v, val v) * u I 1 :=
  pi_iterated_integral_continuous μ _ ι Idx e val u I rfl he hu hloc
end PositivityTheory.Rg.BcB.CG
