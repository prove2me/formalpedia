-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.pi_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:44:03.728051+00:00
-- url     : https://prove2.me/submissions/63ff4d3b-3fd4-4acb-a827-5d6e95fcbb7e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_HeckeFubiniCompatibility_PActPi
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_pi_cont_supp

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
namespace PositivityTheory.Rg.BcB.CG
theorem _root_.solution (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Idx : ι → Type} [∀ v, Fintype (Idx v)]
    (e : ∀ v, X → Idx v → Idx v → ℂ) (u : (∀ v, Idx v) → (ι → X) → ℂ) (I : ∀ v, Idx v)
    (he : ∀ v a b, Continuous (fun t => e v t a b) ∧ HasCompactSupport (fun t => e v t a b))
    (hu : ∀ J, Continuous (u J)) :
    Integrable (fun y : ι → X => ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y) (Measure.pi fun _ => μ) :=
  (pi_cont_supp e u I he hu).1.integrable_of_hasCompactSupport (pi_cont_supp e u I he hu).2
end PositivityTheory.Rg.BcB.CG
