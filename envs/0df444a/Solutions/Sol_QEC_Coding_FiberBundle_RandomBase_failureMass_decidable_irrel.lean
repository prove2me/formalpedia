-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.failureMass_decidable_irrel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:08:25.100375+00:00
-- url     : https://prove2.me/submissions/e25c83b5-0d4a-41f7-967e-b7116f1ffb40

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_eventMass_decidable_irrel


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {Ω : Type*} [Fintype Ω]
    (p : PMF Ω) (event : Ω → Prop)
    (d₁ d₂ : DecidablePred event) :
    @failureMass Ω inferInstance p event d₁ =
      @failureMass Ω inferInstance p event d₂ := by
  unfold failureMass
  exact eventMass_decidable_irrel p (fun ω => ¬event ω) _ _
end QEC.Coding.FiberBundle.RandomBase
