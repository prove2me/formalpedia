-- Prove2me | solution 1 for PI.GalTorsConj.W.continuousOn_veluD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:42:13.625207+00:00
-- url     : https://prove2.me/submissions/7e339a13-31c6-4327-89fd-ed8538d177aa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulMain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Formalism.L2.Th1.F
namespace PI.GalTorsConj.W
theorem _root_.solution (L : PeriodPair) (S : Finset ℂ) :
    ContinuousOn (veluD L S) (veluU L S) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have h0 : ContinuousAt L.derivWeierstrassP z :=
    (L.analyticOnNhd_derivWeierstrassP z hz.1).continuousAt
  have hs : ContinuousAt (fun z => ∑ P ∈ S, L.derivWeierstrassP (z + P)) z := by
    have : ∀ P ∈ S, ContinuousAt (fun z => L.derivWeierstrassP (z + P)) z := by
      intro P hP
      have h1 : ContinuousAt L.derivWeierstrassP (z + P) :=
        (L.analyticOnNhd_derivWeierstrassP _ (hz.2 P hP)).continuousAt
      exact ContinuousAt.comp (g := L.derivWeierstrassP) (f := fun x => x + P) (x := z) h1
        (continuous_add_const P).continuousAt
    exact tendsto_finsetSum S this
  exact h0.add hs
end PI.GalTorsConj.W
