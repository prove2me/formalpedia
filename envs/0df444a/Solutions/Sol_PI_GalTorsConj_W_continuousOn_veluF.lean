-- Prove2me | solution 1 for PI.GalTorsConj.W.continuousOn_veluF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:51:17.160101+00:00
-- url     : https://prove2.me/submissions/d89c14ff-28f1-474b-830f-9e0031b8396e

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
    ContinuousOn (veluF L S) (veluU L S) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have h0 : ContinuousAt L.weierstrassP z := (L.analyticOnNhd_weierstrassP z hz.1).continuousAt
  have hs : ContinuousAt (fun z => ∑ P ∈ S, (L.weierstrassP (z + P) - L.weierstrassP P)) z := by
    have : ∀ P ∈ S, ContinuousAt (fun z => L.weierstrassP (z + P) - L.weierstrassP P) z := by
      intro P hP
      have h1 : ContinuousAt L.weierstrassP (z + P) :=
        (L.analyticOnNhd_weierstrassP _ (hz.2 P hP)).continuousAt
      have h2 : ContinuousAt (fun z => L.weierstrassP (z + P)) z :=
        ContinuousAt.comp (g := L.weierstrassP) (f := fun x => x + P) (x := z) h1
          (continuous_add_const P).continuousAt
      exact h2.sub continuousAt_const
    exact tendsto_finsetSum S this
  exact h0.add hs
end PI.GalTorsConj.W
