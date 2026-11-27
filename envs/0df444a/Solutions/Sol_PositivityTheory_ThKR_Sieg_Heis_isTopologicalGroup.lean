-- Prove2me | solution 1 for PositivityTheory.ThKR.Sieg.Heis.isTopologicalGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:23:03.148418+00:00
-- url     : https://prove2.me/submissions/81305199-4b5e-46f9-a8b6-1bd9d0a63c00

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmulNn
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_SiegelHaar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory MeasureTheory.Measure Topology Set
open scoped NNReal ENNReal Pointwise
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Sieg
variable {A B : Type} [AddCommGroup A] [AddCommGroup B]
variable (β : A →+ A →+ B)
variable [TopologicalSpace A] [TopologicalSpace B]
variable [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]
namespace PositivityTheory.ThKR.Sieg
namespace Heis
theorem _root_.solution (hβ : Continuous fun p : A × A => β p.1 p.2) : IsTopologicalGroup (Heis β) where
  continuous_mul := by
    change Continuous fun p : (A × B) × A × B => ((p.1.1 + p.2.1, p.1.2 + p.2.2 + β p.1.1 p.2.1) : A × B)
    exact (continuous_fst.fst.add continuous_snd.fst).prodMk ((continuous_fst.snd.add continuous_snd.snd).add
      (hβ.comp (continuous_fst.fst.prodMk continuous_snd.fst)))
  continuous_inv := by
    change Continuous fun p : A × B => ((-p.1, -p.2 + β p.1 p.1) : A × B)
    exact continuous_fst.neg.prodMk (continuous_snd.neg.add (hβ.comp (continuous_fst.prodMk continuous_fst)))
end Heis
end PositivityTheory.ThKR.Sieg
