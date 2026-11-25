-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_PairingConjugationLemmas__d_sub_6e4cc9e6dfa7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:38:06.612974+00:00
-- url     : https://prove2.me/submissions/3912c66c-c918-49c1-a002-d35faee1a186

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PairingTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PairingConjugationLemmas
open MeasureTheory Filter Topology Finset Module Formalism.FourierDecayAlt.crystallineComparison
noncomputable section
variable {f : ℕ}
variable (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La]
namespace Formalism.FourierDecayAlt.P.PairingConjugationLemmas
theorem _root_.solution (m m' : Fin (finrank ℤ La) → ℤ) : ψd La (m - m') = ψd La m - ψd La m' := by
  simp only [ψd]
  rw [← map_sub]
  congr 1
  funext j
  simp
end Formalism.FourierDecayAlt.P.PairingConjugationLemmas
