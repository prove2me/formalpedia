-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_big_cell_vanishing_of_commute__266cd2982839
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:47:10.363435+00:00
-- url     : https://prove2.me/submissions/8da71a69-0211-40b5-9fd7-4307cf69bfdf

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Mathlib.Topology.Algebra.MvPolynomial
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingOfCommute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open DifferentialOperatorClasses
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C6.BigCellVanishingOfCommute := by
  intro hJ
  obtain ⟨c₃, hc₃, hJ⟩ := hJ
  refine ⟨c₃, hc₃, ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ D Θ A F hS hC hR hA hF g hg
  obtain ⟨h1, h2, h3⟩ := hJ k r Wp Wq D Θ A F hS hC hA hF
  rw [h3 g hg]
  exact hR _ h1 h2 g hg
end Formalism.FourierDecayAlt.P
