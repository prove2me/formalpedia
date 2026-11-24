-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_B2x5_heis_act__04df4e81c20a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:26:16.263008+00:00
-- url     : https://prove2.me/submissions/37ad0096-430a-46fa-bfa8-d33a9381ab90

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_hermitian_first_basis_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_lift_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_heis_act

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ) :
    heisG k r' (liftVec k 1 r' y) b *ᵥ u =
      u - herm (Hpk k r') (res k r' u) y • e0 k r' + u (iL k r') • (liftVec k 1 r' y + b • e0 k r') := by
  rw [heis_act, herm_lift_right, hermitian_first_basis_right]
end Formalism.FourierDecayAlt.P.B2x5
