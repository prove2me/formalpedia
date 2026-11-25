-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_B2x8_cf_lev__t_c6e021a54e58
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:37:15.648179+00:00
-- url     : https://prove2.me/submissions/dea1caba-15f3-4ecc-9cca-52d1ddac207f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_levi_three_block

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (g₁ : Mat k r') (hg : g₁ ∈ GV k r') (p : ℂ × HPar k r') :
    ιLev k 1 r' g₁ *ᵥ Ψt k r' p = Ψt k r' (Tl k r' g₁ p) := by
  simp only [Ψt, Tl, levi_three_block]
  rw [show hb k r' (g₁ *ᵥ p.2.1) p.2.2 = hb k r' p.2.1 p.2.2 by simp only [hb, herm_UH _ hg]]
end Formalism.FourierDecayAlt.P.B2x8
