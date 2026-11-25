-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_axA2__0d56062f0ae4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:38:09.886363+00:00
-- url     : https://prove2.me/submissions/3639cea5-f405-437e-a9b8-6e146f2a2288

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
variable {E : Type} [Field E] [DecidableEq E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
theorem _root_.solution (D : TA.Data E) (Sg : ℕ → ℕ → Finset E) (Th) (hA : KernelSupport D) : KernelSupport (D' D Sg Th) := by
  intro i s hs hsi hi h h' t t' hh hh' ht ht' hc
  have := hA i s hs hsi hi h h' t t' hh hh' ht ht' hc
  show restr (PT Sg i) (D.K i) (TA.ext h s t) (TA.ext h' s t') = 0
  unfold restr
  split_ifs <;> simp [this]
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
