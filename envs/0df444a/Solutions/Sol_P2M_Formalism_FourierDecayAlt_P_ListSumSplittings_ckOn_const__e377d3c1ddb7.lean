-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_ListSumSplittings_ckOn_const__e377d3c1ddb7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:11:18.35368+00:00
-- url     : https://prove2.me/submissions/cb66112b-a0b2-4f1c-9207-15bd20c73a40

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumSplittings
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic Formalism.FourierDecayAlt.P.ListSumInequalities
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumSplittings
theorem _root_.solution {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {m : ℕ∞} (c : F) :
    CkOn m (GV k r) (fun _ : Mat k r => c) := by
  intro g₀ _
  exact ⟨Set.univ, fun _ => c, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
end Formalism.FourierDecayAlt.P.ListSumSplittings
