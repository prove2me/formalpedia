-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_qm_eq__9adcf75d7042
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:37:18.614804+00:00
-- url     : https://prove2.me/submissions/47ea4199-1c0b-4426-9ef1-73e553cde38f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumLocalExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
theorem _root_.solution (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r) {t : ℕ}
    (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (Φ : Mat k r → E) (g : Mat k r) :
    qminorOp (FourTermExpansion.LT M) a b u Φ g = ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      fold M (List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j)) Φ g := by
  unfold qminorOp
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Pi.smul_apply]
  simp only [FourTermExpansion.fold, List.map_ofFn]
  rfl
end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
