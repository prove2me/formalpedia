-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_LongWeylElement_fin_cases__0856e4f673a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:38:09.463974+00:00
-- url     : https://prove2.me/submissions/ed08f85f-9103-460a-9356-b5f35383db64

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement

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
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution (a : Fin (1 + r')) : a = a0 r' ∨ ∃ a' : Fin r', a = Fin.natAdd 1 a' := by
  have := a.isLt
  by_cases h : a.val = 0
  · left
    exact Fin.ext h
  · right
    refine ⟨⟨a.val - 1, by omega⟩, Fin.ext ?_⟩
    show a.val = 1 + (a.val - 1)
    omega
end Formalism.FourierDecayAlt.P.LongWeylElement
