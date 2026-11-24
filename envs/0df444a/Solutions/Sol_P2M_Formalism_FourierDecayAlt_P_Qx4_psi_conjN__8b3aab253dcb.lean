-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Qx4_psi_conjN__8b3aab253dcb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:52:15.199393+00:00
-- url     : https://prove2.me/submissions/339716c4-0912-4628-ae66-b9025654cbf7

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx4_inv_inv__225f23d156f5
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_psi_conjN
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
local notation "⟪" u ", " v "⟫" => herm (Hpk k r) u v
variable {l : Fin r}
local notation "𝐞" => bvec (eI k r l)
local notation "𝐬" => bvec (esI k r l)
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {n u : Mx k r} (hn : n ∈ Nset k r) (hu : u ∈ Nset k r) :
    psi k r z cStd (n⁻¹ * u * n) = psi k r z cStd u := by
  have := psi_conjN hz (WeylGroupFacts.mem_n_inv hn) hu
  rwa [inv_inv' hn.1] at this
end Formalism.FourierDecayAlt.P.Qx4
