-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Qx4_up_conj__489db79eb27d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:12:57.108516+00:00
-- url     : https://prove2.me/submissions/3598dafe-e1ea-43df-8886-2938261c96e3

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_glev_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_up_conj

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
theorem _root_.solution {u p : Mx k r} (hu : u ∈ UP k r l) (hp : p ∈ Glev k r l.succ) : p⁻¹ * u * p ∈ UP k r l := by
  have := up_conj hu (glev_inv hp)
  rwa [Matrix.nonsing_inv_nonsing_inv _ (uh_unit hp.1)] at this
end Formalism.FourierDecayAlt.P.Qx4
