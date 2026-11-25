-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Qx4_nlev_dec__c8a89854c85d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:38:08.760602+00:00
-- url     : https://prove2.me/submissions/d35e4b4a-1b6b-49bd-9264-22b32c845b83

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_mul_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_up_nset
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx4_stab_dec__b3b71b5cc842
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_nlev_e
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_mul


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
theorem _root_.solution {n : Mx k r} (hn : n ∈ Nlev k r l.castSucc) :
    ∃ u ∈ UP k r l, ∃ n₁ ∈ Nlev k r l.succ, n = n₁ * u := by
  obtain ⟨u, hu, g₁, hg₁, h⟩ := stab_dec' hn.2 (nlev_e hn)
  refine ⟨u, hu, g₁, ⟨?_, hg₁⟩, h⟩
  have : g₁ = n * u⁻¹ := by rw [h, Matrix.mul_assoc, uh_mul_inv hu.1.1, Matrix.mul_one]
  rw [this]
  exact WeylGroupFacts.mem_n_mul hn.1 (WeylGroupFacts.mem_n_inv (up_nset hu))
end Formalism.FourierDecayAlt.P.Qx4
