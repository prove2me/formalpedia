-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Qx4_stab_dec__b3b71b5cc842
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:18:07.65481+00:00
-- url     : https://prove2.me/submissions/a9dc50d1-7cb8-4449-abf0-b0a782fdcb63

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_inv_fix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_glev_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_up_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_stab_dec

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
theorem _root_.solution {g : Mx k r} (hg : g ∈ Glev k r l.castSucc) (he : g *ᵥ 𝐞 = 𝐞) :
    ∃ u ∈ UP k r l, ∃ g₁ ∈ Glev k r l.succ, g = g₁ * u := by
  obtain ⟨u, hu, g₁, hg₁, h⟩ := stab_dec (glev_inv hg) (uh_inv_fix hg.1 he)
  refine ⟨u⁻¹, up_inv hu, g₁⁻¹, glev_inv hg₁, ?_⟩
  rw [← Matrix.mul_inv_rev, ← h, Matrix.nonsing_inv_nonsing_inv _ (uh_unit hg.1)]
end Formalism.FourierDecayAlt.P.Qx4
