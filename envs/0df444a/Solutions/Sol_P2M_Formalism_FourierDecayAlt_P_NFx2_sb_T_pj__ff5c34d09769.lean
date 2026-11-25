-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_NFx2_sb_T_pj__ff5c34d09769
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:47:07.490679+00:00
-- url     : https://prove2.me/submissions/aa0a4cbf-3dea-46ea-9ead-4354de624e62

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L0 : PreLevel A P.r}
  {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (σ ρ' ρ : M.Ty P) (v : ℂ) :
    lowerBlockAlt κ QQ σ ρ' v * proj κ ρ = if ρ' = ρ then lowerBlockAlt κ QQ σ ρ v else 0 := by
  rw [lowerBlockAlt, mul_assoc, pj_mul]
  split_ifs with h
  · subst h; rfl
  · rw [mul_zero]
end Formalism.FourierDecayAlt.P.NFx2
