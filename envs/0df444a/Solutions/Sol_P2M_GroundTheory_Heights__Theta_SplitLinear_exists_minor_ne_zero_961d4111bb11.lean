-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SplitLinear_exists_minor_ne_zero_961d4111bb11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:34:54.690253+00:00
-- url     : https://prove2.me/submissions/50a46b54-8755-4151-8f81-670a57e264b9

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRowsLinearIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_SplitLinear_RankMinors
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SplitLinear_exists_rows_linearIndependent_911acfd75589

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.SplitLinear
open Matrix Module
universe u
variable {K : Type*} [Field K]
namespace GroundTheory.Heights₂.Theta.SplitLinear
theorem _root_.solution {r c : Type*} [Fintype r] [Fintype c] (P : Matrix r c K) {k : ℕ}
    (hk : k ≤ P.rank) : ∃ (I : Fin k → r) (J : Fin k → c), (P.submatrix I J).det ≠ 0 := by
  classical
  obtain ⟨I, hI⟩ := exists_rows_linearIndependent P hk
  set N : Matrix (Fin k) c K := P.submatrix I id with hNdef
  have hN : N.rank = k := by
    have := LinearIndependent.rank_matrix (M := N) hI
    simpa using this
  have hNt : k ≤ Nᵀ.rank := by rw [rank_transpose, hN]
  obtain ⟨J, hJ⟩ := exists_rows_linearIndependent Nᵀ hNt
  refine ⟨I, J, ?_⟩
  have hQ : IsUnit (Nᵀ.submatrix J id) := linearIndependent_rows_iff_isUnit.1 hJ
  have e : P.submatrix I J = (Nᵀ.submatrix J id)ᵀ := by ext p q; rfl
  rw [e, det_transpose]
  exact ((isUnit_iff_isUnit_det _).1 hQ).ne_zero
end GroundTheory.Heights₂.Theta.SplitLinear
