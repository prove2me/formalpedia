-- Prove2me | solution 1 for PI.Dv.Tr.rank_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:36.93835+00:00
-- url     : https://prove2.me/submissions/bbd1330f-adb3-4370-ae04-190429a9b210

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_KudlaSiegelWeil
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Theorems.Thm_PI_Dv_Tr_eps_idem
import Theorems.Thm_PI_Dv_Tr_mul_idem
import Theorems.Thm_PI_Dv_Tr_finrank_range_idem
import Theorems.Thm_PI_Dv_Tr_eG_comm
import Theorems.Thm_PI_Dv_Tr_eG_idem
import Theorems.Thm_PI_Dv_Tr_eS_comm
import Theorems.Thm_PI_Dv_Tr_eS_idem
import Theorems.Thm_PI_Dv_Tr_trace_mul_eS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.Tr
theorem _root_.solution (T : GoodSet K G) (P0 P : Pair K G) (hM : M1 T P0)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K G V) :
    finrank K (LinearMap.range (ρ.asAlgebraHom (eps P * eG T))) =
      ∑ s, nS T P s * finrank K (LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s))) := by
  choose c hc using fun s => trace_mul_eS T s ρ
  have hn : ∀ (Q : Pair K G) s, ((nS T Q s : ℕ) : K) = LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom (eps Q)) := by
    intro Q s
    rw [nS]
    exact finrank_range_idem _ (by rw [← map_mul, eps_idem])
  have hidS : ∀ (Q : Pair K G) s, (eps Q * eS T s) * (eps Q * eS T s) = eps Q * eS T s :=
    fun Q s => mul_idem (eps_idem Q) (eS_idem T s) (eS_comm T s (eps Q)).symm
  have hidG : (eps P * eG T) * (eps P * eG T) = eps P * eG T :=
    mul_idem (eps_idem P) (eG_idem T) (eG_comm T (eps P)).symm
  have hr : ∀ s, ((finrank K (LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s))) : ℕ) : K) = c s := by
    intro s
    rw [finrank_range_idem _ (by rw [← map_mul, hidS]), hc, ← hn, hM s, Nat.cast_one, mul_one]
  apply Nat.cast_injective (R := K)
  rw [finrank_range_idem _ (by rw [← map_mul, hidG])]
  rw [eG, Finset.mul_sum, map_sum, map_sum]
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hc, hr, hn, mul_comm]
end PI.Dv.Tr
