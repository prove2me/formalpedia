-- Prove2me | solution 1 for PI.KLW.lset_spans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:13:41.557599+00:00
-- url     : https://prove2.me/submissions/059306b2-1c17-4bd9-9856-a374aca3a08c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairingFactorsThroughPeriods
import Theorems.Thm_PI_KLW_exists_ne_zero_mem
import Theorems.Thm_PI_KLW_exists_natCast_mul_mem
import Theorems.Thm_PI_KLW_natCast_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
variable (cj : E ≃ₐ[ℚ] E) (hc : PI.KerIso.IsConj K cj) {n : Type} [Fintype n]
  (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (p : ℕ)
  (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K))
include hc
namespace PI.KLW
theorem _root_.solution (hI : PI.KerIso.SelfDualI K cj I) : Spans K (Lset I p g₀) := by
  intro v
  obtain ⟨y0, hy0, hne⟩ := exists_ne_zero_mem cj I hI
  choose N hN hNI using fun a => exists_natCast_mul_mem I hy0 hne (g₀.symm v a)
  refine ⟨∏ a, N a, Finset.prod_ne_zero_iff.mpr fun a _ => hN a, 1, Nat.coprime_one_left p,
    fun a => ?_⟩
  rw [Nat.cast_one, one_mul, map_smul, Pi.smul_apply, Algebra.smul_def, map_natCast]
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ a)
  rw [hq, Nat.cast_mul, mul_comm (N a : E), mul_assoc]
  exact natCast_mul_mem I q (hNI a)
end PI.KLW
