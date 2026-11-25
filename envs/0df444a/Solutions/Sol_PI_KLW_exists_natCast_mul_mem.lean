-- Prove2me | solution 1 for PI.KLW.exists_natCast_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:47:49.606421+00:00
-- url     : https://prove2.me/submissions/557ef2ca-f8a8-482a-b510-e6c631443a3c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairingFactorsThroughPeriods
import Theorems.Thm_PI_KLW_Unimod_smul_mem


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
namespace PI.KLW
theorem _root_.solution (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {y0 : E}
    (hy0 : y0 ∈ I) (hne : y0 ≠ 0) (e : E) : ∃ N : ℕ, N ≠ 0 ∧ (N : E) * e ∈ I := by
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) {e / y0}
  have hi : IsIntegral ℤ ((y : E) * (e / y0)) := by
    have := hint (e / y0) (Finset.mem_singleton_self _)
    simpa [zsmul_eq_mul] using this
  have hN : IsIntegral ℤ ((y.natAbs : E) * (e / y0)) := by
    rcases Int.natAbs_eq y with h | h
    · have : (y.natAbs : E) = (y : E) := by rw [← Int.cast_natCast, ← h]
      rw [this]; exact hi
    · have : (y.natAbs : E) = -(y : E) := by
        have h' : (y.natAbs : ℤ) = -y := by omega
        rw [← Int.cast_natCast, h', Int.cast_neg]
      rw [this, neg_mul]; exact hi.neg
  refine ⟨y.natAbs, Int.natAbs_ne_zero.mpr hy, ?_⟩
  have key : (y.natAbs : E) * e = ((⟨(y.natAbs : E) * (e / y0), hN⟩ : 𝓞 E) : E) * y0 := by
    show (y.natAbs : E) * e = (y.natAbs : E) * (e / y0) * y0
    field_simp
  rw [key]
  exact (I : Submodule (𝓞 E) E).smul_mem (⟨(y.natAbs : E) * (e / y0), hN⟩ : 𝓞 E) hy0
end PI.KLW
