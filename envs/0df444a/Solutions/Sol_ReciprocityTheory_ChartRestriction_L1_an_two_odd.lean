-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.an_two_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:33:18.900605+00:00
-- url     : https://prove2.me/submissions/f221e414-7523-4bec-a1b9-979761134356

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinRecursion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgAnTwo
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_congr
import Theorems.Thm_Formalism_L2_Th1_F_Universal_IsU_congr
import Theorems.Thm_Formalism_L2_Th1_F_sgStarQuasi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1
open scoped ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (m : ℕ) :
    F.sgStar L (((2 * m + 1 : ℕ) : ℂ) * (ω₀ / 2)) ^ 2
      = Complex.exp ((Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2) ^ (2 * (m ^ 2 + m))
        * F.sgStar L (ω₀ / 2) ^ 2 := by
  have hm : (m : ℂ) * ω₀ ∈ L.lattice := by
    rw [← nsmul_eq_mul]; exact L.lattice.nsmul_mem h0 m
  have h := F.sgStarQuasi L ((m : ℂ) * ω₀) (ω₀ / 2) hm
  have e1 : ((2 * m + 1 : ℕ) : ℂ) * (ω₀ / 2) = ω₀ / 2 + (m : ℂ) * ω₀ := by push_cast; ring
  have hchi : F.semiChar L ((m : ℂ) * ω₀) ^ 2 = 1 := by
    unfold F.semiChar; split_ifs <;> norm_num
  rw [e1, h, mul_pow, mul_pow, hchi, one_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  congr 2
  unfold F.herm
  simp only [map_mul, Complex.conj_natCast]
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.L1
