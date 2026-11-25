-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.an_two_kap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:56:56.343527+00:00
-- url     : https://prove2.me/submissions/c1a0a026-8600-4417-a67a-456103668bbe

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinRecursion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgAnTwo
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_an_two_shift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_an_two_sq
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_congr
import Theorems.Thm_Formalism_L2_Th1_F_Universal_IsU_congr
import Theorems.Thm_Formalism_L2_Th1_F_halfShift
import Theorems.Thm_Formalism_L2_Th1_F_sgStarBasic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1
open scoped ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) :
    (3 * L.weierstrassP (ω₀ / 2) ^ 2 - L.g₂ / 4) * F.sgStar L (ω₀ / 2) ^ 4
      = Complex.exp ((Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2) := by
  have hz : ω₀ / 4 ∉ L.lattice := by
    intro h
    apply h1
    have := L.lattice.add_mem h h
    have e : ω₀ / 4 + ω₀ / 4 = ω₀ / 2 := by ring
    rwa [e] at this
  have hzt : ω₀ / 4 + ω₀ / 2 ∉ L.lattice := by
    intro h
    apply hz
    have := L.lattice.sub_mem h0 h
    have e : ω₀ - (ω₀ / 4 + ω₀ / 2) = ω₀ / 4 := by ring
    rwa [e] at this
  have h2t : 2 * (ω₀ / 2) ∈ L.lattice := by
    have e : 2 * (ω₀ / 2) = ω₀ := by ring
    rwa [e]
  have hH := F.halfShift L (ω₀ / 2) (ω₀ / 4) h1 h2t hz hzt
  have hA := an_two_shift L ω₀ h0 h1 (ω₀ / 4)
  have hB1 := an_two_sq L ω₀ h0 h1 (ω₀ / 4) hz
  have hB2 := an_two_sq L ω₀ h0 h1 (ω₀ / 4 + ω₀ / 2) hzt
  have e1 : ω₀ / 4 + ω₀ / 2 - ω₀ / 2 = ω₀ / 4 := by ring
  have e2 : Complex.exp ((Real.pi : ℂ) * F.herm L (ω₀ / 4 + ω₀ / 2) ω₀)
      = Complex.exp ((Real.pi : ℂ) * F.herm L (ω₀ / 4) ω₀)
        * Complex.exp ((Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2) := by
    rw [← Complex.exp_add]; congr 1; unfold F.herm; ring
  rw [e1, e2, hA] at hB2
  have hs : F.sgStar L (ω₀ / 4) ≠ 0 := fun h => hz (((F.sgStarBasic L).2.2.1 _).1 h)
  have hE : Complex.exp ((Real.pi : ℂ) * F.herm L (ω₀ / 4) ω₀) ≠ 0 := Complex.exp_ne_zero _
  have hne : Complex.exp ((Real.pi : ℂ) * F.herm L (ω₀ / 4) ω₀) * F.sgStar L (ω₀ / 4) ^ 2 ≠ 0 :=
    mul_ne_zero hE (pow_ne_zero _ hs)
  apply mul_left_cancel₀ hne
  rw [← hH]
  generalize Complex.exp ((Real.pi : ℂ) * F.herm L (ω₀ / 4) ω₀) = E at *
  generalize Complex.exp ((Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2) = X at *
  generalize F.sgStar L (ω₀ / 4) = s at *
  generalize F.sgStar L (ω₀ / 4 - ω₀ / 2) = s' at *
  generalize F.sgStar L (ω₀ / 2) = T at *
  generalize L.weierstrassP (ω₀ / 4) - L.weierstrassP (ω₀ / 2) = a at *
  generalize L.weierstrassP (ω₀ / 4 + ω₀ / 2) - L.weierstrassP (ω₀ / 2) = b at *
  linear_combination (-1 : ℂ) * hB2 + (-(E * T ^ 2 * b)) * hB1
end ReciprocityTheory.ChartRestriction.L1
