-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.kType_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:42:50.766105+00:00
-- url     : https://prove2.me/submissions/bf5d18b2-b659-45b9-97ab-909c4ea4ea82

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KtintExpApplyOfEig
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_ktint_exp_apply_of_eig
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_ktint_inK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_ktint_exp_two_pi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_KType_op_curve
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exists_curve
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_onep_KG_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : ∀ a, ∃ m : ℤ, Λ a = m := by
  intro a
  have hX := ktint_inK ε a
  obtain ⟨γ, hγ⟩ := exists_curve ε hX
  have hop := KType.op_curve T hX γ hγ (2 * Real.pi)
  have h1 : γ (2 * Real.pi) = 1 := by
    apply onep_KG_ext
    rw [hγ, ktint_exp_two_pi]
    rfl
  have hw : (((2 * Real.pi : ℝ) : ℂ) • T.dτ (Complex.I • Matrix.single a a (1 : ℂ))) T.w =
      (((2 * Real.pi : ℝ) : ℂ) * (Complex.I * (Λ a : ℂ))) • T.w := by
    rw [_root_.smul_apply, map_smul, _root_.smul_apply, T.w_wt, smul_smul, smul_smul, mul_assoc]
  have key := ktint_exp_apply_of_eig _ _ _ hw
  rw [← hop, h1] at key
  have hone : T.op 1 = 1 := by
    simp [KType.op]
  rw [hone] at key
  change T.w = _ at key
  have hw0 : T.w ≠ 0 := by
    intro h
    have := T.w_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have he : NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) * (Complex.I * (Λ a : ℂ))) = 1 := by
    by_contra hne
    have h2 : (1 - NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) * (Complex.I * (Λ a : ℂ)))) • T.w = 0 := by
      rw [sub_smul, one_smul, ← key, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact hne (sub_eq_zero.mp h3).symm
    · exact hw0 h3
  rw [← Complex.exp_eq_exp_ℂ, Complex.exp_eq_one_iff] at he
  obtain ⟨m, hm⟩ := he
  refine ⟨m, ?_⟩
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  have h4 : (Λ a : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [← hm]
    push_cast
    ring
  have h5 : (Λ a : ℂ) = ((m : ℝ) : ℂ) := by
    rw [mul_right_cancel₀ hpi h4]
    push_cast
    rfl
  exact_mod_cast h5
end ReciprocityTheory.ChartRestriction.DS.HW
