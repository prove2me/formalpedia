-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_phiV__li_6fbc45786d0f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:59:03.479777+00:00
-- url     : https://prove2.me/submissions/0cfbcf3d-9e2b-4525-b60b-2d7d087b9ac8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LastBasisZero
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_phiV__app_229d361ad964
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_last
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_mp
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_zero_pos



set_option autoImplicit false
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution {k r : ℕ} (hk : 1 ≤ k) : LinearIndependent ℂ (phiV' k r) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg b
  have hs : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have hc : ((Real.sqrt 2)⁻¹ : ℂ) ≠ 0 := by simp [hs]
  have hbl := b.isLt
  by_cases hb : b.val < r
  · have := congrFun hg ⟨b.val, by omega⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ea_phiV'_app hk, Pi.zero_apply] at this
    rw [Finset.sum_eq_single b] at this
    · split_ifs at this <;> first | (exfalso; omega) | simp_all
    · intro c _ hcb
      have : c.val ≠ b.val := fun h => hcb (Fin.ext h)
      split_ifs <;> first | (exfalso; omega) | simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hbr : b.val = r := by omega
    have := congrFun hg ⟨r, by omega⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ea_phiV'_app hk, Pi.zero_apply] at this
    rw [Finset.sum_eq_single b] at this
    · split_ifs at this <;> first | (exfalso; omega) | simp_all
    · intro c _ hcb
      have : c.val ≠ b.val := fun h => hcb (Fin.ext h)
      split_ifs <;> first | (exfalso; omega) | simp
    · intro h; exact absurd (Finset.mem_univ _) h
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
