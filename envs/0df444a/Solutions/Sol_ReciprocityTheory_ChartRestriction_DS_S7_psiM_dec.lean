-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.psiM_dec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:45:42.568054+00:00
-- url     : https://prove2.me/submissions/b9d09ead-8667-41ea-adb5-20a5b414ac0d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecLog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMoments
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ToMKMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecALogLower
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiDecayCore
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_phiM_exp_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_decA_hs_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_exp_noncompactPart_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_inP_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_psM_norm_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_psiM_kexp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_toMK_facts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_toMK_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool} {lam : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) (hlam : IsHCParam lam)
    {h : ℝ} (hgap : GapAtLeast ε lam h) (hq : 1 ≤ q0 ε) (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    ‖PsiM T μ (toMK k * NormedSpace.exp X)‖ ≤
      Real.exp (-(h / 8) * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * q0 ε))) := by
  rw [psiM_kexp T μ k hX]
  have hB : ∀ k' : KG ε, (PhiM μ (toMK k'⁻¹ * NormedSpace.exp X * toMK k')).re ≤
      Real.exp (-(h / 8) * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * q0 ε))) := by
    intro k'
    obtain ⟨hP, hE⟩ := inP_conj k'⁻¹ hX
    rw [inv_inv] at hP hE
    rw [← hE]
    have := phiM_exp_le μ hμ hlam hgap hq hP
    rw [toMK_inv, decA_hs_conj (toMK_facts k').2.1] at this
    rwa [toMK_inv]
  calc ‖T.op k * psM T μ (NormedSpace.exp X)‖ = ‖psM T μ (NormedSpace.exp X)‖ :=
        CStarRing.norm_coe_unitary_mul _ _
    _ ≤ _ := psM_norm_le T μ (exp_noncompactPart_posDef hX) hB
end ReciprocityTheory.ChartRestriction.DS.S7
