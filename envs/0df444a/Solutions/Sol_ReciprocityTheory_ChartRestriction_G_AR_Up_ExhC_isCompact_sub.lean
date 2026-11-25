-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC.isCompact_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:52:54.339706+00:00
-- url     : https://prove2.me/submissions/5a5d398e-b322-4235-beee-3d858ff85425

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhC_coord_le_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhC_rh_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhC_normSq_tPart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhC_sub_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhC_isClosed_psd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhC_continuous_torusCharacter
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhC_cont_G
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhB_zPart_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
open Matrix Topology Filter
open scoped ComplexOrder Matrix
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
variable {f p q N' : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
theorem _root_.solution (a : ℝ) :
    IsCompact {v : V (nD f p q + N') | v ∈ OmSet f p q N' ∧ eOm v ≤ a} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · rw [sub_eq]
    exact isClosed_psd.inter (isClosed_le (Real.continuous_exp.comp (continuous_torusCharacter.sub continuous_const)) cont_G)
  · refine isBounded_iff_forall_norm_le.2 ⟨(nD f p q + N') * (1 + Real.exp a) + 1, ?_⟩
    rintro v ⟨hv, he⟩
    have hT : Real.log (1 + ‖tPart v‖ ^ 2) ≤ a := by
      have := rh_nonneg hv; unfold eOm at he; linarith
    have hT2 : ‖tPart v‖ ^ 2 ≤ Real.exp a := by
      have h := Real.exp_le_exp.2 hT
      rw [Real.exp_log (by positivity)] at h; linarith
    have hco : ∀ i, ‖v i‖ ^ 2 ≤ 1 + Real.exp a := by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · have h := coord_le_one hv j
        rw [zPart_apply] at h
        have : ‖v (Fin.castAdd N' j)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (v (Fin.castAdd N' j))]
        linarith [Real.exp_pos a]
      · have h := normSq_tPart v
        have h2 : ‖v (Fin.natAdd (nD f p q) j)‖ ^ 2 ≤ ‖tPart v‖ ^ 2 := by
          rw [h]
          exact Finset.single_le_sum (f := fun j => ‖v (Fin.natAdd (nD f p q) j)‖ ^ 2)
            (fun _ _ => by positivity) (Finset.mem_univ j)
        linarith
    have hn : ‖v‖ ^ 2 ≤ (nD f p q + N') * (1 + Real.exp a) := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin (nD f p q + N'), (1 + Real.exp a) :=
            Finset.sum_le_sum fun i _ => hco i
        _ = _ := by simp; ring
    have h0 : 0 ≤ ((nD f p q + N' : ℕ) : ℝ) * (1 + Real.exp a) := by positivity
    push_cast at h0
    nlinarith [norm_nonneg v]
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
