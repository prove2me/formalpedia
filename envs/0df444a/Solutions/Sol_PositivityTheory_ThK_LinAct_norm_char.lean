-- Prove2me | solution 1 for PositivityTheory.ThK.LinAct.norm_char
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:04.098185+00:00
-- url     : https://prove2.me/submissions/592eaadb-3b1a-455a-992f-20c9df2526f7

import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_LinearActInt
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_cball


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM MeasureTheory ValuativeRel Topology Filter PositivityTheory.ThKH.Evl
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.LinAct
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {κ ι : Type} [Fintype κ] [Fintype ι] {ψ : AddChar k ℂ}
omit [Invertible (2 : k)]
namespace PositivityTheory.ThK.LinAct
theorem _root_.solution (hc : Continuous ψ) (x : k) : ‖ψ x‖ = 1 := by
  have hle : ∀ y, ‖ψ y‖ ≤ 1 := fun y => by
    by_cases h0 : y = 0
    · simp [h0]
    obtain ⟨M, hM⟩ := (GlobalTheory.SplitWeil.isCompact_cball (Units.mk0 y h0)).exists_bound_of_continuousOn hc.continuousOn
    have hm : ∀ n : ℕ, n • y ∈ GlobalTheory.SplitWeil.cball (Units.mk0 y h0) := fun n => by
      induction n with
      | zero => simp [GlobalTheory.SplitWeil.cball]
      | succ n ih =>
        rw [succ_nsmul]
        exact GlobalTheory.SplitWeil.add_mem_cball ih (by simp [GlobalTheory.SplitWeil.cball])
    by_contra hy
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (not_le.1 hy)
    have := hM _ (hm n)
    rw [AddChar.map_nsmul_eq_pow, norm_pow] at this
    exact absurd hn (not_lt.2 this)
  have h1 : ‖ψ x‖ * ‖ψ (-x)‖ = 1 := by
    rw [← norm_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, norm_one]
  refine le_antisymm (hle x) ?_
  calc (1 : ℝ) = ‖ψ x‖ * ‖ψ (-x)‖ := h1.symm
    _ ≤ ‖ψ x‖ * 1 := mul_le_mul_of_nonneg_left (hle _) (norm_nonneg _)
    _ = ‖ψ x‖ := mul_one _
end PositivityTheory.ThK.LinAct
