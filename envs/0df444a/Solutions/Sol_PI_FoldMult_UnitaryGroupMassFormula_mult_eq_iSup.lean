-- Prove2me | solution 1 for PI.FoldMult.UnitaryGroupMassFormula.mult_eq_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:40:34.214807+00:00
-- url     : https://prove2.me/submissions/919e9e85-63ab-4ada-83f4-7728c6598149

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FoldMult
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MultiplicityMeasurability_MeasurableMult
import Theorems.Thm_PI_FoldMult_UnitaryGroupMassFormula_cnt_encard_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
open PI PI.FoldMult PI.FoldMult.UnitaryGroupMassFormula
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
namespace PI.FoldMult.UnitaryGroupMassFormula
theorem _root_.solution (Γ : Subgroup G) [DiscreteTopology Γ] (Ω : Set G) (hΩ : IsCompact Ω)
    (x : G) : Formalism.L2.SG.FoldBound.mult Γ Ω x =
      ⨆ A : Finset Γ, (hitSet Γ Ω A).indicator (fun _ => (A.card : ℝ≥0∞)) x := by
  obtain ⟨N, hN, hle⟩ := cnt_encard_le Γ Ω hΩ x
  unfold Formalism.L2.SG.FoldBound.mult
  apply le_antisymm
  · refine iSup_le fun y => ?_
    have hfin : (cnt Γ Ω x y).Finite := Set.encard_lt_top_iff.1 ((hle y).trans_lt hN)
    refine le_iSup_of_le hfin.toFinset ?_
    have hx : x ∈ hitSet Γ Ω hfin.toFinset := ⟨y, fun a ha => hfin.mem_toFinset.1 ha⟩
    rw [Set.indicator_of_mem hx]
    change ((cnt Γ Ω x y).encard : ℝ≥0∞) ≤ (hfin.toFinset.card : ℝ≥0∞)
    exact le_of_eq (by rw [hfin.encard_eq_coe_toFinset_card, ENat.toENNReal_coe])
  · refine iSup_le fun B => ?_
    by_cases hx : x ∈ hitSet Γ Ω B
    · obtain ⟨y, hy⟩ := hx
      rw [Set.indicator_of_mem (show x ∈ hitSet Γ Ω B from ⟨y, hy⟩)]
      refine le_iSup_of_le y ?_
      have hsub : (B : Set Γ) ⊆ cnt Γ Ω x y := fun a ha => hy a ha
      have hc := Set.encard_le_encard hsub
      rw [Set.encard_coe_eq_coe_finsetCard] at hc
      show (B.card : ℝ≥0∞) ≤ _
      rw [← ENat.toENNReal_coe]
      exact ENat.toENNReal_le.2 hc
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
end PI.FoldMult.UnitaryGroupMassFormula
