-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.finiteIndex_of_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:45:12.490774+00:00
-- url     : https://prove2.me/submissions/5bbcf634-2cd8-4ca1-b352-8e0e5cf58970

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_Herbrand
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandF
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrand
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_mem_ball
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_uval
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_uval_mem
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_uval_ne_zero
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_uval_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) [(subG p K L).Normal]
    (X : AddSubgroup (layerU p K L).V) {ε : ℝ} (hε : 0 < ε) (hX : ∀ w, ‖uval w - 1‖ < ε → w ∈ X) :
    X.FiniteIndex := by
  have : ProperSpace L := FiniteDimensional.proper ℚ_[p] L
  have hc : IsCompact (Metric.closedBall (0 : L) 1) := isCompact_closedBall 0 1
  obtain ⟨t, -, htf, hcov⟩ := finite_cover_balls_of_compact hc (e := ε) hε
  have hex : ∀ w : (layerU p K L).V, ∃ y : t, ‖uval w - ((y : L) : PadicAlgCl p)‖ < ε := by
    intro w
    have hw : (⟨uval w, uval_mem h w⟩ : L) ∈ Metric.closedBall (0 : L) 1 := by
      rw [mem_closedBall_zero_iff]; exact (norm_uval w).le
    obtain ⟨y, hy, hwy⟩ := Set.mem_iUnion₂.1 (hcov hw)
    rw [Metric.mem_ball, dist_eq_norm] at hwy
    exact ⟨⟨y, hy⟩, hwy⟩
  choose c hc' using hex
  have hsub : ∀ w w', c w = c w' → w - w' ∈ X := by
    intro w w' hww
    apply hX
    have h1 : uval (w - w') - 1 = (uval w - uval w') * (uval w')⁻¹ := by
      rw [uval_sub, sub_mul, mul_inv_cancel₀ (uval_ne_zero w')]
    rw [h1, norm_mul, norm_inv, norm_uval, inv_one, mul_one]
    have h2 : uval w - uval w' = (uval w - ((c w : L) : PadicAlgCl p)) - (uval w' - ((c w : L) : PadicAlgCl p)) := by
      ring
    rw [h2, sub_eq_add_neg]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (hc' w) ?_)
    rw [norm_neg, hww]; exact hc' w'
  have : Finite t := htf
  have hfin : Finite ((layerU p K L).V ⧸ X) := by
    refine Finite.of_injective (fun q => c q.out) fun q q' hqq => ?_
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq]
    have := hsub _ _ hqq.symm
    rwa [sub_eq_neg_add] at this
  exact AddSubgroup.finiteIndex_of_finite_quotient
end ReciprocityTheory.DiscreteGroups.LocalClassField
