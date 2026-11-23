-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.finite_resK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:00.514809+00:00
-- url     : https://prove2.me/submissions/293abf9c-46ac-4c3e-a6aa-27f518c9ecf7

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrDefs
import Definitions.Def_Lemmata_PadicNatCastNorm_NormNatCastOfNotDvd
import Definitions.Def_Lemmata_FirstBlockLemmaC_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaD_Imports
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormSubEqOneOfPowEqOne
import Theorems.Thm_P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sub_le_max__b9ad733dbc67
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_res_eq_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_resK_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Obar_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField
variable {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
theorem _root_.solution (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K) :
    Finite (resK p K) := by
  have : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  have hc : IsCompact (Metric.closedBall (0 : K) 1) := isCompact_closedBall 0 1
  obtain ⟨t, -, htf, hcov⟩ := finite_cover_balls_of_compact hc (e := 1) one_pos
  classical
  let g : K → kbar p := fun x => if h : ‖(x : PadicAlgCl p)‖ ≤ 1 then res ⟨x, mem_Obar_iff.2 h⟩ else 0
  have hsub : (resK p K : Set (kbar p)) ⊆ g '' t := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := (mem_resK_iff K c).1 hc
    have hxb : (⟨x, hx⟩ : K) ∈ Metric.closedBall (0 : K) 1 := by
      rw [mem_closedBall_zero_iff]; exact norm_le_one x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov hxb)
    rw [Metric.mem_ball, dist_eq_norm] at hxy
    have hxy' : ‖(x : PadicAlgCl p) - (y : PadicAlgCl p)‖ < 1 := hxy
    have hy1 : ‖(y : PadicAlgCl p)‖ ≤ 1 := by
      have h1 : (y : PadicAlgCl p) = (x : PadicAlgCl p) - ((x : PadicAlgCl p) - (y : PadicAlgCl p)) := by ring
      rw [h1]
      exact (norm_sub_le_max' _ _).trans (max_le (norm_le_one x) hxy'.le)
    refine ⟨y, hy, ?_⟩
    have hg : g y = res ⟨(y : PadicAlgCl p), mem_Obar_iff.2 hy1⟩ := dif_pos hy1
    rw [hg]
    exact ((res_eq_iff x ⟨(y : PadicAlgCl p), mem_Obar_iff.2 hy1⟩).2 hxy').symm
  exact (htf.image g).subset hsub
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
