-- Prove2me | solution 1 for PositivityTheory.ThKF0.FinLine.off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:06.678687+00:00
-- url     : https://prove2.me/submissions/9810ff0b-f4d4-4dd2-83bd-53257f67e5a1

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_Imports
import Theorems.Thm_PositivityTheory_ThKF0_FinLine_ind_mem
import Theorems.Thm_PositivityTheory_ThKF0_FinLine_uniform
import Theorems.Thm_PositivityTheory_ThKF0_FinLine_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Filter Topology
open scoped Classical
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.FinLine
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]
variable {U₀ : OpenAddSubgroup G} (h₀ : IsCompact (U₀ : Set G)) {P : Set G} {l : (G → ℂ) →ₗ[ℂ] ℂ}
include h₀
namespace PositivityTheory.ThKF0.FinLine
theorem _root_.solution (h2 : ∀ a ∉ P, ∃ χ : G → ℂ, IsLocallyConstant χ ∧ χ a ≠ 1 ∧ ∀ φ ∈ SB G, l (fun x => χ x * φ x) = l φ)
    {φ : G → ℂ} (hφ : φ ∈ SB G) (hP : ∀ a, φ a ≠ 0 → a ∉ P) : l φ = 0 := by
  choose! χ hχ hne hl using h2
  have hV : ∀ a, ∃ V : OpenAddSubgroup G, a ∉ P → ∀ u ∈ V, χ a (a + u) = χ a a := by
    intro a
    by_cases ha : a ∈ P
    · exact ⟨⊤, fun h => absurd ha h⟩
    have : ∀ᶠ u in 𝓝 (0 : G), χ a (a + u) = χ a a := by
      simpa using (((hχ a ha).comp_continuous (continuous_add_left a)).eventually_eq 0)
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ this
    exact ⟨V, fun _ u hu => hV hu⟩
  choose V hV using hV
  have hcl : IsClosed (Function.support φ) := (hφ.1.isClopen_fiber 0).compl.isClosed
  have hK : IsCompact (Function.support φ) := IsCompact.of_isClosed_subset hφ.2 hcl (subset_tsupport _)
  obtain ⟨s, hs, hcov⟩ := hK.elim_nhds_subcover (fun a => (fun b => b - a) ⁻¹' (V a : Set G))
    (fun a _ => (continuous_sub_right a).continuousAt.preimage_mem_nhds (by
      show (V a : Set G) ∈ 𝓝 (a - a); rw [sub_self]; exact (V a).mem_nhds_zero))
  obtain ⟨U₁, hU₁⟩ := uniform hφ
  obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean ((U₀ : Set G) ∩ U₁ ∩ ⋂ a ∈ s, (V a : Set G))
    (inter_mem (inter_mem U₀.mem_nhds_zero U₁.mem_nhds_zero) ((biInter_finset_mem s).2 fun a _ => (V a).mem_nhds_zero))
  obtain ⟨t, ht, e⟩ := decomp hφ U fun u hu => hU₁ u (hU hu).1.2
  rw [e, map_sum]
  refine Finset.sum_eq_zero fun q hq => ?_
  obtain ⟨a, ha, hqa⟩ := Set.mem_iUnion₂.mp (hcov ((ht q).1 hq))
  have haP : a ∉ P := hP a (hs a ha)
  have h3 := hl a haP _ (ind_mem h₀ (fun u hu => (hU hu).1.1) q.out)
  have h4 : (fun x => χ a x * ind U q.out x) = χ a a • ind U q.out := by
    funext x
    simp only [ind, Pi.smul_apply, smul_eq_mul]
    split_ifs with hx
    · have := hV a haP _ ((V a).add_mem (Set.mem_iInter₂.1 (hU hx).2 a ha) hqa)
      rw [← this]; congr 2; beta_reduce; abel
    · simp
  rw [h4, map_smul, smul_eq_mul] at h3
  rw [map_smul, (mul_left_eq_self₀.1 h3).resolve_left (hne a haP), smul_zero]
end PositivityTheory.ThKF0.FinLine
