-- Prove2me | solution 1 for PI.FoldUnfold.UnitaryGroupMassFormula.count_ae_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:40:39.999806+00:00
-- url     : https://prove2.me/submissions/0ce24858-665d-4c8d-8e32-62cf60d6338a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FoldUnfold
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingIdentity_FoldUnfoldMain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal Pointwise
open PI PI.FoldUnfold PI.FoldUnfold.UnitaryGroupMassFormula
namespace PI.FoldUnfold.UnitaryGroupMassFormula
theorem _root_.solution {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    (S : Subgroup G) [Countable S] (F : Set G) (hF : IsFundamentalDomain S F μ) :
    ∀ᵐ y ∂μ, ∑' s : S, F.indicator (fun _ => (1 : ℝ≥0∞)) ((s : G) * y) = 1 := by

  have hcov := hF.ae_covers
  have hnull : ∀ᵐ y ∂μ, ∀ s t : S, s ≠ t → ¬ ((s : G) * y ∈ F ∧ (t : G) * y ∈ F) := by
    rw [ae_all_iff]
    intro s
    rw [ae_all_iff]
    intro t
    by_cases hst : s = t
    · exact Filter.Eventually.of_forall fun y h => absurd hst h
    · have hd : AEDisjoint μ (s⁻¹ • F) (t⁻¹ • F) := hF.aedisjoint (inv_injective.ne hst)
      have h0 : μ (s⁻¹ • F ∩ t⁻¹ • F) = 0 := hd
      have h1 : ∀ᵐ y ∂μ, y ∉ s⁻¹ • F ∩ t⁻¹ • F := ae_iff.mpr (by simpa using h0)
      filter_upwards [h1] with y hy _ hyy
      apply hy
      exact ⟨by simpa [Set.mem_inv_smul_set_iff, Subgroup.smul_def] using hyy.1,
        by simpa [Set.mem_inv_smul_set_iff, Subgroup.smul_def] using hyy.2⟩
  filter_upwards [hcov, hnull] with y hy huniq
  obtain ⟨g, hg⟩ := hy
  rw [Subgroup.smul_def, smul_eq_mul] at hg
  rw [tsum_eq_single g]
  · simp [Set.indicator_of_mem hg]
  · intro b hb
    have : (b : G) * y ∉ F := fun hb' => huniq b g hb ⟨hb', hg⟩
    simp [Set.indicator_of_notMem this]
end PI.FoldUnfold.UnitaryGroupMassFormula
