-- Prove2me | solution 1 for PI.Residue.hitBound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:19:03.501186+00:00
-- url     : https://prove2.me/submissions/c66a569b-1b3c-4b94-96a2-2195efd0f6d0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_RealHitIneq
import Theorems.Thm_PI_Residue_real_hit_ineq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped ENNReal Classical
noncomputable section
open PI PI.Residue
namespace PI.Residue
theorem _root_.solution (hbox : BoxVolume) : HitBound := by
  intro K _ _ ρ s x hρ hs hx
  have hpos : ∀ w, 0 < normAtPlace w x := fun w =>
    lt_of_le_of_ne (normAtPlace_nonneg w x) (Ne.symm (mixedEmbedding.norm_ne_zero_iff.1 hx.ne' w))
  have hhit : hit K ρ x = box K (fun w => ρ / normAtPlace w x) := by
    ext y
    simp only [hit, box, Set.mem_ofPred_eq]
    exact forall_congr' fun w => (lt_div_iff₀ (hpos w)).symm
  have hprod : ∏ w, (ρ / normAtPlace w x) ^ mult w
      = ρ ^ Module.finrank ℚ K / mixedEmbedding.norm x := by
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, sum_mult_eq, mixedEmbedding.norm_apply]
  have hA : 0 < ρ ^ Module.finrank ℚ K := by positivity
  by_cases h : mixedEmbedding.norm x ≤ 2 * ρ ^ Module.finrank ℚ K
  · calc volume ({y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ x) ≤ volume (hit K ρ x) :=
          measure_mono Set.inter_subset_right
      _ = vfac K * ENNReal.ofReal (ρ ^ Module.finrank ℚ K / mixedEmbedding.norm x) := by
          rw [hhit, hbox K _ (fun w => div_pos hρ (hpos w)), hprod]
      _ ≤ _ := by
          gcongr
          exact real_hit_ineq _ _ s hA hx hs h
  · have hempty : {y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ x = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hy1, hy2⟩
      rw [hhit] at hy2
      have hle : mixedEmbedding.norm y ≤ ρ ^ Module.finrank ℚ K / mixedEmbedding.norm x := by
        rw [← hprod, mixedEmbedding.norm_apply]
        exact Finset.prod_le_prod (fun w _ => pow_nonneg (normAtPlace_nonneg w y) _)
          (fun w _ => pow_le_pow_left₀ (normAtPlace_nonneg w y) (hy2 w).le _)
      have hhalf : ρ ^ Module.finrank ℚ K / mixedEmbedding.norm x ≤ 1 / 2 := by
        rw [div_le_iff₀ hx]
        rw [not_le] at h
        linarith
      have hy1' : 1 / 2 < mixedEmbedding.norm y := hy1
      linarith
    rw [hempty, measure_empty]
    exact zero_le
end PI.Residue
