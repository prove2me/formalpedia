-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.peak_trace_bound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:21:22.765262+00:00
-- url     : https://prove2.me/submissions/beaadb5b-787b-4712-90f7-7aeebc31dee7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PeakTraceBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSumStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PeakTraceBoundHolds
import Theorems.Thm_PositivityTheory_Rg_BcB_F_ExponentialIntegralMeasures_trace_contra
import Theorems.Thm_PositivityTheory_Rg_BcB_F_ExponentialIntegralMeasures_peak

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.style.haveILetI false
open scoped ComplexOrder
open PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures
namespace PositivityTheory.Rg.BcB.F
theorem _root_.solution : PositivityTheory.Rg.BcB.F.PeakTraceBound := by
  intro A _ _ _ _ ι _ _ H _ _ _ R β m V _ _ _ ρ u p a₀ hβ hu ha₀ hbound hv
  obtain ⟨v, hv0, huv, hρv⟩ := hv
  by_contra hne
  push_neg at hne
  have hμpos : 0 < ‖p a₀‖ := norm_pos_iff.2 ha₀
  set K : ℝ := 1 + ∑ s, ‖R s a₀‖ with hK
  have hKs : ∀ s, ‖R s a₀‖ ≤ K := by
    intro s
    have := Finset.single_le_sum (f := fun s => ‖R s a₀‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
    linarith
  have hKp : 0 < K := by positivity
  obtain ⟨g, hg1, hgs⟩ := peak R β m p hβ hne (‖p a₀‖ / 2 / K) (by positivity)
  obtain ⟨C, N, j, hC⟩ := hbound (a₀ * g) (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  refine trace_contra (u * ρ (a₀ * g)) v hv0 (p a₀) ?_ (‖p a₀‖ / 2) (max C 0) N j (by positivity)
    (by linarith) ?_
  · simp [Module.End.mul_apply, map_mul, hρv, hg1, huv, map_smul]
  · filter_upwards [hC, Filter.eventually_gt_atTop j] with k hk hkj
    refine hk.trans ?_
    have hX : ∀ s, ‖(β s ^ m * R s (a₀ * g)) ^ (k - j)‖ ≤ (‖p a₀‖ / 2) ^ (k - j) := by
      intro s
      have h1 : ‖β s ^ m * R s (a₀ * g)‖ ≤ ‖p a₀‖ / 2 := by
        have e : β s ^ m * R s (a₀ * g) = R s a₀ * (β s ^ m * R s g) := by
          rw [map_mul, ← mul_assoc, ← mul_assoc, ((hβ s a₀).pow_left m).eq]
        rw [e]
        calc _ ≤ ‖R s a₀‖ * ‖β s ^ m * R s g‖ := norm_mul_le _ _
          _ ≤ K * (‖p a₀‖ / 2 / K) := mul_le_mul (hKs s) (hgs s) (norm_nonneg _) hKp.le
          _ = ‖p a₀‖ / 2 := by field_simp
      calc _ ≤ ‖β s ^ m * R s (a₀ * g)‖ ^ (k - j) := norm_pow_le' _ (by omega)
        _ ≤ _ := pow_le_pow_left₀ (norm_nonneg _) h1 _
    have hsup : Finset.univ.sup' Finset.univ_nonempty
        (fun s => ‖(β s ^ m * R s (a₀ * g)) ^ (k - j)‖) ≤ (‖p a₀‖ / 2) ^ (k - j) :=
      Finset.sup'_le _ _ (fun s _ => hX s)
    have hsup0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun s => ‖(β s ^ m * R s (a₀ * g)) ^ (k - j)‖) :=
      (norm_nonneg _).trans (Finset.le_sup' (fun s => ‖(β s ^ m * R s (a₀ * g)) ^ (k - j)‖)
        (Finset.mem_univ (Classical.arbitrary ι)))
    have hk0 : (0 : ℝ) ≤ (1 + (k : ℝ)) ^ N := by positivity
    set σ := Finset.univ.sup' Finset.univ_nonempty (fun s => ‖(β s ^ m * R s (a₀ * g)) ^ (k - j)‖)
    calc C * (1 + (k : ℝ)) ^ N * σ ≤ max C 0 * (1 + (k : ℝ)) ^ N * σ := by
          apply mul_le_mul_of_nonneg_right _ hsup0
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hk0
      _ ≤ max C 0 * (1 + (k : ℝ)) ^ N * (‖p a₀‖ / 2) ^ (k - j) := by
          apply mul_le_mul_of_nonneg_left hsup
          exact mul_nonneg (le_max_right _ _) hk0
end PositivityTheory.Rg.BcB.F
