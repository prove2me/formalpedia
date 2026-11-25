-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.integrable_hk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:57:05.400906+00:00
-- url     : https://prove2.me/submissions/7e438802-d8ed-4d5a-a405-dd7817e31e2d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralHkDiag
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_continuous_hk
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_norm_hk
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_pow_exp_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Module
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.PosProof
namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof
theorem _root_.solution (k l : ℕ) : Integrable (hk k l) := by
  obtain ⟨C, hC⟩ := pow_exp_le (k + l)
  have hi : Integrable (fun z : ℂ => (1 + ‖z‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by norm_num [finrank_real_complex])
  refine (hi.const_mul C).mono' (continuous_hk k l).aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rw [norm_hk]
  exact hC _ (norm_nonneg _)
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
