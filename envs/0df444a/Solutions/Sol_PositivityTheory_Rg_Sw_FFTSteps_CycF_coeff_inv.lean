-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.CycF.coeff_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:58:40.779609+00:00
-- url     : https://prove2.me/submissions/76e47067-9403-4297-bdbd-3f06db482b9b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFT
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_act_emb_other
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_act_emb_same
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_coeff_sum_monomial
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_decomp
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_th_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.CycF
variable {m n : ℕ} {ε : Fin m → Bool}
namespace PositivityTheory.Rg.Sw.FFTSteps.CycF
theorem _root_.solution (v : Matrix (Rw ε true) (Rw ε true) ℂ) (Q : PX m n) (hQ : act (blk ε true v) Q = Q)
    (μ : VV (Rw ε false) n →₀ ℕ) : sub v (v.map star) ((Th ε Q).coeff μ) = (Th ε Q).coeff μ := by
  classical
  have h1 : act (blk ε true v) Q = ∑ ν ∈ (Th ε Q).support,
      emb ε true (sub v (v.map star) ((Th ε Q).coeff ν)) * emb ε false (monomial ν 1) := by
    conv_lhs => rw [decomp (ε := ε) Q]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    rw [map_mul]
    congr 1
    · exact DFunLike.congr_fun (act_emb_same true v) _
    · exact DFunLike.congr_fun (act_emb_other true false (by decide) v) _
  rw [hQ] at h1
  have h2 := congrArg (fun P => coeff μ (Th ε P)) h1
  simp only [map_sum, th_prod, coeff_sum_monomial] at h2
  by_cases hμ : μ ∈ (Th ε Q).support
  · rw [if_pos hμ] at h2
    exact h2.symm
  · have : coeff μ (Th ε Q) = 0 := notMem_support_iff.1 hμ
    rw [this, map_zero]
end PositivityTheory.Rg.Sw.FFTSteps.CycF
