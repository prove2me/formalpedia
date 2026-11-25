-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.CycF.indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:38:06.022696+00:00
-- url     : https://prove2.me/submissions/9dd4499f-edb8-4832-8222-e906ff19ff98

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTC
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_th_embT
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_th_embF

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
variable {m n : ℕ} (ε : Fin m → Bool)
variable {ε}
namespace PositivityTheory.Rg.Sw.FFTSteps.CycF
theorem _root_.solution {J : Type} [Fintype J] (b : J → PV (Rw ε true) (Fin n) (Fin n)) (hb : LinearIndependent ℂ b)
    (t : J → PV (Rw ε false) (Fin n) (Fin n)) (h : ∑ j, emb ε true (b j) * emb ε false (t j) = 0) : ∀ j, t j = 0 := by
  have h2 := congrArg (Th ε) h
  rw [map_sum, map_zero] at h2
  simp_rw [map_mul, th_embT, th_embF] at h2
  intro j
  ext μ
  have h3 := congrArg (coeff μ) h2
  rw [coeff_sum, coeff_zero] at h3
  simp_rw [coeff_C_mul, coeff_map] at h3
  have h4 : ∑ i, (coeff μ (t i)) • b i = 0 := by
    rw [← h3]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Algebra.smul_def, mul_comm]
  have := Fintype.linearIndependent_iff.1 hb _ h4 j
  simpa using this
end PositivityTheory.Rg.Sw.FFTSteps.CycF
