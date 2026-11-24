-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.CycF.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:00:39.649348+00:00
-- url     : https://prove2.me/submissions/a8b7e1f4-6dff-4ad2-8e63-0d6001e8b6e0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTC
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
variable {m n : ℕ} (ε : Fin m → Bool)
variable {ε}
namespace PositivityTheory.Rg.Sw.FFTSteps.CycF
theorem _root_.solution (Q : PX m n) :
    Q = ∑ μ ∈ (Th ε Q).support, emb ε true ((Th ε Q).coeff μ) * emb ε false (monomial μ 1) := by
  apply (Th ε).injective
  rw [map_sum]
  simp_rw [th_prod]
  exact (Th ε Q).as_sum
end PositivityTheory.Rg.Sw.FFTSteps.CycF
